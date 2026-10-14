"""Persistent native worker threads, exact counters, common strategy scheduler."""
from collections import deque
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import datetime
import json
import os
import re
import struct
import subprocess
import threading
import time
from pathlib import Path
from . import ROOT
from .platform_support import idle_seconds
from .settings import LOGS, apply_math_environment, atomic_json
from .native import Hasher, hash256
from .connections import CoreConnection, PoolConnection
from .protocol import DIFF1

def clean_text(text):
    return "".join(c if c.isprintable() else " " for c in str(text))[:1000]

def append_log(path, value, limit=5*1024*1024):
    path = Path(path); path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists() and path.stat().st_size > limit:
        old = path.with_suffix(path.suffix + ".1")
        os.replace(path, old)
    with path.open("a") as f:
        f.write(json.dumps(value, ensure_ascii=False) + "\n")

class Engine:
    def __init__(self, config, logs=None):
        self.c = config
        self.distributor = None
        self.logs = LOGS if logs is None else Path(logs)
        apply_math_environment(config,self.logs)
        self.stop = threading.Event()
        self.manual_pause = threading.Event()
        self.lock = threading.RLock()
        self.events = deque(maxlen=150)
        self.samples = deque(maxlen=910)
        self.began = time.time()
        self.monotonic_start = time.monotonic()
        self.state = {"state":"STARTING", "hashes":0, "shares_accepted":0, "shares_rejected":0,
                      "shares_unknown":0, "blocks_accepted":0, "block_candidates":0,
                      "best_difficulty":0, "best_difficulty_unbounded":False,
                      "height":None, "latency_ms":None, "error":"",
                      "strategy":config["strategy"], "connection":config["connection"],
                      "worker":config["worker"], "workers":config["workers"], "started":self.began,
                      "candidate_count":0, "rounds":0, "math_source":"legacy Python", "paused_reason":""}
        from .mathrevision import fingerprint
        self.state["math_implementation"] = fingerprint()
        self.hasher = Hasher(config["native_hasher"])
        from .pruning import Pruner
        self.pruner = Pruner(config)
        self.state['pruning'] = self.pruner.description()
        from .priority import Priority
        self.priority = Priority()
        self.state['priority'] = self.priority.description()
        self.abacus = None
        if config['strategy']=='thesis2':
            from .abacus import Workspace
            self.abacus=Workspace(self.hasher,config['thesis2_step'])
            self.state['resident_abacus']=self.abacus.description()
        from .difficulty import KEY, active_multiplier
        self.state["network"] = config["network"]
        self.state[KEY] = active_multiplier(config)
        self.state["hasher"] = self.hasher.source
        self.connection = (CoreConnection if config["connection"] == "core" else PoolConnection)(config,self.emit)
        self.cache_key = None
        self.cached_candidates = []
        self.last_idle_check = 0
        self.active_pause = False
        self.awake = None
        self.active_seconds = 0.0
        # MINER-01/DATA-01: observational only; no work selection or submissions.
        # See observatory_telemetry.py and the observatory MASTER_PLAN.md.
        from .observatory_telemetry import Telemetry
        self.model_telemetry = Telemetry(self.logs, config['network'], config.get('observatory_telemetry', True))
        from .provider_runtime import ProviderRuntime
        self.provider = ProviderRuntime(config, self.logs)
        from .resources import ResourceController
        self.resources = ResourceController(config, self.logs, self.stop, lambda: self.state['hashes'])

    def emit(self, kind, message, **extra):
        event = {"ts":time.time(),"kind":kind,"message":clean_text(message),**extra}
        with self.lock:
            self.events.append(event)
            append_log(self.logs/"events.jsonl", event)
            if "height" in extra:
                self.state["height"] = extra["height"]

    def snapshot(self):
        with self.lock:
            now = time.monotonic()
            result = dict(self.state)
            result["elapsed"] = max(0,time.time()-self.began)
            result["active_seconds"] = self.active_seconds
            result["hashrate"] = self.state["hashes"] / max(.001,now-self.monotonic_start)
            rates = {}
            for window in (10,60,900):
                candidates = [p for p in self.samples if now - p[0] <= window]
                if len(candidates) >= 2:
                    a,b = candidates[0], candidates[-1]
                    rates[str(window)] = (b[1]-a[1])/max(.001,b[0]-a[0])
                else:
                    rates[str(window)] = 0
            result["rates"] = rates
            result["events"] = list(self.events)
            result["endpoint"] = self.connection.label
            result["connected"] = self.connection.connected
            result["pid"] = os.getpid()
            result['model_telemetry'] = self.model_telemetry.snapshot()
            result['provider'] = self.provider.snapshot()
            result['resources'] = self.resources.snapshot()
            return result

    def paused(self):
        if self.manual_pause.is_set():
            self.state["paused_reason"] = "manual"
            return True
        now = time.monotonic()
        if self.c["pause_on_active"] and now-self.last_idle_check > 2:
            self.last_idle_check = now
            try:
                idle = idle_seconds()
                self.active_pause = idle is not None and idle < self.c["pause_on_active"]
            except (OSError,subprocess.TimeoutExpired):
                self.active_pause = False
        if self.active_pause:
            self.state["paused_reason"] = f"keyboard / mouse active · resume after {self.c['pause_on_active']}s idle"
            return True
        self.state["paused_reason"] = ""
        return False

    def candidates(self, work):
        from thesis_mining import (nonce_generate_unified_py, recovery_suggested_nonce, build_candidate_list,
                                   bits_compact_to_difficulty_bits, quadrant_from_nonce, get_base_nonce_source,
                                   get_last_seed_prime_path, get_base_nonce_version)
        key = (work.height,work.bits,work.header[:76])
        if key == self.cache_key:
            return self.cached_candidates
        base = nonce_generate_unified_py(work.height,bits_compact_to_difficulty_bits(work.bits and int(work.bits,16)))
        rec = recovery_suggested_nonce(bytes.fromhex(work.bits))
        recovery = base if rec is None else rec
        minimal = list(dict.fromkeys([base,recovery]))
        if self.c["single_nonce_only"]:
            candidates = minimal
        elif self.c["partition"] == "chunk":
            # Preserve the old eight logical ranges independently of physical CPU workers.
            candidates = []
            for lane in range(8):
                candidates.extend(build_candidate_list(base,recovery,lane*(1<<29),(lane+1)*(1<<29),block_height=work.height))
        else:
            candidates = build_candidate_list(base,recovery,0,1<<32,block_height=work.height)
            if self.c["partition"] == "quadrant":
                lanes = [[] for _ in range(4)]
                for nonce in candidates:
                    lanes[quadrant_from_nonce(nonce)].append(nonce)
                # Interleave logical quadrants so a two-worker default visits all four.
                candidates = [lane[i] for i in range(max(map(len,lanes),default=0)) for lane in lanes if i < len(lane)]
        candidates = list(dict.fromkeys(candidates))
        self.cache_key, self.cached_candidates = key, candidates
        self.state["candidate_count"] = len(candidates)
        source = get_base_nonce_source() + ":" + get_base_nonce_version()
        self.state["math_version"] = get_base_nonce_version()
        self.state["math_source"] = source + " · " + str(get_last_seed_prime_path())
        from nonce_logger import log_nonce_round
        nonce_path = self.logs/"nonces.jsonl"
        if nonce_path.exists() and nonce_path.stat().st_size > 5*1024*1024:
            os.replace(nonce_path,self.logs/"nonces.jsonl.1")
        log_nonce_round(work.height,work.bits,base,recovery,minimal,len(candidates),candidates,base_nonce_source=source)
        return candidates

    def tasks(self, work):
        for task in self.unfiltered_tasks(work):
            if self.stop.is_set() or not self.connection.valid(work):
                return
            ordered = self.priority.order(work, task)
            filtered = self.pruner.filter_task(work, ordered)
            self.state['pruning'] = self.pruner.description()
            self.state['priority'] = self.priority.description()
            if 'nonces' not in filtered or len(filtered['nonces']):
                yield filtered

    def unfiltered_tasks(self, work):
        batch = self.c["batch_size"]
        if self.c["strategy"] == "thesis2":
            from itertools import islice
            from .thesis2 import Traversal, VERSION
            self.abacus.bind(work)
            plan = Traversal(work.header,self.c["thesis2_step"],self.c["thesis2_prime"],workspace=self.abacus,
                             order=self.c.get('thesis2_order','field'))
            # Older libraries need the compatibility table. Materialize it
            # before reporting memory so status describes the actual backend.
            if self.hasher.fill_factored is None and self.hasher.fill_nonces is not None:
                plan.offsets
            self.state['resident_abacus']=self.abacus.description()
            self.state["candidate_count"] = 1 if self.c["single_nonce_only"] else 1 << 32
            self.state["math_source"] = VERSION
            self.state["math_details"] = plan.description()
            self.provider.observe(work, plan)
            self.state['math_details']['candidate_backend']=('native scale-graph rods' if self.hasher.fill_factored is not None
                else 'native offset table' if self.hasher.fill_nonces is not None else 'Python exact formula')
            if self.c["nonce_log"]:
                append_log(self.logs/"thesis2-nonces.jsonl",{"ts":time.time(),"height":work.height,"bits":work.bits,
                           **self.state['math_details'],"first_20":list(islice(plan.nonces(),20))})
            yield from self.hasher.traversal_batches(plan,batch,single=self.c["single_nonce_only"])
            return
        if self.c["single_nonce_only"] or self.c["strategy"] != "linear":
            candidates = self.candidates(work)
            for i in range(0,len(candidates),batch):
                yield {"nonces":candidates[i:i+batch]}
            if self.c["single_nonce_only"] or self.c["strategy"] == "thesis":
                return
            count = self.c["phase3_nonces"]
            start = candidates[0] if candidates else 0
            seen = set(candidates)
            for offset in range(0,count,batch):
                # Hybrid does not count duplicate thesis candidates twice.
                values = [(start+offset+i)&0xffffffff for i in range(min(batch,count-offset))]
                values = [n for n in values if n not in seen]
                if values:
                    yield {"nonces":values}
        else:
            for start in range(0,1<<32,batch):
                yield {"start":start,"count":min(batch,(1<<32)-start)}

    def scan_task(self, work, task):
        begin = time.monotonic()
        total, hits = 0, []
        remaining = dict(task)
        while not self.stop.is_set() and self.connection.valid(work):
            tried, nonce = self.hasher.scan(work.header,work.target,stop=self.stop.is_set,**remaining)
            total += tried
            if nonce is None:
                break
            hits.append(nonce)
            if "nonces" in remaining:
                values = remaining["nonces"][tried:]
                if not values:
                    break
                remaining = {"nonces":values}
            else:
                count = remaining["count"] - tried
                if not count:
                    break
                remaining = {"start":(remaining["start"]+tried)&0xffffffff,"count":count}
            # Return promptly after a share; coordinator reschedules the unscanned tail.
            if hits:
                break
        else:
            remaining = None
        if not hits or total == (len(task["nonces"]) if "nonces" in task else task["count"]):
            remaining = None
        elapsed = time.monotonic()-begin
        duty=min(self.c['cpu_duty'],self.resources.admission(0)[1]) if self.resources.enabled else self.c['cpu_duty']
        if duty < 100:
            self.stop.wait(min(2,elapsed*(100/duty-1)))
        return total,hits,remaining,elapsed

    def sample_batch(self, work, task, tried, round_id):
        if not self.c["supt_log"] or tried <= 0:
            return
        import supt_streams as ss
        step = self.c["supt_sample_every"]
        values = self.hasher.sampled_nonces(task,tried,step)
        ss.sample_hashes(round_id, ((nonce,hash256(work.header[:76]+struct.pack("<I",nonce)))
                                   for nonce in values))

    def submit_hits(self, work, hits, submitted, round_id, on_outcome=None):
        winning = -1
        for nonce in hits:
            if nonce in submitted:
                continue
            submitted.add(nonce)
            value = int.from_bytes(hash256(work.header[:76]+struct.pack("<I",nonce)),"little")
            if value > work.target:
                raise RuntimeError("Native result failed independent SHA256d validation")
            # A zero hash has no finite DIFF1/hash ratio. Keep JSON
            # finite and preserve this result across later shares.
            if value == 0:
                self.state["best_difficulty"] = None
                self.state["best_difficulty_unbounded"] = True
            elif not self.state["best_difficulty_unbounded"]:
                self.state["best_difficulty"] = max(self.state["best_difficulty"],DIFF1/value)
            if value <= work.network_target:
                self.state["block_candidates"] += 1
            if not self.connection.valid(work) or self.stop.is_set():
                self.emit("stale","Discarded solution from an expired job")
                continue
            before = time.monotonic()
            try:
                accepted,reason,block = self.connection.submit(work,nonce)
            except Exception as e:
                accepted,reason,block = None,str(e),False
            if on_outcome is not None:
                on_outcome(nonce,accepted,reason,block)
            self.state["latency_ms"] = round((time.monotonic()-before)*1000,1)
            self.model_telemetry.outcome(work,nonce,accepted,block,round_id)
            if accepted is None:
                self.state["shares_unknown"] += 1
            elif accepted:
                winning = nonce
                if block:
                    self.state["blocks_accepted"] += 1
                else:
                    self.state["shares_accepted"] += 1
            else:
                self.state["shares_rejected"] += 1
            self.emit("accepted" if accepted else "unknown" if accepted is None else "rejected",reason,
                      nonce=nonce,latency_ms=self.state["latency_ms"])
            if accepted and block:
                if self.c["stop_after_block"]:
                    self.stop.set()
                # Wait for fresh Core work after successful submission.
                while self.connection.valid(work) and not self.stop.wait(.1):
                    if time.monotonic()-before > 3:
                        break
                return True, winning
        return False, winning

    def round(self, executor, work):
        if self.c.get("distribution_enabled", False) and self.c["strategy"] == "thesis2" and not self.c["single_nonce_only"]:
            from .distribution.runtime import Runtime
            if self.distributor is None: self.distributor = Runtime(self)
            return self.distributor.round(executor, work)
        import supt_streams as ss
        ss.set_active_search_mode(self.c["strategy"])
        round_id = ss.begin_round(work.height,search_mode=self.c["strategy"])
        began = time.monotonic(); attempted = 0; winning = -1
        tasks = iter(self.tasks(work)); pending = {}; retry = deque(); exhausted = False
        submitted = set()
        try:
            while pending or not exhausted or retry:
                invalid = (self.stop.is_set() or not self.connection.valid(work) or self.paused() or
                           (self.c["run_seconds"] and time.monotonic()-self.monotonic_start >= self.c["run_seconds"]) or
                           (self.c["round_restart_seconds"] and time.monotonic()-began >= self.c["round_restart_seconds"]))
                if invalid:
                    exhausted = True; retry.clear()
                slots=self.resources.local_workers()
                while not invalid and len(pending) < slots and (not exhausted or retry):
                    try:
                        task = retry.popleft() if retry else next(tasks)
                    except StopIteration:
                        exhausted = True; break
                    pending[executor.submit(self.scan_task,work,task)] = task
                if not pending:
                    if not invalid and not exhausted and slots==0:
                        self.tick();self.stop.wait(.1);continue
                    break
                done,_ = wait(pending,timeout=.1,return_when=FIRST_COMPLETED)
                for future in done:
                    task = pending.pop(future)
                    tried,hits,tail,seconds = future.result()
                    self.priority.observe(task,tried,hits)
                    self.state['priority'] = self.priority.description()
                    attempted += tried
                    with self.lock:
                        self.state["hashes"] += tried
                    self.sample_batch(work,task,tried,round_id)
                    self.model_telemetry.batch(work,task,tried,round_id,hits)
                    if tail and not invalid:
                        retry.append(tail)
                    accepted_block, accepted_nonce = self.submit_hits(work, hits, submitted, round_id)
                    if accepted_nonce != -1: winning = accepted_nonce
                    if accepted_block: return
                self.tick()
        finally:
            # Account every in-flight batch, even during a stop or successful block.
            for future,task in pending.items():
                tried,drained_hits,_,_ = future.result()
                attempted += tried
                with self.lock:
                    self.state["hashes"] += tried
                self.sample_batch(work,task,tried,round_id)
                self.model_telemetry.batch(work,task,tried,round_id,drained_hits)
            self.active_seconds += time.monotonic()-began
            ss.end_round(round_id,winning,attempted,time.monotonic()-began)
            self.state["rounds"] += 1

    def tick(self):
        now = time.monotonic()
        with self.lock:
            if not self.samples or now-self.samples[-1][0] >= 1:
                self.samples.append((now,self.state["hashes"]))
                atomic_json(self.logs/"status.json",self.snapshot())

    def run(self):
        self.provider.start()
        import supt_streams as ss
        ss._round_counter = int(time.time() * 1000)
        if self.c["yield_cpu"]:
            try:
                os.nice(5)
            except (OSError, AttributeError):
                pass
        if self.c["keep_awake"] and Path("/usr/bin/caffeinate").exists():
            self.awake = subprocess.Popen(["/usr/bin/caffeinate","-i","-w",str(os.getpid())],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
        self.emit("start",f"Started · {self.c['connection']} · {self.c['strategy']} · {self.c['workers']} workers")
        if not self.hasher.lib:
            self.emit("notice","Using Python hashing; run install.command to build native acceleration")
        self.connection.start()
        try:
            self.resources.start()
            with ThreadPoolExecutor(max_workers=self.resources.capacity,thread_name_prefix="sha256") as executor:
                while not self.stop.is_set():
                    if ((self.c["max_rounds"] and self.state["rounds"] >= self.c["max_rounds"]) or
                        (self.c["run_seconds"] and time.monotonic()-self.monotonic_start >= self.c["run_seconds"])):
                        self.emit("stop","Configured session limit reached")
                        self.stop.set()
                        break
                    if self.paused():
                        self.state["state"] = "PAUSED"
                        self.tick(); self.stop.wait(.2); continue
                    work = self.connection.work()
                    if work is None:
                        self.state["state"] = "CONNECTING"
                        self.tick(); self.stop.wait(.2); continue
                    self.state["state"] = "MINING"
                    self.state["height"] = work.height
                    self.round(executor,work)
        finally:
            self.resources.close()
            if self.distributor is not None: self.distributor.close()
            self.provider.close()
            self.pruner.close()
            self.connection.close()
            ss.shutdown_writer()
            self.model_telemetry.close()
            if self.awake:
                self.awake.terminate()
            self.state["state"] = "STOPPED"
            self.tick()

    def summary(self, desktop=True):
        snapshot = self.snapshot(); snapshot["events"] = []
        snapshot["ended"] = time.time()
        atomic_json(self.logs/"last-session.json",snapshot)
        append_log(self.logs/"reports.jsonl",snapshot)
        if desktop:
            stamp = datetime.datetime.now().strftime("%Y-%m-%d %H.%M.%S")
            path = ROOT.parent/f"BTC-miner-summary {stamp}.txt"
            path.parent.mkdir(exist_ok=True)
            path.write_text("BTC MINER — SESSION\n\n" + "\n".join(f"{key}: {value}" for key,value in snapshot.items() if key not in ("events","rates")) + "\n")
            return str(path)
        return str(self.logs/"last-session.json")
