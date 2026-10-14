"""User-invoked inspection, historical analysis and offline benchmarking."""
import concurrent.futures
import os
import platform
import sys
import time
from pathlib import Path
from . import ROOT, VERSION
from .settings import apply_math_environment
from .native import Hasher, hash256
from .rpc import RPC

GENESIS = bytes.fromhex(
    "010000000000000000000000000000000000000000000000000000000000000000000000"
    "3ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa4b1e5e4a29ab5f49"
    "ffff001d1dac2b7c")

def self_test(config, require_native=False):
    """Small, deterministic consensus/scanner checks without connections or logs."""
    import random
    import struct
    from .protocol import target_from_bits
    expected = "000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f"
    actual = hash256(GENESIS)[::-1].hex()
    hasher = Hasher(config["native_hasher"])
    reference = Hasher(False)
    checks = [{"name":"genesis_hash", "ok":actual == expected}]
    if require_native:
        checks.append({"name":"native_available", "ok":hasher.lib is not None})
        checks.append({"name":"native_thesis2_available", "ok":hasher.fill_nonces is not None})
    nonce = struct.unpack_from("<I", GENESIS, 76)[0]
    result = hasher.scan(GENESIS, target_from_bits("1d00ffff"), start=nonce-8, count=16)
    checks.append({"name":"genesis_nonce_and_scan_count", "ok":result == (9, nonce)})
    rng = random.Random(20260929)
    matched = True
    comparisons = 0
    for _ in range(24):
        header = bytes(rng.getrandbits(8) for _ in range(80))
        for target in (1, 1 << 250, (1 << 256)-1):
            for task in ({"start":0xfffffff0,"count":32},
                         {"nonces":[rng.randrange(1 << 32) for _ in range(32)]}):
                matched &= hasher.scan(header,target,**task) == reference.scan(header,target,**task)
                comparisons += 1
    checks.append({"name":"scanner_matches_hashlib", "ok":matched, "comparisons":comparisons})
    value = int.from_bytes(hash256(GENESIS), "little")
    checks.append({"name":"inclusive_target_boundary", "ok":
                   hasher.scan(GENESIS,value,start=nonce,count=1) == (1,nonce) and
                   hasher.scan(GENESIS,value-1,start=nonce,count=1) == (1,None)})
    from itertools import islice
    from .thesis2 import Traversal
    plan = Traversal(GENESIS)
    plan.first_tile = plan.tile_count-1
    batch = next(hasher.traversal_batches(plan,16384))["nonces"]
    checks.append({"name":"thesis2_batch_matches_reference",
                   "ok":list(batch) == list(islice(plan.nonces(),16384))})
    return {"ok":all(check["ok"] for check in checks), "hasher":hasher.source,
            "native_available":hasher.lib is not None, "native_note":hasher.reason,
            "genesis_hash":actual, "checks":checks,
            "scope":"Offline hash/scanner checks; no network connection or mining service"}

def doctor(config, connect=False):
    hasher = Hasher(config["native_hasher"])
    report = {"version":VERSION,"folder":str(ROOT),"python":sys.version.split()[0],
              "architecture":platform.machine(),"macOS":platform.mac_ver()[0],
              "logical_cpus":os.cpu_count(),"workers":config["workers"],
              "hasher":hasher.source,"native_note":hasher.reason,
              "native_thesis2_batches":hasher.fill_nonces is not None,
              "connection":config["connection"],"network":config["network"],
              "math":config["strategy"],
              "math_reference":str(ROOT/"reference/thesis2-math-in-pictures.html"),
              "optional_math_present":(ROOT/"optional/c. math").is_dir(),
              "mining_started":False}
    if config["connection"] == "core":
        rpc = RPC(config)
        report["rpc"] = rpc.url
        report["cookie_exists"] = rpc.cookie().is_file()
        if connect:
            report["node"] = rpc.check()
            from .protocol import core_work, script_for_address
            script = script_for_address(config["address"],config["network"])
            address = rpc.call("validateaddress",[config["address"]])
            if not address.get("isvalid") or address.get("scriptPubKey") != script.hex():
                raise ValueError("Bitcoin Core and the miner disagree on the payout address script")
            template = rpc.call("getblocktemplate",[{"rules":["segwit"]}])
            work = core_work(template,config["address"],config["network"],os.urandom(8),0)
            if int(template["target"],16) != work.target:
                raise ValueError("Bitcoin Core template target disagrees with its compact bits")
            # BIP23 proposal mode validates the constructed block, including
            # its merkle root and witness commitment, without checking PoW
            # or submitting/broadcasting the block.
            result = rpc.call("getblocktemplate",[{"mode":"proposal",
                             "data":(work.header+work.data["body"]).hex()}])
            if result is not None:
                raise ValueError(f"Bitcoin Core did not validate the candidate block: {result}; refresh and retry")
            report.update(core_ready=True,address_validated=True,
                          template_height=work.height,template_bits=work.bits,
                          template_transactions=len(template.get("transactions",[])),
                          proposal={"valid":True,"pow_checked":False,"broadcast":False})
    else:
        from .connections import endpoint
        if config["pool"]:
            host,port,tls = endpoint(config["pool"],config["tls"])
            report["pool"] = {"host":host,"port":port,"tls":tls}
        else:
            report["setup_needed"] = "Set pool and pool_user (or payout address)"
    return report

def inspect_math(config, height=900000, bits="17034219", strategy=None):
    apply_math_environment(config)
    if (strategy or config["strategy"]) == "thesis2":
        from .thesis2 import report
        from .protocol import target_from_bits
        target = target_from_bits(bits)
        header = bytes(68)+height.to_bytes(4,"little")+int(bits,16).to_bytes(4,"little")+bytes(4)
        result = report(header,config["thesis2_step"],config["thesis2_prime"],order=config.get('thesis2_order','field'))
        result.update({"height":height,"bits":bits,"target":f"{target:064x}",
                       "header_context":"Synthetic inspection header. Live mining seeds from the actual 76-byte header prefix."})
        return result
    from thesis_mining import (nonce_generate_unified_py, bits_compact_to_difficulty_bits, recovery_suggested_nonce,
                              build_candidate_list, quadrant_from_nonce, nonce_to_lattice_500d,
                              get_base_nonce_source, get_last_seed_prime_path)
    from .protocol import target_from_bits, DIFF1
    target = target_from_bits(bits)
    exponent = bits_compact_to_difficulty_bits(int(bits,16))
    base = nonce_generate_unified_py(height,exponent)
    rec = recovery_suggested_nonce(bytes.fromhex(bits))
    candidates = build_candidate_list(base,base if rec is None else rec,0,1<<32,block_height=height)
    return {"strategy_version":"legacy-2026-05","height":height,"bits":bits,"target":f"{target:064x}",
            "network_difficulty":DIFF1/target,"legacy_difficulty_parameter":exponent,
            "base_nonce":base,"recovery_nonce":rec,"base_source":get_base_nonce_source(),
            "seed_path":get_last_seed_prime_path(),"entropy_bounds":[config["entropy_min"],config["entropy_max"]],
            "candidates":len(candidates),"space_percent":len(candidates)/(1<<32)*100,
            "quadrants":[sum(quadrant_from_nonce(n)==q for n in candidates) for q in range(4)],
            "first_20":candidates[:20],"lattice_500d_first_12":nonce_to_lattice_500d(base)[:12],
            "interpretation":"Candidate ordering and diagnostics; legacy parameter is not Bitcoin hash difficulty."}

def backtest(config, count, strategy=None):
    apply_math_environment(config)
    from thesis_mining import nonce_generate_unified_py, recovery_suggested_nonce, build_candidate_list, bits_compact_to_difficulty_bits
    rpc = RPC(config); chain = rpc.call("getblockchaininfo")
    end = chain["blocks"]; start = max(0,end-count+1)
    rows = []
    mode = strategy or config["strategy"]
    for height in range(start,end+1):
        blockhash = rpc.call("getblockhash",[height])
        block = rpc.call("getblockheader",[blockhash,True])
        bits = block["bits"]; actual = block["nonce"]
        if mode == "thesis2":
            from .thesis2 import Traversal
            raw = bytes.fromhex(rpc.call("getblockheader",[blockhash,False]))
            plan = Traversal(raw,config["thesis2_step"],config["thesis2_prime"],order=config.get('thesis2_order','field'))
            position = plan.rank(actual)
            rows.append({"height":height,"actual_nonce":actual,"index_zero_based":position,
                         "hashes_to_published_nonce":position+1,"nonce_domain":1<<32,
                         "mapping_version":plan.description()['mapping_version'],"first_tile":plan.first_tile})
            continue
        base = nonce_generate_unified_py(height,bits_compact_to_difficulty_bits(int(bits,16)))
        rec = recovery_suggested_nonce(bytes.fromhex(bits))
        minimal = list(dict.fromkeys([base] + ([] if rec is None else [rec])))
        candidates = build_candidate_list(base,base if rec is None else rec,0,1<<32,block_height=height)
        delta = (actual-base)&0xffffffff
        rows.append({"height":height,"actual_nonce":actual,"base_nonce":base,
                     "minimal_hit":actual in minimal,"candidate_hit":actual in candidates,
                     "candidate_index":candidates.index(actual) if actual in candidates else None,
                     "candidate_count":len(candidates),"circular_distance":min(delta,(1<<32)-delta)})
    if mode == "thesis2":
        return {"chain":chain["chain"],"strategy":mode,"blocks":len(rows),"details":rows,
                "interpretation":"Rank of a published nonce on its recorded header. Full coverage makes membership automatic; this is not a mining speedup or prediction."}
    return {"chain":chain["chain"],"blocks":len(rows),"minimal_hits":sum(r["minimal_hit"] for r in rows),
            "candidate_hits":sum(r["candidate_hit"] for r in rows),"details":rows,
            "interpretation":"Historical nonce membership only; does not establish a speedup or predict rewards."}

def benchmark(config, seconds=3, sweep=False, strategy=None):
    if strategy is not None:
        return benchmark_engine(config,seconds,sweep,strategy)
    hasher = Hasher(config["native_hasher"])
    workers = sorted(set(min(os.cpu_count() or 1,n) for n in (1,2,4,8))) if sweep else [config["workers"]]
    rows = []
    for count in workers:
        began = time.monotonic(); deadline = began+seconds
        def worker(index):
            total = 0; nonce = index * (1<<28)
            while time.monotonic()<deadline:
                tried,_ = hasher.scan(GENESIS,1,start=nonce,count=config["batch_size"])
                total += tried; nonce = (nonce+config["batch_size"])&0xffffffff
            return total
        with concurrent.futures.ThreadPoolExecutor(max_workers=count) as executor:
            hashes = sum(executor.map(worker,range(count)))
        elapsed = time.monotonic()-began
        rows.append({"workers":count,"hashes":hashes,"elapsed":round(elapsed,3),"hashrate":round(hashes/elapsed,1)})
    return {"hasher":hasher.source,"offline":True,"results":rows,
            "note":"Raw hashing only. No connection, share submissions, strategy overhead or SUPT sampling."}

def benchmark_engine(config, seconds, sweep, strategy):
    """Run the real scheduler and diagnostics against fixed, offline work."""
    import tempfile
    from .engine import Engine
    from .protocol import Work
    import supt_streams as ss
    work = Work(GENESIS,1,1,0,"1d00ffff","offline-benchmark",1)
    class OfflineConnection:
        label = "offline benchmark"
        connected = True
        def start(self): pass
        def close(self): self.connected = False
        def valid(self, work): return self.connected
        def work(self): return work
        def submit(self, work, nonce):
            raise RuntimeError("Offline benchmarks cannot submit solutions")
    workers = sorted(set(min(os.cpu_count() or 1,n) for n in (1,2,4,8))) if sweep else [config["workers"]]
    rows = []
    for count in workers:
        with tempfile.TemporaryDirectory(prefix="btc-benchmark-") as folder:
            c = dict(config,strategy=strategy,workers=count,pause_on_active=0,keep_awake=False,
                     yield_cpu=False,run_seconds=seconds,max_rounds=0,round_restart_seconds=0,
                     single_nonce_only=False)
            engine = Engine(c,logs=folder)
            engine.connection = OfflineConnection()
            before = ss._stream_a_rows
            began = time.monotonic()
            engine.run()
            elapsed = time.monotonic()-began
            rows.append({"workers":count,"hashes":engine.state["hashes"],"elapsed":round(elapsed,3),
                         "hashrate":round(engine.state["hashes"]/elapsed,1),
                         "diagnostic_samples":ss._stream_a_rows-before})
    apply_math_environment(config)
    return {"hasher":engine.hasher.source,"offline":True,"strategy":strategy,"results":rows,
            "supt_log":config["supt_log"],"supt_sample_every":config["supt_sample_every"],
            "native_thesis2_batches":engine.hasher.fill_nonces is not None,
            "note":"Real scheduler, nonce generation and configured diagnostics in temporary logs. No network or submissions; idle/sleep policies disabled for measurement."}

def probe(config, window="512", source="both", compare=False, z0=False):
    apply_math_environment(config)
    from supt_probe import run_probe_report, run_compare_report, run_z0_probe_report
    if compare:
        # Legacy mode buffers are process-local. Rehydrate persisted streams by round/mode below.
        from .settings import LOGS
        import json, csv
        import supt_streams as ss
        mapping = {}
        path = LOGS/"math/search_mode.jsonl"
        if path.exists():
            for line in path.read_text().splitlines():
                try:
                    row = json.loads(line); mode = row["search_mode"]
                    if mode not in ss._mode_round_counts:
                        continue
                    mapping[row["round_id"]] = mode
                    ss._mode_round_counts[mode] += 1
                    ss._mode_hashes_tried[mode].append(row["hashes_tried"])
                    ss._mode_seconds[mode].append(row["seconds"])
                    ss._mode_stream_a_samples[mode] += row["stream_a_samples"]
                except (KeyError,ValueError,TypeError):
                    continue
        path = LOGS/"math/nonce_hash_stream.csv"
        if path.exists():
            with path.open() as f:
                for row in csv.DictReader(f):
                    mode = mapping.get(int(row["block"]))
                    if mode:
                        ss._mode_hash_int[mode].append(int(row["hash_int"]))
        return run_compare_report()
    return (run_z0_probe_report if z0 else run_probe_report)(window_filter=window, source_filter=source)
