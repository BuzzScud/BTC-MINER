"""Production engine adapter: local and remote nodes share one partition ledger."""
from concurrent.futures import wait, FIRST_COMPLETED
from ..platform_support import fcntl
import json
import os
from pathlib import Path
import threading
import time

from ..settings import atomic_json
from ..thesis2 import Traversal, VERSION
from .geometry import job_spec
from .store import Store, Rejected
from .transport import LocalClient, read_tokens, serve
from .worker import Worker


def node_id():
    import re
    value = os.environ.get('BTC_NODE_ID','coordinator')
    if not re.fullmatch(r'[A-Za-z0-9_.-]{1,64}',value):
        raise ValueError('BTC_NODE_ID must contain 1..64 letters, digits, dots, underscores or hyphens')
    return value


class Runtime:
    def __init__(self,engine):
        self.engine=engine; self.server=None; self.thread=None; self.store=None
        self.peer=None
        self.folder=engine.logs/'distribution'; self.folder.mkdir(parents=True,exist_ok=True)
        self.owner=(self.folder/'coordinator.lock').open('a+')
        try:
            fcntl.flock(self.owner,fcntl.LOCK_EX|fcntl.LOCK_NB)
            self.node=node_id()
            self.store=Store(self.folder/'work.sqlite',lease_seconds=engine.c.get('distribution_lease_seconds',15),
                             initial_region=engine.c['batch_size'])
            port=engine.c.get('distribution_port',0)
            ready=dict(node_id=self.node,pid=os.getpid(),transport='local',database=str(self.folder/'work.sqlite'))
            if port:
                auth=engine.c.get('distribution_auth','')
                if not auth: raise ValueError('Configure distribution_auth before enabling the listener')
                tokens=read_tokens(auth)
                self.server,self.thread=serve(self.store,engine.c['distribution_host'],port,tokens,
                                               engine.c.get('distribution_cert',''),engine.c.get('distribution_key',''))
                ready.update(transport='https' if engine.c.get('distribution_cert') else 'http',
                             host=engine.c['distribution_host'],port=self.server.server_port)
                from .buffers import Peer
                self.peer=Peer(LocalClient(self.store,self.node),self.node,self.folder/'buffers',
                               peers=[p for p in tokens if p!=self.node],provider=engine.c.get('provider_enabled',False))
                self.peer.initialize()
            atomic_json(self.folder/'ready.json',ready)
        except BaseException:
            self.close(); raise

    def close(self):
        if self.server:
            self.server.shutdown(); self.server.server_close(); self.thread.join(timeout=5); self.server=None
        if self.store: self.store.close(); self.store=None
        self.owner.close()

    def round(self,executor,work):
        engine=self.engine; store=self.store
        import supt_streams as ss
        ss.set_active_search_mode('thesis2')
        round_id=ss.begin_round(work.height,search_mode='thesis2')
        began=time.monotonic(); winning=-1; submitted=set(); pending={}
        stop=threading.Event(); job=None; accounted=0; initial_count=0; progress_cursor=0
        def valid():
            elapsed=time.monotonic()-began
            return not (engine.stop.is_set() or not engine.connection.valid(work) or engine.paused() or
                        (engine.c['round_restart_seconds'] and elapsed>=engine.c['round_restart_seconds']) or
                        (engine.c['run_seconds'] and time.monotonic()-engine.monotonic_start>=engine.c['run_seconds']))
        def update():
            nonlocal accounted,progress_cursor
            stats=store.stats(job)
            delta=stats['hashed']-accounted
            with engine.lock: engine.state['hashes']+=max(0,delta)
            accounted=stats['hashed']; engine.state['distribution']=dict(stats,node_id=self.node)
            engine.state['pruning']=engine.pruner.description()
            for event in store.progress(job,progress_cursor):
                if event['hashes']:
                    values,_=store.geometry(job).batch(engine.hasher,event['start'],event['stop'],event['hashes'])
                    task={'nonces':values}
                    engine.sample_batch(work,task,event['hashes'],round_id)
                    engine.model_telemetry.batch(work,task,event['hashes'],round_id,json.loads(event['hits']))
                progress_cursor=event['id']
        try:
            engine.abacus.bind(work)
            plan=Traversal(work.header,engine.c['thesis2_step'],engine.c['thesis2_prime'],
                           workspace=engine.abacus,order=engine.c.get('thesis2_order','field'))
            engine.state.update(candidate_count=1<<32,math_source=VERSION,math_details=plan.description(),
                                resident_abacus=engine.abacus.description())
            engine.state['math_details']['candidate_backend']='distributed exact tile/cell/label regions'
            engine.state['priority']=dict(enabled=False,excluded=0,
                reason='Exact geometric prefixes are scheduled by measured node capacity')
            engine.provider.observe(work,plan)
            if not valid(): return
            spec=job_spec(work,plan)
            initial_count,progress_cursor=store.baseline(spec['id']);accounted=initial_count
            job=store.activate(spec)
            # Bounded pre-dispatch proposal pass. The existing independently
            # verified pruner supplies proposals; Store independently gates them.
            budget=engine.c.get('distribution_pruning_ms',1000)
            if budget and engine.pruner.enabled and valid():
                region=store.proof_region(job,engine.pruner.sample)
                if region:
                    geometry=store.geometry(job)
                    values=[geometry.nonce(i) for i in range(region['cursor'],region['stop'])]
                    values=[n for n in values if n is not None]
                    old=engine.pruner.budget_ms
                    try:
                        engine.pruner.budget_ms=min(old,budget)
                        kept=engine.pruner.filter_task(work,{'nonces':values})['nonces']
                        if valid():
                            store.pulse(job)
                            try:
                                store.exclude(job,region['id'],[n for n in values if n not in set(kept)])
                            except Rejected as error:
                                # A remote node may have acquired this region
                                # while the solver ran. Its lease wins; never
                                # alter assigned work under an active worker.
                                if str(error) not in ('region_not_pending','stale_job'): raise
                    finally: engine.pruner.budget_ms=old
            workers=[Worker(LocalClient(store,'local:'+self.node+':'+str(i)),hasher=engine.hasher,
                            batch_size=engine.c['batch_size'],stop=stop,cpu_duty=engine.c['cpu_duty'],
                            admission=lambda i=i:engine.resources.admission(i))
                     for i in range(engine.resources.capacity)]
            while valid():
                store.pulse(job)
                busy=set(pending.values())
                for i,worker in enumerate(workers):
                    if i not in busy:
                        if engine.resources.admission(i)[0]:pending[executor.submit(worker.step)]=i
                        else:worker.release()
                done,_=wait(pending,timeout=.05,return_when=FIRST_COMPLETED)
                for future in done:
                    pending.pop(future)
                    try: future.result()
                    except Rejected as error:
                        if str(error) not in ('stale_job','stale_lease','progress_conflict'): raise
                update()
                if self.peer: self.peer.tick(dict(job=job,state='mining',hashed=accounted))
                # Submission remains exclusively in the original engine path.
                while valid():
                    nonce=store.take_hit(job)
                    if nonce is None: break
                    reported=[]
                    def outcome(n,accepted,reason,block):
                        store.finish_hit(job,n,dict(accepted=accepted,reason=reason,block=block))
                        reported.append(n)
                        if accepted and block:
                            stop.set(); store.deactivate(job)
                    accepted_block,found=engine.submit_hits(work,[nonce],submitted,round_id,on_outcome=outcome)
                    if not reported: store.finish_hit(job,nonce,dict(accepted=None,reason='stale before submission',block=False))
                    if found!=-1: winning=found
                    if accepted_block: return
                engine.tick()
                if store.stats(job)['complete']: break
                if not done: stop.wait(.01)
        finally:
            stop.set()
            if job:
                store.deactivate(job)
            for future in pending:
                try: future.result()
                except Rejected: pass
            if job: update()
            engine.active_seconds+=time.monotonic()-began
            ss.end_round(round_id,winning,accounted-initial_count,time.monotonic()-began)
            engine.state['rounds']+=1
