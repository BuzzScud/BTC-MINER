"""Live lossless filtering, with bounded work and retention on every unknown result."""
import hashlib
from array import array
import json
import os
import select
import subprocess
import sys
import time
from . import ROOT
from .platform_support import pipe_read

MODEL='bitcoin-sha256d-v1'


class Pruner:
    def __init__(self,config):
        self.enabled=config.get('pruning_enabled',True)
        self.budget_ms=config.get('pruning_budget_ms',1000)
        self.sample=config.get('pruning_candidates',8)
        self.process=None;self.last_job=None;self.geometry_v2=False;self.geometry_offer_sent=False;self.last_transport=None
        self.state={'enabled':self.enabled,'model':MODEL,'jobs_checked':0,'candidates_checked':0,
                    'candidates_excluded':0,'unknown_jobs':0,'seconds':0.0,
                    'verification_hashes':0,'contradictions':0,
                    'scope':'Symbolic proposals independently checked with SHA256d; unknowns and winners retained. Verification hashes are additional work.',
                    'last_reason':'waiting for work'}

    def close(self):
        p=self.process;self.process=None;self.geometry_v2=False;self.geometry_offer_sent=False
        self.state['geometry_v2_negotiated']=False
        if p is None:return
        if p.poll() is None:
            p.terminate()
            try:p.wait(timeout=.5)
            except subprocess.TimeoutExpired:p.kill();p.wait(timeout=1)
        for stream in (p.stdin,p.stdout):
            if stream:stream.close()

    def account_transport(self, stats, replace=False):
        previous=self.last_transport if replace else None
        self.last_transport=stats
        self.state['transport_mode']=stats['mode']
        delta=stats['saved_bytes']-(previous['saved_bytes'] if previous else 0)
        self.state['transport_bytes_saved']=self.state.get('transport_bytes_saved',0)+delta
        jobs=int(stats['saved_bytes']>0)-(int(previous['saved_bytes']>0) if previous else 0)
        self.state['compressed_jobs']=self.state.get('compressed_jobs',0)+jobs

    def query(self,request):
        if self.process is None or self.process.poll() is not None:
            self.close()
            # A replacement process has not advertised NG2. Convert a prepared
            # envelope back to exact points before selecting baseline NG1.
            from base64 import b64decode
            if 'nonce_geometry' in request and b64decode(request['nonce_geometry'])[:3]==b'NG2':
                from .geometry_codec import decode_points, compact_request
                transport_started=time.monotonic()
                raw={k:v for k,v in request.items() if k!='nonce_geometry'}
                raw['nonces']=decode_points(request['nonce_geometry'])
                request,stats=compact_request(raw)
                self.account_transport(stats,replace=True)
                self.state['transport_seconds']=self.state.get('transport_seconds',0.0)+time.monotonic()-transport_started
            bundled=ROOT/'.test-tools/abacus-solver/bin/python'
            interpreter=str(bundled) if bundled.is_file() else sys.executable
            self.process=subprocess.Popen([interpreter,'-u','-B','-m','btcminer.pruning_worker'],
                cwd=ROOT,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
        p=self.process
        if not self.geometry_offer_sent:
            from .geometry_codec import wire_size
            offered=dict(request,geometry_offer=True)
            self.state['capability_request_bytes']=self.state.get('capability_request_bytes',0)+wire_size(offered)-wire_size(request)
            request=offered;self.geometry_offer_sent=True
        p.stdin.write((json.dumps(request)+'\n').encode());p.stdin.flush()
        # Includes process/model loading. Timeout or process death retains input.
        deadline=time.monotonic()+2+self.budget_ms/1000
        line=b''
        while b'\n' not in line and len(line)<65536:
            try:
                chunk=pipe_read(p.stdout,min(8192,65536-len(line)),max(0,deadline-time.monotonic()))
            except TimeoutError:
                self.close();raise
            if not chunk:break
            line+=chunk
        if not line.endswith(b'\n') or line.count(b'\n')!=1:
            self.close();raise ValueError('incomplete pruning response')
        return json.loads(line)

    def filter_task(self,work,task):
        key=(work.header[:76],work.target,work.generation)
        if not self.enabled or key==self.last_job:return task
        self.last_job=key
        if 'nonces' in task:
            size=len(task['nonces']);candidates=list(task['nonces'][:self.sample])
        else:
            size=task['count'];candidates=[(task['start']+i)&0xffffffff for i in range(min(size,self.sample))]
        if not candidates:return task
        request={'model':MODEL,'header':work.header.hex(),'target':str(work.target),
                 'nonces':candidates,'budget_ms':self.budget_ms}
        digest=hashlib.sha256(json.dumps([request['header'],request['target'],candidates],separators=(',',':')).encode()).hexdigest()
        # Exact symbolic transport, with whole-message size comparison and a
        # local replay gate. Raw candidates remain the fallback.
        from .geometry_codec import compact_request
        transport_started = time.monotonic()
        request, transport = compact_request(request, allow_predictive=bool(self.geometry_v2 and self.process is not None and self.process.poll() is None))
        self.state['transport_seconds'] = self.state.get('transport_seconds', 0.0)+time.monotonic()-transport_started
        self.account_transport(transport)
        began=time.monotonic();self.state['jobs_checked']+=1;self.state['candidates_checked']+=len(candidates)
        try:
            result=self.query(request)
            keep=result.get('keep')
            if result.get('model')!=MODEL or result.get('key')!=digest or not isinstance(keep,list) or any(type(n)!=int or n not in candidates for n in keep):
                raise ValueError('unverified or wrong-job pruning response')
            if len(keep)!=len(set(keep)) or len(candidates)!=len(set(candidates)):
                raise ValueError('duplicate pruning candidate')
            from .geometry_predictive import capability
            if 'geometry_capability' in result:
                from .geometry_codec import wire_size
                baseline={k:v for k,v in result.items() if k!='geometry_capability'}
                self.state['capability_response_bytes']=self.state.get('capability_response_bytes',0)+wire_size(result)-wire_size(baseline)
                self.geometry_v2 = result['geometry_capability'] == capability()
            self.state['geometry_v2_negotiated'] = self.geometry_v2
            removed=set(candidates)-set(keep)
            if result.get('excluded')!=len(removed):raise ValueError('inconsistent pruning count')
            self.state['last_reason']=result.get('reason','checked')
            # An UNSAT response is not a Lean proof of the Python/SMT model.
            # Check each proposed exclusion against the actual Bitcoin hash.
            from .native import hash256
            for nonce in tuple(removed):
                value = int.from_bytes(hash256(work.header[:76]+nonce.to_bytes(4,'little')), 'little')
                self.state['verification_hashes'] += 1
                if value <= work.target:
                    removed.remove(nonce)
                    self.state['contradictions'] += 1
                    self.state['last_reason'] = 'Solver contradicted SHA256d; winning candidate retained'
            self.state['unknown_jobs']+=bool(result.get('unknown',True))
            for name in ('adaptive_splits','completed_buckets','solver_checks'):
                self.state[name]=self.state.get(name,0)+int(result.get(name,0))
        except (OSError,ValueError,TypeError,KeyError,AttributeError) as e:
            self.close();removed=set();self.state['unknown_jobs']+=1;self.state['last_reason']=str(e)
        finally:self.state['seconds']+=time.monotonic()-began
        self.state['candidates_excluded']+=len(removed)
        if not removed:return task
        values=task['nonces'] if 'nonces' in task else ((task['start']+i)&0xffffffff for i in range(size))
        if isinstance(values,array):
            return {'nonces':array(values.typecode,(n for n in values if n not in removed))}
        return {'nonces':[n for n in values if n not in removed]}

    def description(self):
        return {**self.state,'transport_net_bytes_saved':self.state.get('transport_bytes_saved',0)
                -self.state.get('capability_request_bytes',0)-self.state.get('capability_response_bytes',0)}
