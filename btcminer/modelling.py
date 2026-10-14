"""Local live experiment: real nonce generators and SHA256d, private Core optional.

No production settings, service control, wallets or RPC endpoints are reused.
Targets change at a completed scan boundary. A pending batch keeps its unused
suffix, including after a successful hash. Experimental tower bounds gate work.
"""
from array import array
from collections import deque
from dataclasses import dataclass
import hashlib
import json
import math
import os
from pathlib import Path
import secrets
import socket
import subprocess
import threading
import time
import urllib.request

from . import ROOT
from .native import Hasher, hash256
from .thesis2 import Traversal
from .scale_graph import Frame, FormulaValue
from .settings import DEFAULTS, atomic_json
from .protocol import core_work
from .rpc import RPC

SERVICE = 'btc-scale-lab-v1'
P = 2**256 - 2**32 - 977
GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
G_SOURCE = 'https://github.com/bitcoin-core/secp256k1/blob/master/src/group_impl.h'
MAX_HASH = (1 << 256) - 1
DEFAULT = dict(mode='model', bits=18, depths=[8, 2, 3], lift_bits=0, scale_power=0,
               wait_limit=30, min_rate=1000, sweep_end=32, sweep_step=2, sweep_seconds=10)


def validate_control(old, change):
    if not isinstance(change, dict) or set(change) - set(DEFAULT):
        raise ValueError('Unknown controls')
    c = dict(old, **change)
    if c['mode'] not in ('model', 'regtest'): raise ValueError('Choose model or regtest')
    for key, low, high in [('bits',0,256), ('lift_bits',0,4096), ('scale_power',0,256),
                          ('wait_limit',1,86400), ('min_rate',0,1000000000),
                          ('sweep_end',0,256), ('sweep_step',1,64), ('sweep_seconds',1,600)]:
        if type(c[key]) is not int or not low <= c[key] <= high:
            raise ValueError(f'{key} must be an integer between {low} and {high}')
    if not isinstance(c['depths'], list) or len(c['depths']) != 3 or any(type(d) is not int or not 0 <= d <= 2048 for d in c['depths']):
        raise ValueError('Three rod depths between 0 and 2048 are required')
    return c


def target_for(bits, network_target=None):
    t = MAX_HASH >> bits
    return min(t, network_target) if network_target is not None else t


def tower_probe(plan, controls, label_index=0, cell_index=0):
    """A lifted, magnitude-rescaled value must read exactly before dispatch.

    Lifting by multiples of 144000 preserves the nonce offset. Rescaling a
    FormulaValue preserves its rational value; it does NOT multiply the nonce.
    Bounds deliberately include all lifts from zero to the selected maximum.
    """
    cell = (plan.cell_phase + cell_index * plan.prime) % 400
    u = 360 * cell + plan.phase + int(plan.residues[label_index])
    lift = (1 << controls['lift_bits']) - 1
    scale = 10 ** controls['scale_power']
    formula = FormulaValue(('add','u',('mul',144000,'lift'))).rescale(scale)
    frame = Frame((2,3,5), tuple(controls['depths']))
    column = formula.column(frame, {'u':u,'lift':lift}, {'u':(0,287998),'lift':(0,lift)})
    shallow = Frame((2,3,5), tuple(min(d,t) for d,t in zip(frame.depths,(7,2,3))))
    projected = column.project(shallow)
    reference = scale * (u + 144000 * lift)
    if column.residues != tuple(reference % m for m in frame.moduli):
        raise ArithmeticError('Independent rod evaluation mismatch')
    if projected.residues != tuple(reference % m for m in shallow.moduli):
        raise ArithmeticError('Scale projection mismatch')
    out = dict(status='exact' if column.bounds[1]-column.bounds[0] < frame.capacity else 'capacity_limit',
               depths=list(frame.depths), moduli=[str(m) for m in frame.moduli],
               capacity=str(frame.capacity), capacity_bits=frame.capacity.bit_length(),
               bound=str(column.bounds[1]), residues=[str(x) for x in column.residues],
               magnitude_scale=str(scale), lift=str(lift), offset=u%144000,
               formula='(u + 144000 × lift) × scale / scale', projection_ok=True,
               fibre_sizes=list(frame.bases), readback=None)
    if out['status'] == 'exact':
        value = formula.value(frame, {'u':u,'lift':lift}, {'u':(0,287998),'lift':(0,lift)})
        if value.denominator != 1 or value.numerator != u + 144000*lift or int(value)%144000 != u%144000:
            raise ArithmeticError('Bounded readback or magnitude scaling mismatch')
        out['readback'] = str(value.numerator)
    return out


def independent_nonces(plan, cursor, count):
    """Direct integer reference, separate from native CRT and descriptor.offset."""
    out = []
    while len(out) < count and cursor < 29827*144000:
        turn, index = divmod(cursor,144000)
        cell, label = divmod(index,360)
        offset = (360*((plan.cell_phase+cell*plan.prime)%400)+plan.phase+int(plan.residues[label]))%144000
        n = ((plan.first_tile+turn)%29827)*144000+offset
        cursor += 1
        if n < 1 << 32: out.append(n)
    return out, cursor


class Lane:
    def __init__(self, header, order, hasher):
        self.plan = Traversal(header, order=order)
        self.batches = hasher.traversal_batches(self.plan,8192)
        self.pending = array('I'); self.at = 0; self.raw_cursor = 0
        self.hashes = self.generated = self.verified = self.hits = 0
        self.replays = 0; self.best = None; self.exhausted = False
        self.started = time.monotonic(); self.last_hit = self.started
        # The label and cell permutations imply a complete 144000-offset tile.
        if set(self.plan.residues) != set(range(360)) or math.gcd(self.plan.prime,400) != 1:
            raise ArithmeticError('Traversal is not a permutation')

    def take(self):
        if self.at == len(self.pending):
            try: values = next(self.batches)['nonces']
            except StopIteration:
                self.exhausted = True
                if self.hashes != 1 << 32: raise ArithmeticError('Nonce space exhausted with missing candidates')
                return None
            expected, cursor = independent_nonces(self.plan, self.raw_cursor, len(values))
            if list(values) != expected: raise ArithmeticError('Native nonce sequence differs: duplicate, omission or wrong order')
            self.raw_cursor = cursor; self.generated += len(values); self.verified += len(values)
            self.pending = values; self.at = 0
        return self.pending[self.at:]

    def record(self, tried, winner, values, header, target):
        if type(tried) is not int or not 1 <= tried <= len(values): raise ArithmeticError('Invalid native attempted count')
        if winner is None and tried != len(values): raise ArithmeticError('Native scan skipped an unfinished suffix')
        if winner is not None and values[tried-1] != winner: raise ArithmeticError('Winner position disagrees with attempted count')
        # Three independent hashes per scan and every reported winner. Best is
        # explicitly a sampled best, not an assertion about unrecorded hashes.
        samples = set([int(values[0]), int(values[(tried-1)//2]), int(values[tried-1])])
        for nonce in samples:
            h = header[:76] + nonce.to_bytes(4,'little')
            value = int.from_bytes(hashlib.sha256(hashlib.sha256(h).digest()).digest(),'little')
            self.replays += 1
            self.best = value if self.best is None else min(self.best,value)
            if value <= target and nonce != winner:
                raise ArithmeticError('Native scan missed a target-valid replay sample')
            if nonce == winner and value > target: raise ArithmeticError('Native winner fails independent SHA256d')
        self.at += tried; self.hashes += tried
        if winner is not None:
            self.hits += 1; self.last_hit = time.monotonic()

    def view(self):
        return dict(order=self.plan.order, hashes=self.hashes, hits=self.hits,
                    candidates_verified=self.verified, generated=self.generated,
                    pending=len(self.pending)-self.at, raw_cursor=self.raw_cursor,
                    hash_replays=self.replays, sampled_best=None if self.best is None else f'{self.best:064x}',
                    exhausted=self.exhausted, descriptor=self.plan.descriptor.packed().hex(),
                    seconds_since_hit=time.monotonic()-self.last_hit)


class PrivateChain:
    def __init__(self, folder, binary=None):
        self.folder = Path(folder); self.binary = Path(binary or ROOT/'.test-tools/bitcoin-31.1/bin/bitcoind')
        self.process = None; self.log = None; self.rpc = None; self.extra = 0; self.ready = False

    def start(self):
        if self.process is not None and self.process.poll() is None:
            if self.ready: return
            self.close()  # Reconcile a partially initialized node on retry.
        if not self.binary.is_file(): raise ValueError('Private Core binary is unavailable: '+str(self.binary))
        self.folder.mkdir(parents=True,exist_ok=True,mode=0o700)
        with socket.socket() as sock: sock.bind(('127.0.0.1',0)); port=sock.getsockname()[1]
        self.config = dict(DEFAULTS,network='regtest',rpc_host='127.0.0.1',rpc_port=port,
                           rpc_datadir=str(self.folder),rpc_cookie=str(self.folder/'regtest/.cookie'),rpc_timeout=5)
        self.rpc = RPC(self.config)
        self.log = (self.folder/'console.log').open('ab')
        self.process = subprocess.Popen([str(self.binary),'-regtest',f'-datadir={self.folder}',
            '-server=1','-listen=0','-connect=0','-dnsseed=0','-discover=0','-networkactive=0',
            '-rpcbind=127.0.0.1',f'-rpcport={port}','-fallbackfee=0.0002','-printtoconsole=1'],
            stdin=subprocess.DEVNULL,stdout=self.log,stderr=subprocess.STDOUT)
        deadline=time.monotonic()+25
        while True:
            try: info=self.rpc.call('getblockchaininfo'); break
            except (ValueError,RuntimeError):
                if self.process.poll() is not None or time.monotonic()>deadline: raise RuntimeError('Private Core startup failed; see modelling node console')
                time.sleep(.1)
        if info['chain'] != 'regtest' or self.rpc.call('getconnectioncount') != 0: raise RuntimeError('Private chain isolation check failed')
        wallets=self.rpc.call('listwalletdir')['wallets']
        if any(w['name']=='scale-lab' for w in wallets):
            if 'scale-lab' not in self.rpc.call('listwallets'): self.rpc.call('loadwallet',['scale-lab'])
        else: self.rpc.call('createwallet',['scale-lab'])
        self.config['address']=self.rpc.call('getnewaddress',['scale-lab','bech32'])
        if info['blocks']<101: self.rpc.call('generatetoaddress',[101-info['blocks'],self.config['address']],timeout=45)
        self.ready=True

    def work(self, cancelled):
        self.start()
        txid=self.rpc.call('sendtoaddress',[self.rpc.call('getnewaddress',['scale-lab','bech32']),0.01])
        tx=self.rpc.call('getrawtransaction',[txid,True])
        if not any(v.get('txinwitness') for v in tx['vin']): raise ArithmeticError('Signed witness transaction fixture missing')
        deadline=time.monotonic()+15
        while not cancelled():
            template=self.rpc.call('getblocktemplate',[{'rules':['segwit']}])
            if any(t['txid']==txid for t in template['transactions']): break
            if time.monotonic()>deadline: raise RuntimeError('Core template did not include the signed fixture transaction')
            time.sleep(.1)
        else: return None
        self.extra += 1
        work=core_work(template,self.config['address'],'regtest',self.extra.to_bytes(8,'little'),self.extra)
        work.data['fixture_txid']=txid
        return work

    def submit(self,work,nonce):
        header=work.header[:76]+nonce.to_bytes(4,'little')
        result=self.rpc.call('submitblock',[(header+work.data['body']).hex()])
        if result is not None: raise ArithmeticError('Private Core rejected a solved block: '+str(result)[:160])
        blockhash=hash256(header)[::-1].hex()
        block=self.rpc.call('getblock',[blockhash])
        if work.data['fixture_txid'] not in block['tx']: raise ArithmeticError('Accepted block omitted the signed fixture')
        if self.rpc.call('getconnectioncount') != 0: raise ArithmeticError('Private node acquired a peer')
        return dict(hash=blockhash,height=block['height'],transactions=len(block['tx']),
                    fixture_txid=work.data['fixture_txid'],header_hex=header.hex(),public_peers=0)

    def close(self):
        if self.process is not None and self.process.poll() is None:
            try:self.rpc.call('stop')
            except Exception:pass
            try:self.process.wait(timeout=8)
            except subprocess.TimeoutExpired:self.process.terminate();self.process.wait(timeout=5)
        if self.log:self.log.close()
        self.process=None;self.ready=False


class Lab:
    def __init__(self, folder, binary=None):
        self.folder=Path(folder);self.folder.mkdir(parents=True,exist_ok=True)
        self.lock=threading.RLock();self.stop=threading.Event();self.controls=dict(DEFAULT,depths=list(DEFAULT['depths']))
        self.running=False;self.reset_id=0;self.revision=0;self.applied_revision=-1
        self.hasher=Hasher();self.chain=PrivateChain(self.folder/'private-node',binary)
        self.events=deque(maxlen=400);self.history=deque(maxlen=600);self.lanes={}
        self.last_lanes={};self.totals={order:dict(hashes=0,hits=0,generated=0,candidates_verified=0,hash_replays=0) for order in ('field','flower')}
        self.state='IDLE';self.error='';self.probe={};self.work=None;self.job_id=None
        self.epoch=time.monotonic();self.epoch_hashes=0;self.hashes=0;self.hits=0;self.accepted=0
        self.wait_started=self.epoch;self.last_point=0;self.scan_seconds=0.;self.warnings=[]
        self.sweep=False;self.sweep_since=None;self.first_limits={};self.target=target_for(DEFAULT['bits'])
        self.paused_at=time.monotonic()
        self.thread=threading.Thread(target=self.run,daemon=True,name='scale-lab-worker');self.thread.start()

    def event(self,kind,**details):
        row=dict(at=time.time(),kind=kind,**details);self.events.append(row)
        path=self.folder/'events.jsonl'
        if path.exists() and path.stat().st_size>5*1024*1024:os.replace(path,path.with_suffix('.jsonl.1'))
        with path.open('a') as f:f.write(json.dumps(row,allow_nan=False)+'\n')

    def command(self,action,changes=None):
        with self.lock:
            if action=='configure':
                c=validate_control(self.controls,changes)
                if c==self.controls:return self.snapshot()
                mode_change=c['mode']!=self.controls['mode']
                self.controls=c;self.revision+=1
                if mode_change:self.reset_id+=1
                self.event('controls_requested',revision=self.revision,controls=c)
            elif action in ('start','pause','reset'):
                if action=='start':
                    if self.state=='ERROR':raise ValueError('Reset the experiment after an error')
                    if not self.running and self.paused_at is not None:
                        gap=time.monotonic()-self.paused_at;self.epoch+=gap;self.wait_started+=gap
                        for lane in self.lanes.values():lane.last_hit+=gap
                    self.paused_at=None
                    self.running=True
                elif action=='pause':
                    if self.running:self.paused_at=time.monotonic()
                    self.running=False;self.sweep_since=None
                    if self.state!='ERROR':self.state='PAUSED'
                else:
                    self.reset_id+=1;self.error='';self.state='IDLE';self.running=False
                    self.sweep=False;self.first_limits={};self.history.clear()
                    self.lanes={};self.work=None;self.job_id=None;self.applied_revision=-1
                    self.last_lanes={};self.totals={order:dict(hashes=0,hits=0,generated=0,candidates_verified=0,hash_replays=0) for order in ('field','flower')}
                    self.hashes=self.hits=self.accepted=self.epoch_hashes=0;self.scan_seconds=0.
                    self.epoch=self.wait_started=self.paused_at=time.monotonic()
                    self.probe={};self.warnings=[]
                self.event(action)
            elif action=='sweep':
                if self.controls['sweep_end']<self.controls['bits']:raise ValueError('Sweep end must be at least the current difficulty')
                if self.state=='ERROR':raise ValueError('Reset after an error')
                self.sweep=True;self.sweep_since=None;self.running=True;self.event('sweep_started')
            elif action=='stop_sweep':self.sweep=False;self.event('sweep_stopped')
            else:raise ValueError('Unknown action')
            return self.snapshot()

    def snapshot(self):
        with self.lock:
            elapsed=max(.001,time.monotonic()-self.epoch)
            rate=(self.hashes-self.epoch_hashes)/elapsed
            log_expected=256-math.log2(self.target+1)
            return dict(service=SERVICE,root=str(ROOT),state=self.state,running=self.running,error=self.error,
                controls=self.controls,revision=self.revision,applied_revision=self.applied_revision,
                mode=self.controls['mode'],backend=self.hasher.source,hashes=self.hashes,hits=self.hits,
                accepted_blocks=self.accepted,rate=rate,scan_rate=self.hashes/max(.001,self.scan_seconds),
                epoch_seconds=elapsed,epoch_hashes=self.hashes-self.epoch_hashes,
                expected_hashes_log2=log_expected,expected_seconds=(2.0**log_expected)/rate if rate>0 else None,
                target_hex=f'{self.target:064x}',network_target_hex=f'{self.work.network_target:064x}' if self.work is not None and self.controls['mode']=='regtest' else None,
                header_hex=self.work.header.hex() if self.work is not None else None,job_id=self.job_id,
                lanes={order:dict(self.lanes[order].view() if order in self.lanes else self.last_lanes.get(order,{}),
                                 **totals) for order,totals in self.totals.items()},scale=self.probe,
                history=list(self.history),events=list(self.events),warnings=self.warnings,
                sweep=self.sweep,first_limits=self.first_limits,
                g=dict(x=f'{GX:064x}',y=f'{GY:064x}',field_prime=f'{P:064x}',
                       on_curve=(GY*GY-GX*GX*GX-7)%P==0,source=G_SOURCE,
                       role='Fixed secp256k1 generator used by Bitcoin transaction keys and signatures'),
                scope='Actual miner traversal and native hashing. Independent bounded lab scheduler; no production priority/pruning. Every generated nonce is compared with an integer reference; SHA256d replay is sampled plus every winner.',
                difficulty_scope='Local target overlay. Core consensus nBits is unchanged; only stricter solutions are submitted.',
                retention='Last 600 chart points and 400 events in this view; events also journaled with one 5 MB rotation.')

    def new_work(self,mode,generation):
        if mode=='regtest':
            return self.chain.work(lambda:self.stop.is_set() or self.reset_id!=generation or not self.running)
        from .diagnostics import GENESIS
        from .protocol import Work
        return Work(GENESIS,target_for(0),target_for(0),0,'1d00ffff','genesis-header-model',generation,{})

    def run(self):
        generation=-1;lane_turn=0
        try:
            while not self.stop.is_set():
                with self.lock:
                    active=self.running;reset_id=self.reset_id;c=dict(self.controls);revision=self.revision
                    if not active and self.state!='ERROR':self.state='PAUSED' if self.work else 'IDLE'
                if not active:self.stop.wait(.04);continue
                try:
                    if generation!=reset_id or not self.lanes:
                        with self.lock:self.state='PREPARING PRIVATE CHAIN' if c['mode']=='regtest' else 'PREPARING MODEL'
                        work=self.new_work(c['mode'],reset_id)
                        if work is None:continue
                        lanes={order:Lane(work.header,order,self.hasher) for order in ('field','flower')}
                        with self.lock:
                            if reset_id!=self.reset_id:continue
                            self.work=work;self.lanes=lanes;generation=reset_id
                            self.job_id=hashlib.sha256(work.header[:76]).hexdigest();self.wait_started=time.monotonic()
                            self.event('job',mode=c['mode'],job_id=self.job_id,header_hex=work.header.hex(),height=work.height)
                    with self.lock:
                        # Applying controls and recording a completed batch share
                        # this lock: no batch can straddle two target revisions.
                        if revision!=self.revision or generation!=self.reset_id:continue
                        if revision!=self.applied_revision:
                            self.target=target_for(c['bits'],self.work.network_target if c['mode']=='regtest' else None)
                            self.applied_revision=revision;self.epoch=time.monotonic();self.epoch_hashes=self.hashes
                            self.wait_started=self.epoch;self.sweep_since=None
                            self.event('controls_applied',revision=revision,controls=c,target_hex=f'{self.target:064x}',job_id=self.job_id)
                        order=('field','flower')[lane_turn%2];lane_turn+=1;lane=self.lanes[order]
                        before=lane.view()
                        self.probe=tower_probe(lane.plan,c)
                        if self.probe['status']=='capacity_limit':
                            self.state='CAPACITY LIMIT'
                            self.first_limits.setdefault('capacity',dict(at=time.time(),controls=c,capacity=self.probe['capacity'],bound=self.probe['bound']))
                            values=None
                        else:
                            values=lane.take();self.state='RUNNING' if values is not None else 'SPACE EXHAUSTED'
                        if values is not None:
                            scan_work=self.work
                            began=time.monotonic()
                            tried,winner=self.hasher.scan(self.work.header,self.target,nonces=values)
                            self.scan_seconds+=time.monotonic()-began
                            lane.record(tried,winner,values,self.work.header,self.target)
                            after=lane.view()
                            for name in self.totals[order]:self.totals[order][name]+=after[name]-before[name]
                            self.last_lanes[order]=after
                            self.hashes+=tried
                            if winner is not None:
                                self.hits+=1;self.wait_started=time.monotonic()
                                self.event('hit',order=order,nonce=winner,target_hex=f'{self.target:064x}',bits=c['bits'],
                                           job_id=self.job_id,header_hex=(self.work.header[:76]+winner.to_bytes(4,'little')).hex())
                        else:winner=None
                    # Core RPC is outside the state lock so the dashboard and
                    # pause controls remain responsive while Core builds work.
                    if winner is not None and c['mode']=='regtest':
                        accepted=self.chain.submit(scan_work,winner)
                        with self.lock:
                            current_job=generation==self.reset_id
                            if current_job:
                                self.accepted+=1
                                for name,item in self.lanes.items():
                                    self.last_lanes[name]=dict(item.view(),pending=0)
                                self.lanes={}
                            self.event('block_accepted',order=order,retired_run=not current_job,**accepted)
                    with self.lock:
                        now=time.monotonic()
                        self.warnings=[]
                        if now-self.wait_started>c['wait_limit']:
                            self.warnings.append('Waiting-time limit exceeded; no arithmetic error has been observed.')
                            self.first_limits.setdefault('waiting',dict(at=time.time(),controls=c))
                        elapsed=now-self.epoch;rate=(self.hashes-self.epoch_hashes)/max(.001,elapsed)
                        if elapsed>3 and rate<c['min_rate'] and self.state=='RUNNING':
                            self.warnings.append('Observed wall-clock rate is below your performance limit.')
                            self.first_limits.setdefault('performance',dict(at=time.time(),controls=c,rate=rate))
                        if now-self.last_point>=1:
                            self.history.append(dict(at=time.time(),bits=c['bits'],rate=rate,hits=self.hits,
                                accepted=self.accepted,state=self.state,mode=c['mode']))
                            self.last_point=now
                        if self.sweep:
                            if self.sweep_since is None:self.sweep_since=now
                            if now-self.sweep_since>=c['sweep_seconds']:
                                self.event('sweep_step',bits=c['bits'],epoch_hashes=self.hashes-self.epoch_hashes,state=self.state)
                                if c['bits']>=c['sweep_end']:self.sweep=False;self.event('sweep_complete')
                                else:
                                    self.controls=dict(self.controls,bits=min(c['sweep_end'],c['bits']+c['sweep_step']))
                                    self.revision+=1;self.sweep_since=None
                    self.stop.wait(.003 if values is not None else .05)
                except Exception as error:
                    with self.lock:
                        self.error=str(error)[:1000];self.state='ERROR';self.running=False;self.sweep=False
                        self.first_limits.setdefault('error',dict(at=time.time(),message=self.error,controls=c))
                        self.event('error',message=self.error)
        finally:self.chain.close()

    def close(self):
        self.stop.set();self.thread.join(timeout=60)
        atomic_json(self.folder/'last-session.json',self.snapshot())


def serve(folder,port,binary=None):
    from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
    import signal
    lab=Lab(folder,binary);token=secrets.token_urlsafe(32)
    class Handler(BaseHTTPRequestHandler):
        def log_message(self,*args):pass
        def send(self,status,content,kind='application/json'):
            if not isinstance(content,bytes):content=json.dumps(content,allow_nan=False).encode()
            self.send_response(status);self.send_header('Content-Type',kind);self.send_header('Content-Length',str(len(content)))
            self.send_header('Cache-Control','no-store');self.send_header('X-Content-Type-Options','nosniff')
            self.send_header('Content-Security-Policy',"default-src 'self'; script-src 'self' 'unsafe-inline'; style-src 'self' 'unsafe-inline'; connect-src 'self'; frame-ancestors 'none'")
            self.end_headers();self.wfile.write(content)
        def local(self):
            return self.headers.get('Host') in (f'127.0.0.1:{port}',f'localhost:{port}')
        def do_GET(self):
            if not self.local():self.send(403,{'error':'Local host required'});return
            if self.path=='/health':self.send(200,dict(service=SERVICE,root=str(ROOT),pid=os.getpid()))
            elif self.path in ('/api/state','/api/export'):self.send(200,lab.snapshot())
            elif self.path=='/':
                page=(ROOT/'src/ui/modelling.html').read_text().replace('__LAB_TOKEN__',token)
                self.send(200,page.encode(),'text/html; charset=utf-8')
            else:self.send(404,{'error':'Not found'})
        def do_POST(self):
            origin=self.headers.get('Origin')
            if (not self.local() or self.headers.get('X-Lab-Token')!=token or
                    origin not in (None,f'http://127.0.0.1:{port}',f'http://localhost:{port}')):
                self.send(403,{'error':'Local lab token required'});return
            if self.path!='/api/control':self.send(404,{'error':'Not found'});return
            try:
                size=int(self.headers.get('Content-Length','0'))
                if not 0<size<=16384:raise ValueError('Invalid request size')
                body=json.loads(self.rfile.read(size))
                if not isinstance(body,dict) or set(body)-{'action','changes'}:raise ValueError('Invalid control object')
                result=lab.command(body.get('action'),body.get('changes'))
            except (ValueError,TypeError,KeyError) as e:self.send(400,{'error':str(e)[:200]});return
            self.send(200,result)
    server=ThreadingHTTPServer(('127.0.0.1',port),Handler)
    def shutdown(*_):threading.Thread(target=server.shutdown,daemon=True).start()
    signal.signal(signal.SIGTERM,shutdown);signal.signal(signal.SIGINT,shutdown)
    try:server.serve_forever(poll_interval=.2)
    finally:server.server_close();lab.close()


def launch(port=63219,open_browser=True):
    from .platform_support import fcntl
    import sys
    folder=ROOT/'modelling';folder.mkdir(exist_ok=True)
    if type(port) is not int or not 1024<=port<=65535:raise ValueError('Port must be 1024–65535')
    with (folder/'launch.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        def health():
            try:
                opener=urllib.request.build_opener(urllib.request.ProxyHandler({}))
                with opener.open(f'http://127.0.0.1:{port}/health',timeout=.4) as r:state=json.load(r)
                return state if state.get('service')==SERVICE and state.get('root')==str(ROOT) else None
            except (OSError,ValueError):return None
        result=health();started=False
        if result is None:
            with (folder/'server.log').open('ab') as output:
                process=subprocess.Popen([sys.executable,'-B','-m','btcminer.modelling','--serve','--port',str(port)],
                    cwd=ROOT,stdin=subprocess.DEVNULL,stdout=output,stderr=subprocess.STDOUT,start_new_session=True)
            deadline=time.monotonic()+10
            while time.monotonic()<deadline and process.poll() is None:
                result=health()
                if result:break
                time.sleep(.1)
            if not result:
                if process.poll() is None:process.terminate();process.wait(timeout=5)
                raise RuntimeError('Lab could not start; inspect modelling/server.log')
            started=True
        url=f'http://127.0.0.1:{port}/';atomic_json(folder/'server.json',dict(**result,port=port,url=url))
    if open_browser:__import__('webbrowser').open(url)
    return dict(ok=True,url=url,started=started,pid=result['pid'],message='Live modelling lab ready')


if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser();parser.add_argument('--serve',action='store_true');parser.add_argument('--port',type=int,default=63219)
    args=parser.parse_args()
    if args.serve:serve(ROOT/'modelling',args.port)
    else:print(json.dumps(launch(args.port)))
