"""Provider-modeled, durable duplex frame lanes for cooperating mining nodes.

The provider builds numeric/model previews. Until it offers durable cross-peer
buffers, this service supplies ownership, sequence, storage and acknowledgment.
Each directed lane has independent credit. Receiver ACK, not publication, frees
a slot. Frames retain the model identity and immutable bytes until acknowledged.
"""
import base64
import hashlib
import json
from pathlib import Path
import re
import time

from ..settings import atomic_json
from .geometry import canonical, integer
from .store import Rejected

MODEL = dict(protocol='btc-duplex-buffer/v1',slots=16,slot_bytes=4096,
             rods=[128,9,125],rod_capacity=144000,byte_capacity=65536,
             coordinate='slot=(sequence-1) mod 16; byte=4096*slot+offset')
MODEL_ID = hashlib.sha256(canonical(MODEL).encode()).hexdigest()
SCHEMAS = {'model.publish': {'model','provenance'}, 'model.list':set(),
           'buffer.send': {'receiver','model_id','payload'},
           'buffer.read': {'sender','after'}, 'buffer.ack': {'sender','sequence'}}


def frame_geometry(sender,receiver,sequence,length):
    """Injective byte addresses on coprime rods within a bounded ring slot."""
    integer(sequence,1,(1<<53)-1);integer(length,1,MODEL['slot_bytes'])
    slot=(sequence-1)%MODEL['slots']; start=slot*MODEL['slot_bytes']
    residues=[start%r for r in MODEL['rods']]
    readback=sum(r*w for r,w in zip(residues,(122625,64000,101376)))%MODEL['rod_capacity']
    if readback!=start:raise ArithmeticError('Buffer rod projection mismatch')
    return dict(lane=hashlib.sha256(canonical([sender,receiver,MODEL_ID]).encode()).hexdigest(),
                slot=slot,start=start,stop=start+length,residues=residues,
                readback=readback,model_id=MODEL_ID)


def initialize(db):
    db.executescript('''
      CREATE TABLE IF NOT EXISTS peer_models(peer TEXT PRIMARY KEY,model_id TEXT,provenance TEXT);
      CREATE TABLE IF NOT EXISTS lanes(sender TEXT,receiver TEXT,next INTEGER,acked INTEGER,
        PRIMARY KEY(sender,receiver));
      CREATE TABLE IF NOT EXISTS frames(sender TEXT,receiver TEXT,sequence INTEGER,
        model_id TEXT,digest TEXT,payload TEXT,PRIMARY KEY(sender,receiver,sequence));
    ''')


def operation(db,peer,request):
    action=request['action']
    if action=='model.publish':
        if canonical(request['model'])!=canonical(MODEL): raise Rejected('model_mismatch')
        provenance=request['provenance']
        if not isinstance(provenance,dict) or len(canonical(provenance))>32768:
            raise Rejected('invalid_provenance')
        db.execute('INSERT OR REPLACE INTO peer_models VALUES(?,?,?)',(peer,MODEL_ID,canonical(provenance)))
        return dict(node_id=peer,model_id=MODEL_ID)
    if action=='model.list':
        rows=db.execute('SELECT * FROM peer_models ORDER BY peer LIMIT 256').fetchall()
        return dict(model=MODEL,model_id=MODEL_ID,peers=[dict(node_id=r['peer'],model_id=r['model_id'],
                    backend=json.loads(r['provenance']).get('backend')) for r in rows])
    if action=='buffer.send':
        receiver=request['receiver']
        if not isinstance(receiver,str) or not 1<=len(receiver)<=128 or receiver==peer:
            raise Rejected('invalid_receiver')
        if request['model_id']!=MODEL_ID: raise Rejected('model_mismatch')
        for node in (peer,receiver):
            if db.execute('SELECT 1 FROM peer_models WHERE peer=? AND model_id=?',(node,MODEL_ID)).fetchone() is None:
                raise Rejected('peer_model_unavailable')
        try:
            encoded=request['payload']
            if not isinstance(encoded,str) or len(encoded)>5500: raise ValueError()
            raw=base64.b64decode(encoded,validate=True)
        except (ValueError,TypeError): raise Rejected('invalid_payload') from None
        if not 1<=len(raw)<=MODEL['slot_bytes']: raise Rejected('payload_limit')
        if base64.b64encode(raw).decode()!=encoded: raise Rejected('noncanonical_payload')
        db.execute('INSERT OR IGNORE INTO lanes VALUES(?,?,1,0)',(peer,receiver))
        lane=db.execute('SELECT * FROM lanes WHERE sender=? AND receiver=?',(peer,receiver)).fetchone()
        if lane['next']-lane['acked']-1>=MODEL['slots']: raise Rejected('no_credit')
        sequence=lane['next']; integer(sequence,1,(1<<53)-1)
        digest=hashlib.sha256(raw).hexdigest()
        db.execute('INSERT INTO frames VALUES(?,?,?,?,?,?)',(peer,receiver,sequence,MODEL_ID,digest,encoded))
        db.execute('UPDATE lanes SET next=next+1 WHERE sender=? AND receiver=?',(peer,receiver))
        return dict(sequence=sequence,slot=(sequence-1)%MODEL['slots'],digest=digest,model_id=MODEL_ID,
                    geometry=frame_geometry(peer,receiver,sequence,len(raw)))
    sender=request['sender']
    if not isinstance(sender,str) or not 1<=len(sender)<=128 or sender==peer: raise Rejected('invalid_sender')
    lane=db.execute('SELECT * FROM lanes WHERE sender=? AND receiver=?',(sender,peer)).fetchone()
    if action=='buffer.read':
        after=integer(request['after'],0,(1<<53)-1)
        if lane is None:
            if after: raise Rejected('invalid_cursor')
            return dict(frames=[],acked=0,next=1)
        # after=0 is restart recovery: return everything not durably ACKed.
        if after and (after<lane['acked'] or after>=lane['next']): raise Rejected('invalid_cursor')
        rows=db.execute('SELECT * FROM frames WHERE sender=? AND receiver=? AND sequence>? ORDER BY sequence LIMIT 16',
                        (sender,peer,max(after,lane['acked']))).fetchall()
        return dict(frames=[dict(r,slot=(r['sequence']-1)%MODEL['slots'],
                    geometry=frame_geometry(sender,peer,r['sequence'],len(base64.b64decode(r['payload'])))) for r in rows],
                    acked=lane['acked'],next=lane['next'])
    sequence=integer(request['sequence'],0,(1<<53)-1)
    if lane is None or sequence>=lane['next']: raise Rejected('invalid_cursor')
    ack=max(sequence,lane['acked'])
    db.execute('UPDATE lanes SET acked=? WHERE sender=? AND receiver=?',(ack,sender,peer))
    db.execute('DELETE FROM frames WHERE sender=? AND receiver=? AND sequence<=?',(sender,peer,ack))
    return dict(acked=ack,credit=MODEL['slots']-(lane['next']-ack-1))


def model_with_provider(client=None):
    """Each node may independently build/check the shared buffer model."""
    from ..provider import ProviderClient, evaluation_number, scrub
    client=client or ProviderClient(timeout=5)
    if not client.token: client.authenticate()
    cases=[('byte_capacity','16*4096',65536),('rod_capacity','128*9*125',144000),
           ('wrap_after_full_buffer','16-16*floor(16/16)',0)]
    checks=[]
    for name,expression,expected in cases:
        result=client.calculate(expression)
        actual=evaluation_number(result['evaluation'])
        if actual!=expected: raise ArithmeticError('Provider buffer arithmetic mismatch: '+name)
        preview=result.get('modelPreview')
        if not isinstance(preview,dict) or not isinstance(preview.get('frameFingerprint'),str):
            raise ValueError('Provider model preview unavailable')
        checks.append(dict(name=name,expression=expression,expected=expected,actual=str(actual),
                           model_preview=scrub(preview,(client.token,)),
                           request_id=result.get('telemetry',{}).get('requestId')))
    return dict(backend='calculator-model-preview+local-durable-duplex',
                provider_model_available=True,provider_shared_buffers=False,model_id=MODEL_ID,
                checks=checks,observed_at=time.time())


class Peer:
    def __init__(self,client,node,folder,peers=(),provider=True):
        if any(not re.fullmatch(r'[A-Za-z0-9_.-]{1,64}',p) or p in ('.','..') for p in (node,*peers)):
            raise ValueError('Invalid buffer peer ID')
        self.client,self.node,self.folder,self.peers=client,node,Path(folder),tuple(peers)
        self._provider=provider
        self.folder.mkdir(parents=True,exist_ok=True); self.last_tick=-float('inf'); self.provenance=None

    def initialize(self):
        if self.provenance is None:
            try: self.provenance=model_with_provider() if self.provider_enabled else None
            except Exception as error:
                self.provenance=dict(backend='local-exact-fallback',provider_model_available=False,
                                     reason=type(error).__name__,model_id=MODEL_ID)
            if self.provenance is None:
                self.provenance=dict(backend='local-exact',provider_model_available=False,model_id=MODEL_ID)
            atomic_json(self.folder/'model.json',self.provenance)
        reply=self.client.call('model.publish',model=MODEL,provenance=self.provenance)
        if reply['node_id']!=self.node: raise ValueError('BTC_NODE_ID does not match authenticated node identity')

    @property
    def provider_enabled(self): return getattr(self,'_provider',True)

    def tick(self,status):
        if time.monotonic()-self.last_tick<1: return
        self.last_tick=time.monotonic()
        for other in self.peers:
            payload=canonical(dict(type='mining-node-status',node_id=self.node,**status)).encode()
            try:
                self.client.call('buffer.send',receiver=other,model_id=MODEL_ID,
                                 payload=base64.b64encode(payload).decode())
            except Rejected as error:
                if str(error) not in ('no_credit','peer_model_unavailable'): raise
            batch=self.client.call('buffer.read',sender=other,after=0)
            for frame in batch['frames']:
                raw=base64.b64decode(frame['payload'],validate=True)
                if frame['model_id']!=MODEL_ID or hashlib.sha256(raw).hexdigest()!=frame['digest']:
                    raise ValueError('Received frame integrity/model mismatch')
                if frame['sender']!=other or frame['receiver']!=self.node or frame['geometry']!=frame_geometry(other,self.node,frame['sequence'],len(raw)):
                    raise ValueError('Received frame lane/geometry mismatch')
                # Preserve immutable received frames before releasing receiver pin.
                path=self.folder/'received'/other/(str(frame['sequence'])+'.json')
                if path.exists() and json.loads(path.read_text())!=frame:
                    raise ValueError('Received frame changed under same sequence')
                atomic_json(path,frame)
                self.client.call('buffer.ack',sender=other,sequence=frame['sequence'])
