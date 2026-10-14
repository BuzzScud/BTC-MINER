"""Worker pulls an exact region, scans a bounded prefix, commits before moving."""
import threading
import time

from ..native import Hasher
from .geometry import Geometry, implementation
from .store import Rejected
from .transport import TransportError


class Worker:
    def __init__(self,client,*,hasher=None,batch_size=16384,stop=None,cpu_duty=100,peer=None,admission=None):
        if type(batch_size) is not int or not 1<=batch_size<=1000000: raise ValueError('Invalid batch size')
        if not 1<=cpu_duty<=100: raise ValueError('Invalid CPU duty')
        self.client=client; self.hasher=hasher or Hasher(); self.batch_size=batch_size
        self.stop=stop or threading.Event(); self.geometry=None; self.job=None; self.cpu_duty=cpu_duty
        self.peer=peer
        self.admission=admission
        self.assignment=None;self.checked_at=0

    def release(self):
        """Recover an ambiguous request before releasing its current lease."""
        if self.assignment is None:return
        if hasattr(self.client,'recover'):self.client.recover()
        assignment=self.assignment
        try:self.client.call('release',job=assignment['job'],region=assignment['region'],epoch=assignment['epoch'])
        except Rejected as error:
            if str(error) not in ('stale_job','stale_lease','progress_conflict'):raise
        self.assignment=None

    def step(self):
        try: return self._step()
        except Rejected:
            self.assignment=None
            raise

    def _step(self):
        duty=self.cpu_duty
        if self.admission:
            permitted,limit=self.admission();duty=min(duty,limit)
            if not permitted:self.release();return False
        if self.stop.is_set(): self.release();return False
        began=time.monotonic()
        assignment = self.assignment
        if assignment is None:
            assignment = self.client.call('claim',implementation=implementation())['assignment']
            self.checked_at=0
        if assignment is None: return False
        job = assignment['job']
        if self.job != job:
            self.geometry=Geometry.from_spec(assignment['spec']); self.job=job
        geometry=self.geometry
        binding=dict(job=job,region=assignment['region'],epoch=assignment['epoch'])
        # A replayed claim is historical. Check current ownership before hashing.
        if time.monotonic()-self.checked_at>=assignment['lease_seconds']/3:
            self.client.call('heartbeat',**binding)
            self.checked_at=time.monotonic()
        if self.stop.is_set():
            self.client.call('release',**binding); return False
        start=assignment['start']; stop=assignment['stop']
        values,end=geometry.batch(self.hasher,start,stop,self.batch_size)
        scan_began=time.monotonic()
        tried,nonce=(self.hasher.scan(bytes.fromhex(assignment['spec']['header']),
                int(assignment['spec']['target']),nonces=values,stop=self.stop.is_set)
                if values else (0,None))
        if not 0<=tried<=len(values) or (nonce is not None and (tried==0 or values[tried-1]!=nonce)):
            raise ArithmeticError('Hasher returned invalid prefix')
        if tried<len(values): end=geometry.raw_index(values[tried-1])+1 if tried else start
        elapsed=time.monotonic()-scan_began
        if end>start:
            self.client.call('commit',**binding,start=start,cursor=end,hashes=tried,
                             hits=[] if nonce is None else [nonce],seconds=elapsed)
            self.checked_at=time.monotonic()
        self.assignment=dict(assignment,start=end) if end<stop else None
        if self.stop.is_set() and end<stop:
            self.client.call('release',**binding)
        if duty<100: self.stop.wait(min(2,(time.monotonic()-began)*(100/duty-1)))
        return True

    def run(self):
        initialized=False
        while not self.stop.is_set():
            try:
                if self.admission and not self.admission()[0]:
                    self.release();self.stop.wait(.2);continue
                if hasattr(self.client,'recover'): self.client.recover()
                if self.peer:
                    if not initialized: self.peer.initialize(); initialized=True
                    self.peer.tick(dict(job=self.job,state='ready'))
                if not self.step(): self.stop.wait(.2)
            except Rejected as error:
                if str(error) not in ('stale_job','stale_lease','progress_conflict'): raise
                self.stop.wait(.1)
            except TransportError:
                # A replay may have committed progress. Reclaim its current
                # cursor after recovering the pending request, never the old one.
                self.assignment=None
                self.stop.wait(1)
        try:self.release()
        except (Rejected,TransportError):pass  # Expiry/recovery retains uncommitted work.
