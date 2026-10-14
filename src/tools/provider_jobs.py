"""Isolated remote candidate qualification; never starts mining or submits blocks.

Job/revision/target identity, cancellation, bounded retry and independent local
verification guard the two-call provider hash adapter. Each worker owns its
client; checks are serialized so request timeout state is never shared. A
successful candidate remains distinct from an accepted network block.
"""
from dataclasses import dataclass
import hashlib
import math
import struct
import threading
import time
from .provider import ProviderError, hash_header


class JobAborted(ProviderError):
    def __init__(self, reason):
        self.reason=reason
        super().__init__('Remote candidate aborted: '+reason)


@dataclass(frozen=True)
class HashJob:
    header: bytes
    target: int
    revision: str
    identity: str


class RemoteCandidateWorker:
    """One explicitly supplied candidate per check; no hidden nonce search."""
    def __init__(self, client, clock=time.monotonic):
        self.client=client;self.clock=clock;self.job=None
        self.lock=threading.RLock();self.compute_lock=threading.Lock();self.cache={}
        self.counters=dict(request_attempts=0,transient_failures=0,retries=0,
            completed_candidates=0,cache_hits=0,stale=0,cancelled=0,deadline=0)

    def bind(self, header, target, revision):
        if not isinstance(header,bytes) or len(header)!=80:
            raise ValueError('An 80-byte header is required')
        if type(target) is not int or not 0<=target<1<<256:
            raise ValueError('Target must be an exact uint256 integer')
        if not isinstance(revision,str) or not revision:
            raise ValueError('A nonempty work revision is required')
        identity=hashlib.sha256(header[:76]+target.to_bytes(32,'little')+revision.encode()).hexdigest()
        with self.lock:
            if self.job is None or self.job.identity!=identity:
                self.job=HashJob(header,target,revision,identity);self.cache={}
            return self.job

    def check(self, nonce, *, seconds=5, retries=1, cancelled=None):
        if type(nonce) is not int or not 0<=nonce<1<<32:
            raise ValueError('Nonce must be a uint32 integer')
        if type(seconds) not in (int,float) or not math.isfinite(seconds) or not 0<seconds<=60:
            raise ValueError('Deadline must be within 0..60 seconds')
        if type(retries) is not int or not 0<=retries<=3:
            raise ValueError('Retry count must be within 0..3')
        # Capture before waiting: a queued check cannot accidentally migrate to
        # a newer job. The caller must explicitly request it under that job.
        with self.lock:job=self.job
        if job is None:raise ValueError('Bind a job before checking candidates')
        deadline=self.clock()+seconds
        def guard():
            with self.lock:
                reason=('stale' if self.job is not job else
                        'cancelled' if cancelled and cancelled() else
                        'deadline' if self.clock()>=deadline else None)
                if reason:
                    self.counters[reason]+=1
                    raise JobAborted(reason)
        with self.compute_lock:
            guard()
            with self.lock:
                if nonce in self.cache:
                    self.counters['cache_hits']+=1
                    return dict(self.cache[nonce],cached=True)
            owner=self
            class GuardedClient:
                def request(self,*args,**kwargs):
                    guard()
                    previous=owner.client.timeout
                    owner.client.timeout=min(previous,max(.001,deadline-owner.clock()))
                    with owner.lock:owner.counters['request_attempts']+=1
                    try:response=owner.client.request(*args,**kwargs)
                    finally:owner.client.timeout=previous
                    guard()
                    return response
            header=job.header[:76]+struct.pack('<I',nonce)
            for attempt in range(retries+1):
                try:result=hash_header(GuardedClient(),header,'compare')
                except JobAborted:raise
                except ProviderError as error:
                    guard()
                    transient=(error.status in (408,429,500,502,503,504) or
                               (error.status is None and str(error).startswith('Provider transport failed:')))
                    with self.lock:
                        if transient:self.counters['transient_failures']+=1
                    if not transient or attempt==retries:raise
                    with self.lock:self.counters['retries']+=1
                    continue
                break
            if not result['ok']:
                raise ProviderError('Remote candidate failed independent SHA256d validation')
            guard()
            value=int.from_bytes(bytes.fromhex(result['digest_hex']),'little')
            qualified=dict(job_id=job.identity,revision=job.revision,nonce=nonce,
                target=str(job.target),hash_hex=result['hash_hex'],digest_hex=result['digest_hex'],
                meets_target=value<=job.target,independently_verified=True,cached=False,
                accepted_block=False,submitted=False)
            with self.lock:
                guard()
                if len(self.cache)>=128:self.cache.pop(next(iter(self.cache)))
                self.cache[nonce]=qualified;self.counters['completed_candidates']+=1
            return dict(qualified)
