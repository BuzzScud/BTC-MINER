"""Independent boundary/control checks for the opt-in candidate adapter."""
import hashlib
import unittest
from btcminer import tcmp
from btcminer.provider import ProviderError
from btcminer.provider_jobs import RemoteCandidateWorker, JobAborted
from btcminer.diagnostics import GENESIS


class Client:
    timeout=3
    def __init__(self):self.inputs=[];self.callback=None;self.failures=[]
    def request(self,method,path,*,data,headers):
        self.inputs.append(data)
        if self.callback:self.callback()
        if self.failures:
            error=self.failures.pop(0)
            if error:raise error
        frame=tcmp.encode(data)
        return {'x-compression-codec':'coprime','x-original-size':str(len(data)),
                'x-compressed-size':str(len(frame)),
                'x-original-sha256':hashlib.sha256(data).hexdigest()},frame


class JobTests(unittest.TestCase):
    def setUp(self):
        self.client=Client();self.worker=RemoteCandidateWorker(self.client)
        self.nonce=int.from_bytes(GENESIS[76:],'little')
    def test_independent_candidate_comparison_at_target_boundaries(self):
        value=int.from_bytes(hashlib.sha256(hashlib.sha256(GENESIS).digest()).digest(),'little')
        for target in (0,value-1,value,value+1,(1<<256)-1):
            self.worker.bind(GENESIS,target,'work')
            result=self.worker.check(self.nonce)
            self.assertEqual(result['meets_target'],value<=target)
            self.assertTrue(result['independently_verified']);self.assertFalse(result['accepted_block'])
            self.assertFalse(result['submitted'])
    def test_exact_repeated_candidate_is_idempotent_in_same_job(self):
        self.worker.bind(GENESIS,1,'work')
        first=self.worker.check(0);second=self.worker.check(0)
        self.assertTrue(second['cached']);self.assertEqual(first['hash_hex'],second['hash_hex'])
        self.assertEqual(len(self.client.inputs),2)
        self.assertEqual(self.worker.counters['completed_candidates'],1)
    def test_stale_job_between_remote_stages_is_discarded(self):
        self.worker.bind(GENESIS,1,'old')
        self.client.callback=lambda:self.worker.bind(GENESIS,1,'new')
        with self.assertRaises(JobAborted) as caught:self.worker.check(0)
        self.assertEqual(caught.exception.reason,'stale')
        self.assertEqual(len(self.client.inputs),1)
        self.assertEqual(self.worker.counters['completed_candidates'],0)
    def test_cancellation_before_or_during_request_never_qualifies(self):
        self.worker.bind(GENESIS,1,'work')
        with self.assertRaises(JobAborted):self.worker.check(0,cancelled=lambda:True)
        self.assertEqual(len(self.client.inputs),0)
        stop=[False];self.client.callback=lambda:stop.__setitem__(0,True)
        with self.assertRaises(JobAborted):self.worker.check(0,cancelled=lambda:stop[0])
        self.assertEqual(len(self.client.inputs),1)
    def test_deadline_bounds_transport_and_discards_late_response(self):
        clock=[0.0];self.worker.clock=lambda:clock[0]
        self.worker.bind(GENESIS,1,'work')
        def delayed():
            self.assertLessEqual(self.client.timeout,.5);clock[0]=1
        self.client.callback=delayed
        with self.assertRaises(JobAborted) as caught:self.worker.check(0,seconds=.5)
        self.assertEqual(caught.exception.reason,'deadline');self.assertEqual(self.client.timeout,3)
        self.assertEqual(len(self.client.inputs),1)
    def test_transient_retry_counts_requests_once_per_attempt_not_candidate(self):
        self.worker.bind(GENESIS,1,'work')
        self.client.failures=[ProviderError('Provider transport failed: TimeoutError')]
        result=self.worker.check(0,retries=1)
        self.assertTrue(result['independently_verified'])
        self.assertEqual(self.worker.counters['request_attempts'],3)
        self.assertEqual(self.worker.counters['completed_candidates'],1)
        self.assertEqual(self.worker.counters['retries'],1)
    def test_permanent_and_integrity_failures_are_not_retried(self):
        self.worker.bind(GENESIS,1,'work')
        for error in (ProviderError('Provider HTTP 401',401),ProviderError('Provider hash response is bound to different input bytes')):
            self.client.inputs=[];self.client.failures=[error]
            with self.assertRaises(ProviderError):self.worker.check(0,retries=3)
            self.assertEqual(len(self.client.inputs),1)
    def test_exhausted_transient_failure_counts_last_attempt(self):
        self.worker.bind(GENESIS,1,'work')
        self.client.failures=[ProviderError('Provider HTTP 503',503)]*3
        with self.assertRaises(ProviderError):self.worker.check(0,retries=2)
        self.assertEqual(self.worker.counters['transient_failures'],3)
        self.assertEqual(self.worker.counters['retries'],2)
        self.assertEqual(self.worker.counters['request_attempts'],3)
        self.assertEqual(self.worker.counters['completed_candidates'],0)
    def test_new_job_after_second_stage_cannot_enter_cache(self):
        self.worker.bind(GENESIS,1,'work');calls=[0]
        def after_second():
            calls[0]+=1
            if calls[0]==2:self.worker.bind(GENESIS,2,'new')
        self.client.callback=after_second
        with self.assertRaises(JobAborted):self.worker.check(0)
        self.assertEqual(self.worker.cache,{})
    def test_untrusted_winner_cannot_pass_independent_validation(self):
        self.worker.bind(GENESIS,(1<<256)-1,'work')
        original=self.client.request
        def fake(*args,**kwargs):
            headers,frame=original(*args,**kwargs);headers['x-original-sha256']='00'*32;return headers,frame
        self.client.request=fake
        with self.assertRaisesRegex(ProviderError,'independent'):self.worker.check(0)
        self.assertEqual(self.worker.counters['completed_candidates'],0)
    def test_nonce_extremes_and_revision_target_binding(self):
        first=self.worker.bind(GENESIS,1,'work').identity
        for nonce in (0,1,2**32-1):
            self.worker.check(nonce);self.assertEqual(self.client.inputs[-2][76:],nonce.to_bytes(4,'little'))
        self.assertNotEqual(first,self.worker.bind(GENESIS,2,'work').identity)
        for nonce in (-1,True,2**32):
            with self.assertRaises(ValueError):self.worker.check(nonce)
        with self.assertRaises(ValueError):self.worker.bind(GENESIS,True,'work')

if __name__=='__main__':unittest.main()
