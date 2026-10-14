import importlib.util
import random
import time
import unittest
from collections import Counter
from unittest.mock import patch
from btcminer.scaled_abacus import PrecisionAbacus, q_codec, SCALES
from btcminer.priority import Priority
from btcminer.protocol import Work
from btcminer.diagnostics import GENESIS
from btcminer.recurrence import FLOWER, FIBONACCI, verify, native_verifier, Certificate


class ScaledIntegrationTests(unittest.TestCase):
    def test_priority_keeps_native_candidate_storage_packed(self):
        from array import array
        p=Priority();work=Work(GENESIS,123,123,0,'1d00ffff','test',1)
        values=array('I',range(100))
        result=p.order(work,{'nonces':values})['nonces']
        self.assertIsInstance(result,array)
        self.assertEqual(result.typecode,'I')
        self.assertEqual(Counter(result),Counter(values))
        self.assertEqual(values,array('I',range(100)))

    def test_precision_carry_sign_growth_and_reuse(self):
        rng = random.Random(4049); a = PrecisionAbacus(8)
        for bits in (8, 33, 4097, 8192, 16384, 65536):
            x = rng.getrandbits(bits) | 1 << (bits-1)
            y = rng.getrandbits(bits//2)
            for left, right in ((x,y),(-x,y),(x,-y),(-x,-y),(0,-y),(x,-x)):
                self.assertEqual(a.calculate('add',left,right),left+right)
                self.assertEqual(a.calculate('multiply',left,right),left*right)
            self.assertEqual(a.load(x).value(),x)
        old = a.value(); a.reserve(100000)
        self.assertEqual(a.value(),old)
        identity = id(a.model); readings = id(a.readings)
        a.clear(); self.assertEqual(a.value(),0)
        self.assertEqual(a.load(-19).value(),-19)
        self.assertEqual((id(a.model),id(a.readings)),(identity,readings))

    def test_all_scaled_q_roundtrips_and_collisions(self):
        for scale, count in zip(SCALES,(703,4371,15051)):
            c=q_codec(scale); self.assertEqual(len(c.values),count)
            values=list(reversed(c.values)); packed,n=c.pack(values)
            self.assertEqual(c.unpack(packed,n),values)
            self.assertEqual(len(packed),(n*c.bits+7)//8)
            for value in values:
                coordinates=c.coordinates(value)
                self.assertEqual(c.from_coordinates(coordinates['k'],coordinates['index']),value)
            self.assertIs(c,q_codec(scale))
            self.assertIsNone(c.code(0)); self.assertIsNone(c.code(1<<4097))
            with self.assertRaises(ValueError):c.pack([0])
            with self.assertRaises(ValueError):c.unpack(packed[:-1],n)
        c=q_codec(); self.assertEqual(c.coordinates(10)['k'],c.coordinates(15)['k'])
        self.assertNotEqual(c.coordinates(10)['index'],c.coordinates(15)['index'])

    def test_priority_retains_arithmetic_rejects_duplicates_and_wraparound(self):
        p=Priority(64); work=Work(GENESIS,123,123,0,'1d00ffff','test',1)
        for values in (list(range(100)),[2,3,5,10,15,19,19,30,210,0],list(range(2**32-64,2**32))):
            task={'nonces':values}; actual=p.order(work,task)
            self.assertEqual(Counter(actual['nonces']),Counter(values))
            self.assertEqual(actual['nonces'][64:],values[64:])
            p.observe(actual,min(10,len(values)),actual['nonces'][:1])
        self.assertEqual(p.description()['excluded'],0)
        actual=p.order(work,{'start':2**32-3,'count':6})
        values=actual.get('nonces',[(2**32-3+i)&0xffffffff for i in range(6)])
        self.assertEqual(Counter(values),Counter([2**32-3,2**32-2,2**32-1,0,1,2]))

    def test_recurrence_scope_and_invalid_certificates(self):
        for c in (FLOWER,FIBONACCI):
            r=verify(c); self.assertTrue(r['valid']);self.assertEqual(r['bitcoin_nonce_exclusions'],0)
            if native_verifier():self.assertEqual(r['native_result'],1)
        for mutation in ({'e':1},{'L':0},{'Q':0},{'bpow':0},{'rods':(0,)},
                         {'rods':(5,5)},{'coord':2},{'starts':()}, {'Q':1000000},
                         {'F':((1,0),(0,1)), 'starts':((0,32),)}):
            self.assertFalse(verify({**FLOWER,**mutation})['valid'],mutation)

    def test_c_guard_rejects_malformed_certificate_directly(self):
        import ctypes as C
        fn=native_verifier()
        if fn is None:self.skipTest('Optional guarded C library unavailable')
        matrix=((C.c_int64*2)*2)(*( (C.c_int64*2)(*r) for r in FLOWER['F']))
        starts=((C.c_int64*2)*2)(*( (C.c_int64*2)(*r) for r in FLOWER['starts']))
        for field,value in (('e',1),('L',0),('Q',0),('bpow',0),('nrods',33),('Q',2**63)):
            c=Certificate(2,5,32,3,(C.c_uint32*32)(5,7,31),32,60)
            setattr(c,field,value)
            self.assertLess(fn(C.byref(c),matrix,starts,2,1),0)


@unittest.skipUnless(importlib.util.find_spec('z3'),'Optional Z3 environment required')
class AdaptiveTests(unittest.TestCase):
    def test_adaptive_completed_bucket_matches_exhaustive_oracle(self):
        import z3
        from btcminer.adaptive import retain_candidates
        n=z3.BitVec('nonce',8); solver=z3.Solver()
        solver.add((n*3+7)&15==2)
        # This checks a completed exhaustive result, not host scheduling speed.
        # The separate unknown test exercises the conservative timeout path.
        result=retain_candidates(solver,n,list(range(256)),time.monotonic()+30,slice_ms=10000)
        self.assertEqual(result['keep'],[v for v in range(256) if (v*3+7)&15==2])
        self.assertFalse(result['unknown'])

    def test_adaptive_unknown_keeps_everything_and_splits(self):
        import z3
        from btcminer.adaptive import retain_candidates
        n=z3.BitVec('nonce',8); solver=z3.Solver()
        with patch.object(solver,'check',return_value=z3.unknown):
            result=retain_candidates(solver,n,list(range(32)),time.monotonic()+1)
        self.assertEqual(result['keep'],list(range(32)))
        self.assertTrue(result['unknown']);self.assertGreater(result['adaptive_splits'],0)

    def test_integrated_toy_keeps_all_winners(self):
        from btcminer.abacus_lab import toy_check
        r=toy_check(width=8,rounds=8,nonce_bits=8,difficulty=4,budget_ms=2000)
        self.assertTrue(r['ok']);self.assertEqual(r['lost_winners'],[])
        self.assertEqual(r['concrete_hashes_during_pruning'],0)
        self.assertEqual(r['exhaustive_validation_hashes'],256)

    def test_packed_worker_request_matches_raw_request(self):
        from btcminer.pruning_worker import evaluate, request_key
        from btcminer.pruning import MODEL
        values=[6,10,14,15,21,22,33]
        codec=q_codec(); data,count=codec.pack(values)
        request={'model':MODEL,'header':GENESIS.hex(),'target':str((1<<256)-1),'budget_ms':1,
                 'nonce_codes':{'M':codec.modulus,'data':data.hex(),'count':count}}
        result=evaluate(request)
        self.assertEqual(result['keep'],values)
        self.assertEqual(result['key'],request_key(GENESIS.hex(),(1<<256)-1,values))
        with self.assertRaises(ValueError):evaluate(dict(request,nonces=values))

    def test_live_worker_transport_compresses_only_when_smaller(self):
        from btcminer.pruning import Pruner
        from btcminer.settings import DEFAULTS
        values=[n for n in q_codec().values if n<1<<32][-64:]
        p=Pruner(dict(DEFAULTS,pruning_candidates=64,pruning_budget_ms=1))
        self.addCleanup(p.close)
        work=Work(GENESIS,(1<<256)-1,(1<<256)-1,0,'1d00ffff','encoded',1)
        result=p.filter_task(work,{'nonces':values})
        self.assertEqual(result['nonces'],values)
        self.assertEqual(p.description()['compressed_jobs'],1)
        self.assertGreater(p.description()['transport_bytes_saved'],0)


if __name__=='__main__':unittest.main()
