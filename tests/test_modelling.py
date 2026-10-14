import tempfile
import time
import unittest
from array import array
from pathlib import Path

from btcminer.diagnostics import GENESIS
from btcminer.native import Hasher
from btcminer.modelling import (Lab,Lane,DEFAULT,MAX_HASH,GX,GY,P,
    validate_control,target_for,tower_probe,independent_nonces)
from btcminer.thesis2 import Traversal


def until(check,seconds=5):
    deadline=time.monotonic()+seconds
    while time.monotonic()<deadline:
        value=check()
        if value:return value
        time.sleep(.02)
    raise AssertionError('Condition did not become true')


class ModellingTests(unittest.TestCase):
    def test_fixed_g_and_exact_targets(self):
        self.assertEqual((GY*GY-GX**3-7)%P,0)
        self.assertEqual(target_for(0),MAX_HASH)
        self.assertEqual(target_for(256),0)
        self.assertEqual(target_for(18)+1,1<<238)
        self.assertEqual(target_for(0,123),123)

    def test_controls_reject_ambiguous_or_unbounded_values(self):
        for change in ({'bits':True},{'bits':1.5},{'bits':257},{'depths':[8,2]},
                       {'depths':[8,-1,3]},{'depths':[8,2,True]},{'mode':'mainnet'},
                       {'rpc_host':'elsewhere'},{'sweep_seconds':0}):
            with self.subTest(change=change),self.assertRaises(ValueError):validate_control(DEFAULT,change)

    def test_tower_fails_closed_and_recovers_without_changing_offset(self):
        for order in ('field','flower'):
            plan=Traversal(GENESIS,order=order)
            plain=tower_probe(plan,DEFAULT)
            self.assertEqual(plain['status'],'exact')
            low=tower_probe(plan,dict(DEFAULT,depths=[7,2,3]))
            self.assertEqual(low['status'],'capacity_limit');self.assertIsNone(low['readback'])
            high=tower_probe(plan,dict(DEFAULT,depths=[64,16,16],lift_bits=32,scale_power=10))
            self.assertEqual(high['status'],'exact');self.assertEqual(high['offset'],plain['offset'])
            self.assertEqual(int(high['readback'])%144000,plain['offset'])

    def test_partial_winner_keeps_all_unscanned_candidates(self):
        h=Hasher()
        for order in ('field','flower'):
            lane=Lane(GENESIS,order,h);values=lane.take();first=int(values[0])
            tried,winner=h.scan(GENESIS,MAX_HASH,nonces=values)
            self.assertEqual((tried,winner),(1,first))
            lane.record(tried,winner,values,GENESIS,MAX_HASH)
            suffix=lane.take();self.assertEqual(list(suffix),list(values[1:]))
            tried,winner=h.scan(GENESIS,0,nonces=suffix)
            self.assertIsNone(winner)
            lane.record(tried,winner,suffix,GENESIS,0)
            self.assertEqual(lane.hashes,len(values));self.assertEqual(lane.generated,lane.hashes)

    def test_native_corruption_and_false_result_are_detected(self):
        lane=Lane(GENESIS,'flower',Hasher());values=lane.take()
        with self.assertRaises(ArithmeticError):lane.record(len(values),None,values,GENESIS,MAX_HASH)
        lane=Lane(GENESIS,'field',Hasher());lane.batches=iter([{'nonces':array('I',[42,42])}])
        with self.assertRaises(ArithmeticError):lane.take()

    def test_reference_boundary_never_wraps_nonce_space(self):
        plan=Traversal(GENESIS,order='flower');plan.first_tile=29826
        values,cursor=independent_nonces(plan,0,144000)
        self.assertEqual(len(values),144000);self.assertEqual(len(set(values)),144000)
        self.assertTrue(all(0<=x<2**32 for x in values))
        self.assertGreater(cursor,144000)
        values,cursor=independent_nonces(plan,29827*144000-3,100)
        self.assertEqual(cursor,29827*144000);self.assertLessEqual(len(values),3)

    def test_live_controls_preserve_job_and_pause_at_capacity_limit(self):
        with tempfile.TemporaryDirectory() as tmp:
            lab=Lab(Path(tmp))
            try:
                lab.command('start')
                s=until(lambda:(s if s['hashes']>16000 else None) if (s:=lab.snapshot()) else None)
                job=s['job_id'];before=s['hashes']
                lab.command('configure',{'bits':64})
                s=until(lambda:(s if s['applied_revision']==1 else None) if (s:=lab.snapshot()) else None)
                self.assertEqual(s['job_id'],job);self.assertGreaterEqual(s['hashes'],before)
                lab.command('configure',{'depths':[7,2,3]})
                s=until(lambda:(s if s['state']=='CAPACITY LIMIT' else None) if (s:=lab.snapshot()) else None)
                frozen=s['hashes'];time.sleep(.12);self.assertEqual(lab.snapshot()['hashes'],frozen)
                lab.command('configure',{'depths':[8,2,3]})
                until(lambda:lab.snapshot()['hashes']>frozen)
                lab.command('pause');frozen=lab.snapshot()['hashes'];time.sleep(.08)
                self.assertEqual(lab.snapshot()['hashes'],frozen)
                self.assertEqual(lab.snapshot()['job_id'],job)
                self.assertIn('capacity',lab.snapshot()['first_limits'])
                s=lab.snapshot()
                self.assertEqual(sum(l['hashes'] for l in s['lanes'].values()),s['hashes'])
                lab.command('reset');s=lab.snapshot()
                self.assertEqual(s['hashes'],0);self.assertIsNone(s['job_id'])
                self.assertEqual(sum(l['hashes'] for l in s['lanes'].values()),0)
            finally:lab.close()

    def test_sweep_reaches_and_holds_final_target(self):
        with tempfile.TemporaryDirectory() as tmp:
            lab=Lab(tmp)
            try:
                lab.command('configure',{'bits':60,'sweep_end':62,'sweep_step':1,'sweep_seconds':1})
                lab.command('sweep')
                s=until(lambda:(s if not s['sweep'] and s['controls']['bits']==62 else None) if (s:=lab.snapshot()) else None,8)
                self.assertEqual(s['target_hex'],f'{target_for(62):064x}')
                self.assertEqual([x['bits'] for x in s['events'] if x['kind']=='sweep_step'],[60,61,62])
                self.assertEqual(s['state'],'RUNNING')
            finally:lab.close()

    def test_waiting_and_performance_limits_are_not_math_failures(self):
        with tempfile.TemporaryDirectory() as tmp:
            lab=Lab(tmp)
            try:
                lab.command('configure',{'bits':256,'wait_limit':1,'min_rate':1000000000})
                lab.command('start')
                s=until(lambda:(s if {'waiting','performance'}<=set(s['first_limits']) else None) if (s:=lab.snapshot()) else None,8)
                self.assertEqual(s['state'],'RUNNING');self.assertEqual(s['error'],'')
                self.assertEqual(len(s['warnings']),2)
                self.assertEqual(s['scale']['status'],'exact')
            finally:lab.close()


if __name__=='__main__':unittest.main()
