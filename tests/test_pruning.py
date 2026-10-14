import hashlib
import importlib.util
import json
import struct
import unittest
from unittest.mock import patch

from btcminer.diagnostics import GENESIS
from btcminer.pruning import Pruner,MODEL
from btcminer.protocol import Work
from btcminer.settings import DEFAULTS


class PruningBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.p=Pruner(DEFAULTS);self.addCleanup(self.p.close)
        self.work=Work(GENESIS,123,123,0,'1d00ffff','test',1)

    def response(self,r,keep):
        key=hashlib.sha256(json.dumps([r['header'],r['target'],r['nonces']],separators=(',',':')).encode()).hexdigest()
        return {'model':MODEL,'key':key,'keep':keep,'excluded':len(r['nonces'])-len(keep),'unknown':False}

    def test_timeout_does_not_remove_candidates(self):
        task={'nonces':[1,2,3]}
        with patch.object(self.p,'query',side_effect=TimeoutError('bounded')):
            self.assertIs(self.p.filter_task(self.work,task),task)
        self.assertEqual(self.p.state['candidates_excluded'],0)

    def test_wrong_model_wrong_job_and_malformed_response_do_not_prune(self):
        task={'nonces':[1,2,3]}
        for reply in ({'model':'toy','keep':[]},{'model':MODEL,'key':'old-job','keep':[]},None,[]):
            self.p.last_job=None
            with patch.object(self.p,'query',return_value=reply):
                self.assertIs(self.p.filter_task(self.work,task),task)
        self.assertEqual(self.p.state['candidates_excluded'],0)

    def test_partial_unknown_keeps_unresolved_tail_and_order(self):
        task={'nonces':list(range(20))}
        def reply(r):
            result=self.response(r,r['nonces'][1:]);result['unknown']=True;return result
        with patch.object(self.p,'query',side_effect=reply) as query:
            self.assertEqual(self.p.filter_task(self.work,task),{'nonces':list(range(1,20))})
            self.assertIs(self.p.filter_task(self.work,task),task)
            self.assertEqual(query.call_count,1)
            self.work.target+=1
            self.p.filter_task(self.work,task)
            self.assertEqual(query.call_count,2)
        self.assertEqual(self.p.state['unknown_jobs'],2)

    def test_linear_wraparound_filter_preserves_unchecked_values(self):
        with patch.object(self.p,'query',side_effect=lambda r:self.response(r,r['nonces'][1:])):
            self.assertEqual(self.p.filter_task(self.work,{'start':0xfffffffe,'count':4}),{'nonces':[0xffffffff,0,1]})


@unittest.skipUnless(importlib.util.find_spec('z3'),'optional Z3 environment required')
class FullSHAConstraintTests(unittest.TestCase):
    def test_complete_symbolic_hash_matches_hashlib_fixed_inputs(self):
        from btcminer.constraintmodel import bitcoin_model,z3
        for header,n in ((GENESIS,2083236893),(GENESIS,0),(bytes(80),0xffffffff),(bytes(range(80)),17)):
            solver=z3.Then('simplify','propagate-values','solve-eqs','simplify','smt').solver()
            solver.set(timeout=3000,max_memory=256)
            nonce,value,_=bitcoin_model(header,solver)
            data=header[:76]+struct.pack('<I',n)
            expected=int.from_bytes(hashlib.sha256(hashlib.sha256(data).digest()).digest(),'little')
            solver.add(nonce==n,value!=z3.BitVecVal(expected,256))
            self.assertEqual(solver.check(),z3.unsat)

    def test_genesis_winner_survives_and_exclusions_are_sound(self):
        from btcminer.pruning_worker import evaluate
        nonce=struct.unpack_from('<I',GENESIS,76)[0]
        target=int.from_bytes(hashlib.sha256(hashlib.sha256(GENESIS).digest()).digest(),'little')
        row=evaluate({'model':MODEL,'header':GENESIS.hex(),'target':str(target),
                      'nonces':[nonce-1,nonce,nonce+1],'budget_ms':2000})
        self.assertIn(nonce,row['keep'])
        removed=set([nonce-1,nonce,nonce+1])-set(row['keep'])
        self.assertEqual(row['excluded'],len(removed))
        for candidate in removed:
            data=GENESIS[:76]+struct.pack('<I',candidate)
            value=int.from_bytes(hashlib.sha256(hashlib.sha256(data).digest()).digest(),'little')
            self.assertGreater(value,target)
        # The wall-clock budget includes model construction. A busy host may
        # retain a loser; that is the required fail-safe result, not a failure.
        if not row['unknown']:
            self.assertEqual(row['keep'],[nonce])
            self.assertEqual(row['excluded'],2)

    def test_tiny_budget_retains_unknowns(self):
        from btcminer.pruning_worker import evaluate
        row=evaluate({'model':MODEL,'header':GENESIS.hex(),'target':'0',
                      'nonces':[0,1,2],'budget_ms':1})
        self.assertTrue(row['unknown'])
        self.assertEqual(row['keep'],[0,1,2])


if __name__=='__main__':unittest.main()
