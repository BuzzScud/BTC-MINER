import base64
import itertools
from math import prod
import random
import unittest
from unittest.mock import Mock, patch
from btcminer.geometry_codec import (Bits, pack_fields, frames, encode_points, decode_points,
    compact_request, describe_points, transport_check, LIMIT)
from btcminer.geometry_predictive import (NAMES, shortest_arc, root_reference, gamma, read_gamma,
    shell_address, shell_value, shell_point, point_address, encode_counts, decode_counts, capability)
from btcminer.pruning import Pruner, MODEL
from btcminer.pruning_worker import evaluate, request_key
from btcminer.settings import DEFAULTS
from btcminer.protocol import Work
from btcminer.diagnostics import GENESIS


class PredictiveGeometryTests(unittest.TestCase):
    def test_shortest_arc_exhaustive_odd_even_and_antipodal_ties(self):
        for m in range(2,33):
            for a,b in itertools.product(range(m),repeat=2):
                d=shortest_arc(a,b,m)
                oracle=min((b-a+k*m for k in range(-2,3)),key=lambda x:(abs(x),x))
                self.assertEqual(d,oracle)
                self.assertEqual((a+d)%m,b)
        self.assertEqual(shortest_arc(0,4,8),-4)

    def test_root_anchor_ties_are_deterministic(self):
        for m in range(2,50):
            for r in range(m):
                index,d=root_reference(r,m)
                roots=(0,1,m-1)
                scores=[(min((r-root)%m,(root-r)%m),i) for i,root in enumerate(roots)]
                self.assertEqual((abs(d),index),min(scores))
                self.assertEqual((roots[index]+d)%m,r)

    def test_shells_bijection_counts_neighbors_and_exact_boundaries(self):
        points=set()
        for k in range(21):
            ring=[shell_point(k,j) for j in range(6*k if k else 1)]
            self.assertEqual(len(set(ring)),6*k if k else 1)
            for j,point in enumerate(ring):
                self.assertEqual(point_address(*point),(k,j))
                self.assertEqual(shell_address(shell_value(k,j)),(k,j))
                a,b=point;self.assertEqual(max(abs(a),abs(b),abs(a-b)),k)
                if k:
                    c,d=ring[(j+1)%len(ring)]
                    self.assertEqual(max(abs(a-c),abs(b-d),abs((a-c)-(b-d))),1)
            points.update(ring);self.assertEqual(len(points),1+3*k*(k+1))
        for k in [1,2,19,65536,1<<4096]:
            for j in [0,6*k-1]:self.assertEqual(shell_address(shell_value(k,j)),(k,j))
        for bad in [(0,1),(1,6),(-1,0),(2,-1)]:
            with self.assertRaises(ValueError):shell_value(*bad)

    def test_gamma_canonical_and_bounded(self):
        for value in range(256):
            data=pack_fields(gamma(value));bits=Bits(data)
            self.assertEqual(read_gamma(bits,255),value);bits.finish()
        with self.assertRaises(ValueError):read_gamma(Bits(b'\0'*20),127)

    def test_count_side_stream_uses_all_three_forms(self):
        rows=[[1,6,2,5,3,4]*10,[6]*64,[1]*16+[2]*16+[3]*16+[4]*16]
        modes=set()
        for values in rows:
            data=encode_counts(values);modes.add(data[0]&3)
            self.assertEqual(decode_counts(data,len(values)),values)
            for broken in [data+b'\0',data[:-1]]:
                with self.assertRaises(ValueError):decode_counts(broken,len(values))
        self.assertEqual(modes,{0,1,2})

    def test_all_new_modes_random_and_structured_roundtrips(self):
        rng=random.Random(19)
        cases=[[0],[LIMIT-1],[7]*64,list(range(64)),[0,LIMIT-1]*32]
        cases += [[rng.randrange(LIMIT) for _ in range(n)] for n in [1,2,8,32,64] for _ in range(10)]
        for mode,values in itertools.product(NAMES,cases):
            with self.subTest(mode=mode,size=len(values)):
                encoded=encode_points(values,mode)
                self.assertEqual(decode_points(encoded),values)
                info=describe_points(encoded);self.assertEqual(info['version'],2)
                self.assertEqual(info['symbolic_form'],mode)
                self.assertTrue(info['certificate_chain_ids'])

    def test_new_modes_reject_all_truncations_wrong_ids_and_trailing_data(self):
        for mode in NAMES:
            encoded=encode_points([0,7,3,90,199,23],mode);raw=base64.b64decode(encoded)
            for n in range(len(raw)):
                with self.assertRaises(ValueError):decode_points(base64.b64encode(raw[:n]).decode())
            for i,v in [(0,0),(3,99),(4,0),(4,65),(5,raw[5]^1)]:
                changed=bytearray(raw);changed[i]=v
                with self.assertRaises(ValueError):decode_points(base64.b64encode(changed).decode())
            with self.assertRaises(ValueError):decode_points(base64.b64encode(raw+b'\0').decode())

    def test_selection_is_negotiated_and_minimizes_complete_wire_size(self):
        rng=random.Random(71)
        values=[rng.randrange(60) for _ in range(64)]
        request={'model':MODEL,'header':GENESIS.hex(),'target':'0','nonces':values}
        old,oldstats=compact_request(request)
        new,stats=compact_request(request,allow_predictive=True)
        if 'nonce_geometry' in old:self.assertEqual(base64.b64decode(old['nonce_geometry'])[:3],b'NG1')
        self.assertLessEqual(stats['wire_bytes'],oldstats['wire_bytes'])
        report=transport_check();self.assertTrue(report['ok'])
        for row in report['cases']:
            costs=[n for n in row['mode_wire_bytes'].values() if n is not None]+[row['raw_wire_bytes']]
            self.assertEqual(row['wire_bytes'],min(costs))
        chosen={row['mode'] for row in report['cases']}
        self.assertTrue((set(NAMES)-{'root-offset'})<=chosen,chosen)
        roots=next(r for r in report['cases'] if r['case']=='anchor_clusters')
        self.assertLess(roots['mode_wire_bytes']['root-offset'],roots['mode_wire_bytes']['raw32'])

    def test_worker_advertises_and_parent_only_uses_confirmed_frame(self):
        p=Pruner(dict(DEFAULTS,pruning_candidates=64));self.addCleanup(p.close)
        process=Mock();process.poll.return_value=None;p.process=process
        process.stdin=None;process.stdout=None
        # Avoid launching/stopping anything; this is a mocked persistent peer.
        process.wait.return_value=0
        values=[0]*16+[300]*16+[20000]*16+[3000000000]*16
        work=Work(GENESIS,0,0,0,'1d00ffff','negotiation',1);task={'nonces':values}
        # Use unique values to pass the parent's independent duplicate gate.
        values=[3000000000+i*i for i in range(64)];task={'nonces':values}
        versions=[]
        def reply(request):
            versions.append(base64.b64decode(request['nonce_geometry'])[:3])
            with patch('btcminer.pruning_worker.z3',None):return evaluate(dict(request,geometry_offer=len(versions)==1))
        with patch.object(p,'query',side_effect=reply):
            self.assertIs(p.filter_task(work,task),task)
            self.assertTrue(p.geometry_v2)
            work.generation+=1;self.assertIs(p.filter_task(work,task),task)
        self.assertEqual(versions,[b'NG1',b'NG2'])
        self.assertEqual(p.state['transport_mode'],'adaptive-rods')
        process.poll.return_value=0

    def test_missing_or_wrong_capability_keeps_baseline(self):
        p=Pruner(DEFAULTS);self.addCleanup(p.close)
        work=Work(GENESIS,0,0,0,'1d00ffff','negotiation',1)
        for cap in [None,{},dict(capability(),version='NG3')]:
            def reply(r):
                return {'model':MODEL,'key':request_key(r['header'],0,r['nonces']),
                        'keep':r['nonces'],'excluded':0,'unknown':True,'geometry_capability':cap}
            with patch.object(p,'query',side_effect=reply):p.filter_task(work,{'nonces':[1,2,3]})
            self.assertFalse(p.geometry_v2);work.generation+=1


    def test_real_worker_negotiation_and_restart_downgrade(self):
        p=Pruner(dict(DEFAULTS,pruning_candidates=64,pruning_budget_ms=1));self.addCleanup(p.close)
        values=[3000000000+i*i for i in range(64)];task={'nonces':values}
        work=Work(GENESIS,LIMIT**8-1,LIMIT**8-1,0,'1d00ffff','negotiation-real',1)
        self.assertIs(p.filter_task(work,task),task)
        self.assertTrue(p.geometry_v2)
        self.assertEqual(p.state['transport_mode'],'residue')
        work.generation+=1
        self.assertIs(p.filter_task(work,task),task)
        self.assertEqual(p.state['transport_mode'],'adaptive-rods')
        response_bytes=p.state['capability_response_bytes']
        work.generation+=1
        self.assertIs(p.filter_task(work,task),task)
        self.assertEqual(p.state['capability_response_bytes'],response_bytes)
        self.assertEqual(p.state['transport_mode'],'adaptive-rods')
        self.assertEqual(p.description()['transport_net_bytes_saved'],p.state['transport_bytes_saved']-p.state['capability_request_bytes']-response_bytes)
        p.close()
        self.assertFalse(p.geometry_v2)
        # The peer dies after the selection poll, before query() writes it.
        dead=Mock();dead.poll.side_effect=[None,0,0];dead.stdin=None;dead.stdout=None
        p.process=dead;p.geometry_v2=True;work.generation+=1
        before=p.state['transport_bytes_saved']
        self.assertIs(p.filter_task(work,task),task)
        self.assertEqual(p.state['transport_mode'],'residue')
        baseline={'model':MODEL,'header':GENESIS.hex(),'target':str(work.target),'nonces':values,'budget_ms':1}
        self.assertEqual(p.state['transport_bytes_saved']-before,compact_request(baseline)[1]['saved_bytes'])
