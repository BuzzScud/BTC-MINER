import base64
from dataclasses import FrozenInstanceError
import hashlib
import json
from math import gcd, lcm
import random
import struct
import unittest
from unittest.mock import patch

from btcminer import ROOT
from btcminer.geometry_codec import (ResidueFrame, Bits, pack_fields, frames, q_model,
    encode_points, decode_points, describe_points, compact_request, transport_check, LIMIT)
from btcminer.pruning import Pruner, MODEL
from btcminer.pruning_worker import evaluate, request_key
from btcminer.diagnostics import GENESIS
from btcminer.protocol import Work
from btcminer.settings import DEFAULTS


def corrupt(encoded, change):
    raw=bytearray(base64.b64decode(encoded));change(raw)
    return base64.b64encode(raw).decode()


class GeometryCodecTests(unittest.TestCase):
    def test_coprime_frame_order_and_immutability(self):
        a=ResidueFrame((3,5,7));b=ResidueFrame((5,3,7))
        self.assertNotEqual(a.fingerprint,b.fingerprint)
        with self.assertRaises(FrozenInstanceError):a.moduli=(5,7)
        for invalid in [(3,6),(2,2),(),(True,3),(1,3)]:
            with self.assertRaises((ValueError,TypeError)):ResidueFrame(invalid)

    def test_complete_small_frame_matches_independent_crt_sum(self):
        f=ResidueFrame((3,5,7));values=list(range(105))
        data=f.pack(values,104);self.assertEqual(f.unpack(data,105,104),values)
        bits=Bits(data)
        for value in values:
            residues=[bits.take(w) for w in f.widths]
            oracle=sum(r*(105//m)*pow(105//m,-1,m) for r,m in zip(residues,f.moduli))%105
            self.assertEqual(oracle,value)
        bits.finish()
        self.assertEqual(len(data),(105*(2+3+3)+7)//8)

    def test_arbitrary_precision_not_u32_storage(self):
        middle=1<<4096;f=ResidueFrame((middle-1,middle,middle+1))
        values=[0,(1<<8193)+19,f.capacity-1]
        self.assertEqual(f.unpack(f.pack(values,f.capacity-1),3,f.capacity-1),values)
        self.assertGreater(f.capacity.bit_length(),8192)

    def test_canonical_residues_bounds_lengths_and_padding(self):
        f=ResidueFrame((3,5));data=f.pack([1],14)
        for data,count,bound in [(bytes([3]),1,14),(data+b'\0',1,14),(bytes([0x80]),1,14),(data,1,0),(data,1,15)]:
            with self.subTest(data=data,bound=bound):
                with self.assertRaises(ValueError):f.unpack(data,count,bound)
        with self.assertRaises(ValueError):f.pack([15],14)
        with self.assertRaises(ValueError):pack_fields([(True,1)])

    def test_orbits_wrap_duplicate_and_singleton(self):
        for values in [[17], [5]*64, [(LIMIT-8+i*7)%LIMIT for i in range(64)], [(17-13*i)%LIMIT for i in range(64)]]:
            encoded=encode_points(values,'orbit')
            self.assertEqual(decode_points(encoded),values)
            d=describe_points(encoded)
            self.assertEqual([(d['start']+i*d['step'])%d['modulus'] for i in range(d['count'])],values)
        with self.assertRaises(ValueError):encode_points([1,3,6],'orbit')

    def test_adaptive_prefix_is_exact_and_minimal(self):
        for bound in [0,10,11,208,209,123456789,LIMIT-1]:
            values=[bound,0,bound//2,bound]
            encoded=encode_points(values,'residue');d=describe_points(encoded)
            self.assertEqual(decode_points(encoded),values)
            self.assertGreater(d['capacity'],bound)
            if len(d['moduli'])>1:self.assertLessEqual(d['capacity']//d['moduli'][-1],bound)

    def test_q_same_clock_is_not_same_product(self):
        frame=q_model(33264000)
        a,b=frame.coordinates(10),frame.coordinates(15)
        self.assertEqual(a['k'],b['k']);self.assertNotEqual(a['index'],b['index'])
        with self.assertRaises(TypeError):frame.routes[10]=(0,0)
        for value in frame.routes:
            row=frame.coordinates(value);p,q=row['p'],row['q']
            self.assertEqual(p*q,value);self.assertEqual(lcm(p-1,q-1),row['k'])
            self.assertEqual(gcd(p,q),1)
        values=[v for v in sorted(frame.routes) if v<LIMIT]
        for start in range(0,len(values),64):
            block=values[start:start+64]
            self.assertEqual(decode_points(encode_points(block,'q-route')),block)
        self.assertEqual(decode_points(encode_points([10,15,10],'q-route')),[10,15,10])

    def test_wrong_frames_modes_counts_and_all_truncations_rejected(self):
        for mode,values in [('orbit',list(range(64))),('residue',[0,4,1]),('q-route',[10,15,33]),('raw32',[0,LIMIT-1])]:
            encoded=encode_points(values,mode);raw=base64.b64decode(encoded)
            for cut in range(len(raw)):
                with self.assertRaises(ValueError):decode_points(base64.b64encode(raw[:cut]).decode())
            for index,value in [(0,0),(3,99),(4,0),(4,65),(5,raw[5]^1)]:
                with self.assertRaises(ValueError):decode_points(corrupt(encoded,lambda r:r.__setitem__(index,value)))
            with self.assertRaises(ValueError):decode_points(encoded+'\n')
            with self.assertRaises(ValueError):decode_points(base64.b64encode(raw+b'\0').decode())

    def test_invalid_domains_and_envelope_limits(self):
        for values in [[],[True],[-1],[1.0],[LIMIT],list(range(65))]:
            for mode in ['orbit','residue','q-route','raw32']:
                with self.assertRaises(ValueError):encode_points(values,mode)
        for invalid in [None,{},'!', 'é', 'a'*4097]:
            with self.assertRaises(ValueError):decode_points(invalid)

    def test_random_roundtrips_and_never_larger_selection(self):
        rng=random.Random(109)
        for n in [1,2,8,16,64]:
            for _ in range(20):
                values=[rng.randrange(LIMIT) for _ in range(n)]
                for mode in ['raw32','residue']:
                    self.assertEqual(decode_points(encode_points(values,mode)),values)
                request={'nonces':values,'header':GENESIS.hex(),'target':'1','model':MODEL}
                selected,stats=compact_request(request)
                self.assertLessEqual(len(json.dumps(selected)),len(json.dumps(request)))
                self.assertEqual(stats['saved_bytes'],len(json.dumps(request))-len(json.dumps(selected)))
                decoded=decode_points(selected['nonce_geometry']) if 'nonce_geometry' in selected else selected['nonces']
                self.assertEqual(decoded,values)
        self.assertTrue(transport_check()['ok'])

    def test_bad_encoder_replay_falls_back_raw(self):
        request={'nonces':[1,2,3]}
        with patch('btcminer.geometry_codec.encode_points',return_value='broken'):
            self.assertIs(compact_request(request)[0],request)

    def test_new_worker_encoding_matches_raw_digest_and_rejects_ambiguity(self):
        for mode,values in [('orbit',[(LIMIT-30+i*7)%LIMIT for i in range(64)]),('residue',[19,0,18]),('q-route',[10,15,10]),('raw32',[LIMIT-1,0])]:
            request={'model':MODEL,'header':GENESIS.hex(),'target':'123','nonce_geometry':encode_points(values,mode)}
            with patch('btcminer.pruning_worker.z3',None):result=evaluate(request)
            self.assertEqual(result['keep'],values)
            self.assertEqual(result['key'],request_key(GENESIS.hex(),123,values))
            for extra in ['nonces','nonce_codes']:
                with self.assertRaises(ValueError):evaluate(dict(request,**{extra:values}))

    def test_actual_pruner_routes_geometry_and_retains_winner(self):
        p=Pruner(dict(DEFAULTS,pruning_candidates=64));self.addCleanup(p.close)
        winner=struct.unpack_from('<I',GENESIS,76)[0]
        values=[winner+i for i in range(64)];task={'nonces':values}
        target=int.from_bytes(hashlib.sha256(hashlib.sha256(GENESIS).digest()).digest(),'little')
        work=Work(GENESIS,target,target,0,'1d00ffff','geometry',1)
        def propose_removing_everything(request):
            self.assertIn('nonce_geometry',request)
            self.assertEqual(decode_points(request['nonce_geometry']),values)
            return {'model':MODEL,'key':request_key(request['header'],target,values),'keep':[],
                    'excluded':len(values),'unknown':False}
        with patch.object(p,'query',side_effect=propose_removing_everything):result=p.filter_task(work,task)
        self.assertIn(winner,result['nonces'])
        self.assertEqual(p.state['contradictions'],1)
        self.assertEqual(p.state['transport_mode'],'orbit')
        self.assertGreater(p.state['transport_bytes_saved'],0)

    def test_wrong_reconstruction_digest_keeps_all_candidates(self):
        p=Pruner(dict(DEFAULTS,pruning_candidates=64));self.addCleanup(p.close)
        values=list(range(3000000000,3000000064));task={'nonces':values}
        work=Work(GENESIS,0,0,0,'1d00ffff','geometry',1)
        with patch.object(p,'query',return_value={'model':MODEL,'key':'wrong-frame-job','keep':[],'excluded':64}):
            self.assertIs(p.filter_task(work,task),task)
        self.assertEqual(p.state['candidates_excluded'],0)


class GeometryContractTests(unittest.TestCase):
    def test_contract_binds_current_sources_and_real_gate_names(self):
        contract=json.loads((ROOT/'research/geometry-codec-contract.json').read_text())
        self.assertFalse(contract['bitcoin_nonce_exclusion_authority'])
        for path,digest in contract['implementation_sources'].items():
            self.assertEqual(hashlib.sha256((ROOT/path).read_bytes()).hexdigest(),digest,path)
        from test_geometry_predictive import PredictiveGeometryTests
        classes={'GeometryCodecTests':GeometryCodecTests,'PredictiveGeometryTests':PredictiveGeometryTests}
        for card in contract['cards']:
            self.assertEqual(card['formal_refinement'],'unproved')
            owner,name=card['gate'].split('.')
            self.assertTrue(callable(getattr(classes[owner],name)))
