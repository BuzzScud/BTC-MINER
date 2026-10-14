import itertools
import random
import struct
import unittest
from collections import Counter
from unittest.mock import Mock

from btcminer.abacus import Workspace,resident_model
from btcminer.connections import CoreConnection
from btcminer.diagnostics import GENESIS
from btcminer.native import Hasher
from btcminer.protocol import Work
from btcminer.settings import DEFAULTS
from btcminer.thesis2 import Traversal


class ResidentAbacusTests(unittest.TestCase):
    def test_binary_packing_and_core_identities(self):
        m=resident_model();self.assertIs(m,resident_model())
        self.assertEqual(m.binary.capacity,8589932544)
        rng=random.Random(19)
        for n in [0,1,2046,2047,2048,2049,(1<<32)-1]+[rng.randrange(1<<32) for _ in range(2000)]:
            self.assertEqual(m.unpack_word(m.pack_word(n)),n)
        self.assertEqual(109**2-1,33*360)
        self.assertEqual(71**2-1,5040)
        self.assertEqual(19**2-1,360)
        self.assertEqual(m.core.rods,(11,19,71,97,109))
        with self.assertRaises(ValueError):m.unpack_word(2047)

    def test_golay_packing_matches_source_for_all_codewords(self):
        m=resident_model();words=[]
        for message in range(4096):
            expected=0
            for i in range(12):
                if message>>i&1:expected^=(0xC75<<i)^(1<<23)
            value=m.golay(message);words.append(value)
            self.assertEqual(value,expected)
            self.assertEqual(value^0xffffff,m.golay(message^0xAE3))
        self.assertEqual(len(set(words)),4096)
        self.assertEqual(Counter(bin(x).count('1') for x in words),{0:1,8:759,12:2576,16:759,24:1})
        self.assertEqual(len(m.golay_pairs),6144)

    def test_e8_root_configuration_has_no_overlapping_equal_spheres(self):
        data=memoryview(resident_model().e8_roots).cast('b')
        roots=[tuple(data[i:i+8]) for i in range(0,len(data),8)]
        self.assertEqual(len(set(roots)),240)
        self.assertTrue(all(sum(v*v for v in r)==8 for r in roots))
        self.assertEqual(min(sum((x-y)**2 for x,y in zip(a,b)) for a,b in itertools.combinations(roots,2)),8)

    def test_warm_workspace_matches_original_order_and_reuses_storage(self):
        hasher=Hasher()
        for step,prime in ((7,19),(359,7),(1,24001)):
            ws=Workspace(hasher,step)
            ids=tuple(id(x) for x in (ws.model,ws.offsets,ws.residue_rows,ws.header_rods,ws.core_readings))
            for gen,header in enumerate((GENESIS,bytes(80),bytes(range(80))),1):
                ws.bind(Work(header,1,1,100,'207fffff','fixture',gen))
                old=Traversal(header,step,prime)
                new=Traversal(header,step,prime,workspace=ws)
                self.assertEqual(new.offsets,old.offsets)
                packed=int.from_bytes(ws.header_rods,'little')
                recovered=[ws.model.unpack_word((packed>>(34*i))&((1<<34)-1)) for i in range(20)]
                self.assertEqual(struct.pack('>20I',*recovered),header)
                new.first_tile=old.first_tile=29826
                self.assertEqual(list(itertools.islice(new.nonces(),24000)),list(itertools.islice(old.nonces(),24000)))
                self.assertEqual(ids,tuple(id(x) for x in (ws.model,ws.offsets,ws.residue_rows,ws.header_rods,ws.core_readings)))
            self.assertEqual(ws.jobs,3);self.assertEqual(ws.tip_changes,1)

    def test_python_fallback_uses_same_resident_order(self):
        ws=Workspace(Hasher(False),7)
        self.assertEqual(Traversal(GENESIS,workspace=ws).offsets,Traversal(GENESIS).offsets)


class CoreTipTests(unittest.TestCase):
    def make_connection(self):
        c=CoreConnection(dict(DEFAULTS),Mock());c.rpc=Mock();c.connected=True
        c.verify_accepted=Mock(return_value={})
        c.template={'placeholder':True};c.generation=5
        work=Work(GENESIS,1,1,100,'207fffff','fixture',5,{'body':bytes()})
        return c,work

    def test_accepted_block_immediately_retires_its_template(self):
        c,work=self.make_connection();c.rpc.call.return_value=None
        self.assertEqual(c.submit(work,0),(True,'block accepted',True))
        self.assertFalse(c.valid(work));self.assertIsNone(c.work())

    def test_late_acceptance_does_not_erase_a_newer_template(self):
        c,work=self.make_connection()
        def reply(*args):c.generation=6;c.template={'new':True};return None
        c.rpc.call.side_effect=reply;c.submit(work,0)
        self.assertEqual(c.template,{'new':True});self.assertEqual(c.generation,6)

    def test_same_height_parent_change_invalidates_previous_work(self):
        from test_protocol import template,ADDRESS
        c=CoreConnection(dict(DEFAULTS,address=ADDRESS,template_refresh=0),Mock());c.rpc=Mock()
        first=template();first['longpollid']='parent-a'
        second=dict(first,previousblockhash='ab'*32,longpollid='parent-b')
        c.rpc.call.side_effect=[first,second]
        captured=[]
        def emit(*args,**kwargs):
            work=c.work();captured.append(work)
            if len(captured)==2:
                self.assertFalse(c.valid(captured[0]));self.assertTrue(c.valid(work));c.stop.set()
        c.emit=emit;c.run()
        self.assertEqual(captured[0].height,captured[1].height)
        self.assertEqual(captured[1].header[4:36],bytes.fromhex('ab'*32)[::-1])
        self.assertNotEqual(captured[0].generation,captured[1].generation)
        self.assertEqual(c.rpc.call.call_args_list[1].args[1], [{'rules':['segwit']}])
