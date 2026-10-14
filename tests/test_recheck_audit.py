"""Independent boundary checks added during the second audit."""
from array import array
import random
import struct
import unittest
import tempfile
import shutil
from pathlib import Path
from unittest.mock import patch

from btcminer.native import Hasher, hash256
from btcminer.serialization import _build_coinbase, _build_coinbase_script_sig, _height_to_script_push


class RecheckAuditTests(unittest.TestCase):
    def test_priority_observation_counts_wrapped_winning_nonce(self):
        from btcminer.priority import Priority
        p=Priority()
        p.observe({'start':2**32-1,'count':2},2,[0])
        self.assertEqual(sum(count for count,hits in p.samples.values()),2)
        self.assertEqual(sum(hits for count,hits in p.samples.values()),1)
        self.assertEqual(p.samples[p.features(0)][1],1)

    def test_revision_changes_for_serialization_difficulty_and_built_library(self):
        from btcminer import mathrevision as revision
        native=next(name for name in revision.FILES if name.endswith(('.dylib','.so','.dll')))
        with tempfile.TemporaryDirectory(prefix='btc-revision-audit-') as folder:
            root=Path(folder)
            for name in revision.FILES:
                target=root/name;target.parent.mkdir(parents=True,exist_ok=True)
                shutil.copyfile(revision.ROOT/name,target)
            with patch.object(revision,'ROOT',root):
                baseline=revision.fingerprint()
                for name in ['btcminer/serialization.py','btcminer/difficulty.py',native]:
                    file=root/name
                    file.write_bytes(file.read_bytes()+b'\nchanged fixture\n')
                    current=revision.fingerprint()
                    self.assertNotEqual(current[name],baseline[name],name)
                    baseline=current

    def test_native_and_python_inclusive_targets_at_actual_hash_boundaries(self):
        rng = random.Random(6102026)
        native = Hasher(True)
        self.assertIsNotNone(native.lib, native.reason)
        for _ in range(80):
            header = rng.randbytes(80) if hasattr(rng, 'randbytes') else bytes(rng.getrandbits(8) for _ in range(80))
            nonce = rng.getrandbits(32)
            value = int.from_bytes(hash256(header[:76]+struct.pack('<I',nonce)), 'little')
            for target in [0, max(0,value-1), value, min((1<<256)-1,value+1), (1<<256)-1]:
                expected = (1, nonce if value <= target else None)
                for hasher in [native, Hasher(False)]:
                    for values in [[nonce], array('I',[nonce])]:
                        self.assertEqual(hasher.scan(header,target,nonces=values),expected)

    def test_native_and_python_scans_wrap_at_uint32_boundary(self):
        rng = random.Random(4294967296)
        native, fallback = Hasher(True), Hasher(False)
        self.assertIsNotNone(native.lib, native.reason)
        for _ in range(30):
            header=bytes(rng.getrandbits(8) for _ in range(80))
            start=(1<<32)-rng.randint(1,20)
            count=40
            nonces=[(start+i)&0xffffffff for i in range(count)]
            hashes=[int.from_bytes(hash256(header[:76]+struct.pack('<I',n)),'little') for n in nonces]
            target=sorted(hashes)[rng.randrange(10)]
            index=next(i for i,value in enumerate(hashes) if value<=target)
            expected=(index+1,nonces[index])
            for hasher in [native,fallback]:
                self.assertEqual(hasher.scan(header,target,start=start,count=count),expected)
                self.assertEqual(hasher.scan(header,target,nonces=array('I',nonces)),expected)

    def test_coinbase_final_combined_length_limit(self):
        height=900000
        for auxiliary in [0,1,75,76,90]:
            script=_build_coinbase_script_sig(height,{'flags':bytes(auxiliary)})
            available=100-len(script)
            tx=_build_coinbase(height,50_00000000,b'\x51',{'flags':bytes(auxiliary)},extra_nonce=bytes(available))
            # version(4), input count(1), outpoint(36), script CompactSize(1).
            self.assertEqual(tx[41],100)
            self.assertEqual(tx[42:42+len(_height_to_script_push(height))],_height_to_script_push(height))
            with self.assertRaises(ValueError):
                _build_coinbase(height,50_00000000,b'\x51',{'flags':bytes(auxiliary)},extra_nonce=bytes(available+1))
