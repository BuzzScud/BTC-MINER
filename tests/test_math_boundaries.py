"""Independent coverage and PoW boundary checks for the monitored math integration."""
import ctypes as C
import hashlib
import itertools
from math import gcd
import unittest

from btcminer.native import Hasher
from btcminer.thesis2 import BIG_CLOCK, NONCE_SPACE, Traversal, board_loop, qualifying_primes


class MathBoundaryTests(unittest.TestCase):
    def test_all_supported_steps_and_field_phases_permute_the_residue_dial(self):
        field = board_loop()
        labels = [a+19*b-1 for a,b in field]
        self.assertEqual(sorted(labels), list(range(360)))
        steps = [s for s in range(1,360) if gcd(s,360)==1]
        self.assertEqual(len(steps),96)
        # Exhaust every step and phase used by the actual traversal's residue map.
        for step in steps:
            for phase in range(360):
                self.assertEqual(len({labels[(phase+k*step)%360] for k in range(360)}),360)
        # The independent cell permutation composes with any residue permutation.
        for prime in qualifying_primes():
            self.assertEqual(gcd(prime,400),1)
            self.assertEqual(len({(i*prime)%400 for i in range(400)}),400)

    def test_every_prime_preserves_exact_final_tile_in_native_code(self):
        hasher = Hasher()
        if not hasher.fill_nonces:
            self.skipTest('Native traversal library is unavailable')
        steps = [s for s in range(1,360) if gcd(s,360)==1]
        for i,prime in enumerate(qualifying_primes()):
            header = hashlib.shake_256(str(prime).encode()).digest(80)
            plan = Traversal(header, step=steps[i*7 % len(steps)], prime=prime)
            plan.first_tile = 0
            last_base = (plan.tile_count-1)*BIG_CLOCK
            remaining = NONCE_SPACE-last_base
            self.assertEqual(last_base+remaining,1<<32)
            cursor = C.c_uint64(last_base)
            offsets = (C.c_uint32*BIG_CLOCK).from_buffer(plan.offsets)
            output = (C.c_uint32*BIG_CLOCK)()
            count = hasher.fill_nonces(offsets,BIG_CLOCK,0,C.byref(cursor),BIG_CLOCK,output)
            actual = list(output[:count])
            with self.subTest(prime=prime):
                self.assertEqual(count,remaining)
                self.assertEqual(sorted(actual),list(range(last_base,NONCE_SPACE)))
                self.assertEqual(actual,[last_base+x for x in plan.offsets if x<remaining])
                self.assertEqual(plan.rank(actual[0]),last_base)
                self.assertEqual(plan.rank(actual[-1]),NONCE_SPACE-1)
                self.assertEqual(hasher.fill_nonces(offsets,BIG_CLOCK,0,C.byref(cursor),BIG_CLOCK,output),0)

    def test_math_generated_nonces_obey_independent_sha256d_target_boundaries(self):
        hasher = Hasher()
        if not hasher.lib:
            self.skipTest('Native hashing library is unavailable')
        for prime in qualifying_primes():
            header = hashlib.shake_256(('pow-'+str(prime)).encode()).digest(80)
            plan = Traversal(header,prime=prime)
            values = list(itertools.islice(plan.nonces(),64))
            hashes = [int.from_bytes(hashlib.sha256(hashlib.sha256(
                header[:76]+nonce.to_bytes(4,'little')).digest()).digest(),'little') for nonce in values]
            target = min(hashes)
            winner = hashes.index(target)
            with self.subTest(prime=prime):
                self.assertEqual(hasher.scan(header,target,nonces=values),(winner+1,values[winner]))
                self.assertEqual(hasher.scan(header,target-1,nonces=values),(len(values),None))
