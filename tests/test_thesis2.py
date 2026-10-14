import itertools
import unittest
import ctypes as C
from array import array

from btcminer.diagnostics import GENESIS
from btcminer.thesis2 import (BIG_CLOCK, NONCE_SPACE, Traversal, board_loop,
                             qualifying_primes, bits_value, encode_gaussian)
from btcminer.native import Hasher
from btcminer.thesis2 import crt_weights, BIG_WHEELS, SMALL_CLOCK


class TraversalTests(unittest.TestCase):
    def test_native_projection_preserves_uint32_descriptor_prime(self):
        from btcminer.thesis2 import OffsetDescriptor
        hasher = Hasher()
        if not hasher.fill_offsets:
            self.skipTest('Native offset projection unavailable')
        for order in ('field', 'flower'):
            descriptor = OffsetDescriptor(143999,359,399,359,4294967293,order)
            output = array('I',[0])*BIG_CLOCK
            hasher.project_offsets(descriptor.residues(),descriptor.phase,
                                   descriptor.cell_phase,descriptor.prime,output)
            self.assertEqual(list(output), [descriptor.offset(i) for i in range(BIG_CLOCK)])
            self.assertEqual(len(set(output)), BIG_CLOCK)

    def test_every_supported_prime_produces_a_full_tile_permutation(self):
        for prime in qualifying_primes():
            with self.subTest(prime=prime):
                plan = Traversal(GENESIS, prime=prime)
                self.assertEqual(len(plan.offsets), BIG_CLOCK)
                self.assertEqual(len(set(plan.offsets)), BIG_CLOCK)
                self.assertEqual((min(plan.offsets), max(plan.offsets)), (0, BIG_CLOCK-1))

    def test_field_visits_every_nonzero_point(self):
        self.assertEqual(set(board_loop()),
                         set(itertools.product(range(19), repeat=2)) - {(0, 0)})

    def test_rank_matches_enumeration_and_partial_tile(self):
        plan = Traversal(GENESIS)
        for i, nonce in enumerate(itertools.islice(plan.nonces(), 1000)):
            self.assertEqual(plan.rank(nonce), i)
        plan.first_tile = plan.tile_count-1
        partial = NONCE_SPACE - plan.first_tile*BIG_CLOCK
        values = list(itertools.islice(plan.nonces(), partial + 10))
        self.assertEqual(len(set(values)), len(values))
        self.assertTrue(all(0 <= n < NONCE_SPACE for n in values))
        for i in (0, partial//2, partial-1, partial, partial+9):
            self.assertEqual(plan.rank(values[i]), i)

    def test_small_batches_preserve_order_and_single_nonce_mode(self):
        plan = Traversal(GENESIS)
        batches = list(itertools.islice(plan.batches(64), 3))
        flattened = [n for batch in batches for n in batch["nonces"]]
        self.assertEqual(flattened, list(itertools.islice(plan.nonces(), 192)))
        self.assertEqual(list(plan.batches(64, single=True)), [{"nonces":[flattened[0]]}])

    def test_nonce_field_does_not_change_search_order(self):
        self.assertEqual(Traversal(GENESIS).offsets,
                         Traversal(GENESIS[:76]+bytes(4)).offsets)

    def test_gaussian_encoding_round_trips_signed_coordinates(self):
        for x, y in itertools.product(range(-20, 21), repeat=2):
            self.assertEqual(bits_value(encode_gaussian(x, y)), (x, y))

    def test_optimized_offsets_match_original_crt_construction(self):
        _, weights = crt_weights(BIG_WHEELS)
        for header, step, prime in ((GENESIS,7,19), (bytes(80),359,7),
                                     (bytes(range(80)),1,24001)):
            plan = Traversal(header, step, prime)
            original = []
            for i in range(400):
                cell = (plan.cell_phase+i*prime) % 400
                for residue in plan.residues:
                    value = SMALL_CLOCK*cell+residue+plan.phase
                    original.append(sum((value%m)*w for m,w in zip(BIG_WHEELS,weights)) % BIG_CLOCK)
            self.assertEqual(list(plan.offsets), original)

    def test_native_batches_match_python_across_partial_tile_and_wrap(self):
        hasher = Hasher()
        if not hasher.fill_nonces:
            self.skipTest("Rebuild native library for optimized traversal")
        for first_tile in (0, 29825, 29826):
            plan = Traversal(GENESIS)
            plan.first_tile = first_tile % plan.tile_count
            expected = list(itertools.islice(plan.nonces(), 400000))
            actual = []
            for task in itertools.islice(hasher.traversal_batches(plan, 10000), 40):
                self.assertIsInstance(task["nonces"], array)
                actual.extend(task["nonces"])
            self.assertEqual(actual, expected)
            first = next(hasher.traversal_batches(plan, 64, single=True))["nonces"]
            self.assertEqual(list(first), expected[:1])

    def test_native_final_tile_finishes_without_wrapping_or_padding(self):
        hasher = Hasher()
        if not hasher.fill_nonces:
            self.skipTest("Rebuild native library for optimized traversal")
        plan = Traversal(GENESIS)
        plan.first_tile = 0
        cursor = C.c_uint64((plan.tile_count-1)*BIG_CLOCK)
        offsets = (C.c_uint32 * BIG_CLOCK).from_buffer(plan.offsets)
        out = (C.c_uint32 * BIG_CLOCK)()
        count = hasher.fill_nonces(offsets, BIG_CLOCK, 0, C.byref(cursor), BIG_CLOCK, out)
        base = (plan.tile_count-1)*BIG_CLOCK
        self.assertEqual(list(out[:count]), [base+n for n in plan.offsets if base+n<NONCE_SPACE])
        self.assertEqual(cursor.value, plan.tile_count*BIG_CLOCK)
        self.assertEqual(hasher.fill_nonces(offsets, BIG_CLOCK, 0, C.byref(cursor), BIG_CLOCK, out), 0)

    def test_buffer_scanning_reports_share_position_and_unscanned_tail(self):
        hasher = Hasher()
        reference = Hasher(False)
        plan = Traversal(GENESIS)
        values = next(hasher.traversal_batches(plan, 1024))["nonces"]
        for target in (1, 1 << 250, (1 << 256)-1):
            self.assertEqual(hasher.scan(GENESIS,target,nonces=values),
                             reference.scan(GENESIS,target,nonces=list(values)))
