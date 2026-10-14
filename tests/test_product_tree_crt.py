"""Independent CRT oracles, signed ranges and native consumer boundaries."""
import concurrent.futures
from dataclasses import FrozenInstanceError
from itertools import product
from math import prod, isqrt
import random
import unittest
from unittest.mock import patch

from btcminer.product_tree_crt import ProductTreeCRT
from btcminer.pqmath import RodAbacus


def primes(count):
    limit = 50000
    flags = bytearray(b'\1') * limit
    flags[:2] = b'\0\0'
    for p in range(2, isqrt(limit)+1):
        if flags[p]:
            flags[p*p::p] = b'\0' * ((limit-1-p*p)//p+1)
    result = tuple(p for p, yes in enumerate(flags) if yes)[:count]
    assert len(result) == count
    return result


def large_primes(count=4096):
    """Exact segmented sieve below2^31; no probable-prime assumption."""
    high = (1 << 31)-1
    low = high-100000
    flags = bytearray(b'\1') * (high-low+1)
    for p in primes(5000):
        if p*p > high: break
        first = max(p*p, ((low+p-1)//p)*p)
        flags[first-low::p] = b'\0' * ((high-first)//p+1)
    result = tuple(low+i for i in range(len(flags)-1, -1, -1) if flags[i])[:count]
    assert len(result) == count
    return result

def reference(moduli, residues):
    """Direct CRT sum; deliberately no tree or merge recurrence."""
    capacity = prod(moduli)
    return sum((r % m)*(capacity//m)*pow(capacity//m, -1, m)
               for m, r in zip(moduli, residues)) % capacity


class ProductTreeTests(unittest.TestCase):
    def test_empty_singleton_and_composite_moduli(self):
        for moduli in ((), (8,), (8, 9, 5), (25, 49, 8, 9, 11)):
            plan = ProductTreeCRT(moduli)
            for x in range(-2*plan.capacity, 2*plan.capacity+1, max(1, plan.capacity//50)):
                readings = tuple(x % m for m in moduli)
                self.assertEqual(plan.encode(x), readings)
                self.assertEqual(plan.decode(readings), x % plan.capacity)
            self.assertEqual(plan.capacity, prod(moduli))

    def test_exhaustive_residue_tuples_and_signed_intervals(self):
        plan = ProductTreeCRT((3, 4, 5))
        for residues in product(range(3), range(4), range(5)):
            canonical = reference(plan.moduli, residues)
            self.assertEqual(plan.decode(residues), canonical)
            self.assertEqual(plan.decode_interval(residues, -30, 29), (canonical+30)%60-30)
            for low in (-100, -1, 0, 1, 100):
                # Independent enumeration of a shorter, possibly empty lift.
                candidates = [x for x in range(low, low+7)
                              if all(x % m == r for m, r in zip(plan.moduli, residues))]
                if candidates:
                    self.assertEqual(plan.decode_interval(residues, low, low+6), candidates[0])
                else:
                    with self.assertRaises(ArithmeticError):
                        plan.decode_interval(residues, low, low+6)

    def test_noncanonical_negative_residues_and_big_uneven_rods(self):
        rng = random.Random(940133)
        for moduli in ((2, 3, 5, 7, 11), (2**521-1, 2**127-1, 2**89-1)):
            plan = ProductTreeCRT(moduli)
            for _ in range(40):
                residues = tuple(rng.randrange(-m**2, m**2) for m in moduli)
                self.assertEqual(plan.decode(residues), reference(moduli, residues))

    def test_invalid_domains_and_capacity_equality_boundary(self):
        for moduli in ((1,), (0,), (-3,), (3, 3), (6, 10), (2, 3, 5, 9)):
            with self.assertRaises(ValueError): ProductTreeCRT(moduli)
        for moduli in ((True,), (2.0,), ('3',)):
            with self.assertRaises(TypeError): ProductTreeCRT(moduli)
        plan = ProductTreeCRT((3, 5))
        for residues in ((), (1,), (1, 2, 3)):
            with self.assertRaises(ValueError): plan.decode(residues)
        for residue in (True, 1.0, '1'):
            with self.assertRaises(TypeError): plan.decode((residue, 2))
        with self.assertRaises(ValueError): plan.decode_interval((0, 0), 1, 0)
        with self.assertRaises(OverflowError): plan.decode_interval((0, 0), 0, 15)
        with self.assertRaises(TypeError): plan.decode_interval((0, 0), False, 1)
        self.assertEqual(plan.decode_interval((0, 0), 0, 14), 0)
        with self.assertRaises(FrozenInstanceError): plan.capacity = 100

    def test_4096_rods_and_reusable_parallel_readback(self):
        plan = ProductTreeCRT(primes(4096))
        self.assertEqual(len(plan.levels), 12)
        self.assertGreater(plan.capacity.bit_length(), 50000)
        rng = random.Random(998122)
        values = (0, 1, plan.capacity-1, -1, -(plan.capacity//3),
                  rng.getrandbits(plan.capacity.bit_length()+50))
        for value in values:
            residues = tuple(value % m for m in plan.moduli)
            self.assertEqual(plan.encode(value), residues)
            self.assertEqual(plan.decode(residues), value % plan.capacity)
        residue_sets = [plan.encode(v) for v in values]
        with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
            self.assertEqual(list(executor.map(plan.decode, residue_sets)),
                             [v % plan.capacity for v in values])
        # A full 4096-rod independent CRT sum oracle at a nontrivial point.
        self.assertEqual(plan.decode(residue_sets[-1]), reference(plan.moduli, residue_sets[-1]))

    def test_4096_largest_31_bit_prime_rods(self):
        moduli = large_primes()
        self.assertEqual((moduli[0], moduli[-1]), (2147483647, 2147395373))
        plan = ProductTreeCRT(moduli)
        self.assertEqual(plan.capacity.bit_length(), 126976)
        self.assertLess(1 << 126975, plan.capacity)
        self.assertLess(plan.capacity, 1 << 126976)
        for value in (0, 1, plan.capacity-1, -1, 1 << 126975,
                      -(1 << 126974), (1 << 250000)+19):
            residues = tuple(value % m for m in moduli)
            self.assertEqual(plan.encode(value), residues)
            self.assertEqual(plan.decode(residues), value % plan.capacity)
        residues = tuple((i*i+19) % m for i,m in enumerate(moduli))
        self.assertEqual(plan.decode(residues), reference(moduli, residues))

    def test_rod_abacus_uses_one_reusable_plan(self):
        abacus = RodAbacus((8, 9, 5))
        plan = abacus._crt_plan
        for value in (-1000, 123, 799):
            self.assertEqual(abacus.reconstruct(abacus.reading(value)), value % 360)
            self.assertIs(abacus._crt_plan, plan)

    def test_large_native_frame_decode_preserves_range_and_certificate(self):
        from btcminer.shared_abacus import Frame
        frame = Frame(primes=64)
        column = frame.column(-(1 << 250)+129)
        self.assertIsNone(frame._crt_plan)
        self.assertEqual(column.value(), -(1 << 250)+129)
        plan = frame._crt_plan
        self.assertIsNotNone(plan)
        column.load((1 << 255)-7)
        self.assertEqual(column.value(), (1 << 255)-7)
        self.assertIs(frame._crt_plan, plan)
        # Native arithmetic result, not only an encode/decode of a literal.
        other, result = frame.column(13), frame.column()
        frame.program([('mul', 2, 0, 1)], [column, other, result])
        self.assertEqual(result.value(), ((1 << 255)-7)*13)
        for invalid in (ProductTreeCRT((3, 5)), object()):
            frame._crt_plan = invalid
            with self.assertRaises(ValueError): column.value()
        frame._crt_plan = plan
        self.assertEqual(column.value(), (1 << 255)-7)
        result._data[0] ^= 1
        with self.assertRaises(ValueError): result.value()
        small = Frame((3, 5, 7))
        self.assertEqual(small.column(-15).value(), -15)
        self.assertIsNone(small._crt_plan)


if __name__ == '__main__':
    unittest.main()
