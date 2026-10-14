import itertools
import json
from fractions import Fraction
from math import gcd, isqrt
import unittest
from unittest.mock import patch

from btcminer import pqmath
from btcminer import thesis2
from btcminer.diagnostics import GENESIS


def sieve(limit):
    flags = bytearray(b'\x01') * (limit + 1)
    flags[:2] = b'\x00\x00'
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            flags[p*p:limit+1:p] = b'\x00' * ((limit - p*p)//p + 1)
    return flags


class RodTests(unittest.TestCase):
    def test_kernel_example_and_exact_operation_count(self):
        rods = pqmath.DynamicRods(19)
        expected = sieve(361)
        self.assertEqual(rods.rods, (2, 3, 5, 7, 11, 13, 17))
        primes = tuple(x for x in range(19, 361) if expected[x])
        self.assertEqual(len(primes), 65)
        self.assertEqual(rods.primes_in_window(), primes)
        for x in range(2, 361):
            passed, count = rods.pass_count(x)
            self.assertEqual(count, 7)
            self.assertEqual(passed, bool(expected[x] and x >= 19))
            self.assertEqual(rods.is_prime_in_window(x), bool(expected[x]))

    def test_sharp_boundary_requires_extension_and_preserves_readings(self):
        rods = pqmath.DynamicRods(19)
        readings = {x: tuple(x % p for p in rods.rods) for x in range(-50, 550)}
        capacity = rods.capacity
        self.assertTrue(rods.pass_count(19*19)[0])
        with self.assertRaises(ValueError):
            rods.is_prime_in_window(361)
        self.assertEqual(rods.extend(), 19)
        self.assertEqual((rods.frontier, rods.volume, rods.capacity), (23, 529, capacity*19))
        self.assertFalse(rods.is_prime_in_window(361))
        for x, before in readings.items():
            self.assertEqual(tuple(x % p for p in rods.rods)[:-1], before)

    def test_dynamic_growth_matches_independent_sieve(self):
        expected = sieve(20000)
        rods = pqmath.DynamicRods(2)
        for x in range(2, len(expected)):
            rods.ensure_volume(x)
            self.assertGreater(rods.volume, x)
            self.assertEqual(rods.is_prime_in_window(x), bool(expected[x]), x)
        self.assertEqual(rods.rods, tuple(p for p in range(2, rods.frontier) if expected[p]))

    def test_shared_runtime_handles_backward_queries_and_small_primes(self):
        expected = sieve(10000)
        for x in itertools.chain(range(10000, -1, -1), (-20, -1)):
            self.assertEqual(pqmath.is_prime(x), bool(x >= 2 and expected[x]), x)

    def test_least_coprime_prime_including_empty_abacus(self):
        expected = sieve(1000)
        for modulus in range(1, 1000):
            p = pqmath.least_coprime_prime(modulus)
            self.assertTrue(expected[p])
            self.assertEqual(gcd(p, modulus), 1)
            self.assertTrue(all(gcd(x, modulus) > 1 for x in range(2, p)))
        for bad in (0, -1):
            with self.assertRaises(ValueError):
                pqmath.least_coprime_prime(bad)

    def test_general_coprime_extension_is_a_crt_round_trip(self):
        base = pqmath.RodAbacus((8, 9, 5))
        extended = base.extend(7)
        self.assertEqual(extended.capacity, 2520)
        for x in range(-2600, 2600):
            self.assertEqual(extended.reading(x)[:-1], base.reading(x))
            self.assertEqual(extended.reconstruct(extended.reading(x)), x % 2520)
            self.assertEqual(base.extend_residue(x % 360, 7, x % 7), x % 2520)
        empty = pqmath.RodAbacus()
        self.assertEqual(empty.reconstruct(()), 0)
        self.assertEqual(empty.extend_residue(0, 7, 5), 5)
        for invalid in (1, 2, 6, 9):
            with self.assertRaises(ValueError):
                base.extend(invalid)

    def test_rod_factoring_and_supplied_eccentricity_band(self):
        rods = pqmath.DynamicRods(61)
        self.assertEqual(rods.factor_on_rods(3439), (19, 181))
        self.assertEqual(rods.factor_on_rods(3439, ('1/10', '1/8')), (19, 181))
        self.assertIsNone(rods.factor_on_rods(3439, ('1/2', '3/4')))
        self.assertIsNone(rods.factor_on_rods(3499))  # independently prime by sieve
        self.assertTrue(sieve(3499)[3499])
        self.assertEqual(rods.factor_on_rods(49), (7, 7))
        self.assertEqual(rods.factor_on_rods(10), (2, 5))
        with self.assertRaises(ValueError):
            rods.factor_on_rods(61*61)

    def test_invalid_rods_and_out_of_volume_queries(self):
        for frontier in (0, 1, 4, 20):
            with self.assertRaises(ValueError):
                pqmath.DynamicRods(frontier)
        rods = pqmath.DynamicRods()
        for value in (0, 1, 361, 400):
            with self.assertRaises(ValueError):
                rods.is_prime_in_window(value)
        for value in (2.5, True, '19'):
            with self.assertRaises(TypeError):
                pqmath.is_prime(value)
        with self.assertRaises(ValueError):
            pqmath.pass_count((2, 0), 19)


class EllipseTests(unittest.TestCase):
    def test_exact_identities_and_reconstruction_for_integer_pairs(self):
        for p in range(1, 31):
            for q in range(p + 1, 60):
                e = pqmath.PQEllipse(p, q)
                lo, hi = e.r_min, e.r_max
                self.assertEqual(hi + lo, q)
                self.assertEqual(hi - lo, p)
                self.assertEqual(hi * lo, e.semi_minor_squared)
                self.assertEqual(hi**2 - lo**2, p*q)
                self.assertEqual(q**4, e.n**2 + 16*e.area_over_pi_squared)
                self.assertEqual(p*p, e.n*e.eccentricity)
                self.assertEqual(q*q, e.n/e.eccentricity)
                self.assertEqual(pqmath.PQEllipse.from_bounds(lo, hi), e)
                self.assertEqual(pqmath.PQEllipse.from_area_squared(e.n, e.area_over_pi_squared), e)
                self.assertEqual(pqmath.PQEllipse.from_eccentricity(e.n, e.eccentricity), e)

    def test_focal_oscillation_endpoints_and_monotonic_bounds(self):
        for p, q in ((19, 181), (101, 103), (2, 3)):
            e = pqmath.PQEllipse(p, q)
            self.assertEqual(e.focal_radius(1), e.r_min)
            self.assertEqual(e.focal_radius(-1), e.r_max)
            values = [e.focal_radius(Fraction(i, 100)) for i in range(-100, 101)]
            self.assertEqual(values, sorted(values, reverse=True))
            self.assertTrue(all(e.r_min <= r <= e.r_max for r in values))

    def test_integer_band_rounding_matches_squared_inequalities(self):
        for n in range(1, 300):
            for lo, hi in ((0, 1), ('1/10', '1/8'), ('1/3', '2/3'), ('1/2', '1/2')):
                lower, upper = pqmath.eccentricity_bounds(n, lo, hi)
                expected = [p for p in range(isqrt(n) + 1) if n*Fraction(lo) <= p*p <= n*Fraction(hi)]
                self.assertEqual(list(range(lower, upper + 1)), expected)
        self.assertEqual(pqmath.eccentricity_bounds(3439, '1/10', '1/8'), (19, 20))

    def test_odd_semiprimes_have_only_the_two_divisor_partitions(self):
        flags = sieve(100)
        primes = [p for p in range(3, 100) if flags[p]]
        for p, q in itertools.combinations(primes, 2):
            n = p*q
            pairs = {pqmath.difference_of_squares_pair(n, d) for d in range(1, isqrt(n)+1) if n % d == 0}
            lo, hi = pqmath.PQEllipse(p, q).integer_bounds()
            self.assertEqual(pairs, {((n+1)//2, (n-1)//2), (hi, lo)})
            self.assertEqual(gcd(lo, hi), 1)
            for x, y in pairs:
                self.assertEqual(x*x - y*y, n)
                self.assertEqual(n % (x-y), 0)

    def test_fermat_search_budget_and_proved_gap_bound(self):
        flags = sieve(100)
        primes = [p for p in range(3, 100) if flags[p]]
        for p, q in itertools.combinations(primes, 2):
            ellipse = pqmath.PQEllipse(p, q)
            steps = ellipse.fermat_steps()
            self.assertLessEqual(steps, ellipse.fermat_step_bound())
            result = pqmath.fermat_factor(p*q, steps)
            self.assertEqual(result.factors, (p, q))
            self.assertEqual((result.increments, result.square_tests), (steps, steps+1))
            if steps:
                self.assertIsNone(pqmath.fermat_factor(p*q, steps-1))
        self.assertEqual(pqmath.fermat_factor(3439, 41).factors, (19, 181))
        self.assertIsNone(pqmath.fermat_factor(3439, 40))
        self.assertEqual(pqmath.fermat_factor(49, 0).factors, (7, 7))
        self.assertEqual(pqmath.fermat_factor(10, 0).factors, (2, 5))
        self.assertIsNone(pqmath.fermat_factor(101, 100))
        self.assertIsNone(pqmath.fermat_factor(2, 0))

    def test_close_factors_are_high_eccentricity_and_fast_for_fermat(self):
        close = pqmath.PQEllipse(101, 103)
        rounder = pqmath.PQEllipse(3, 101)
        self.assertGreater(close.eccentricity, Fraction(9, 10))
        self.assertEqual(close.fermat_steps(), 0)
        self.assertLess(rounder.eccentricity, Fraction(1, 10))
        self.assertGreater(rounder.fermat_steps(), 0)

    def test_arbitrary_precision_geometry_above_8192_product_bits(self):
        # These integers are not claimed prime; the algebraic identities do not need that.
        p = 2**4200 + 1
        q = p + 2
        e = pqmath.PQEllipse(p, q)
        self.assertGreater(e.n.bit_length(), 8192)
        self.assertEqual(e.r_max**2 - e.r_min**2, e.n)
        self.assertEqual(pqmath.PQEllipse.from_area_squared(e.n, e.area_over_pi_squared), e)
        self.assertEqual(pqmath.PQEllipse.from_eccentricity(e.n, e.eccentricity), e)
        self.assertEqual(pqmath.eccentricity_bounds(e.n, e.eccentricity, e.eccentricity), (p, p))
        self.assertEqual(pqmath.fermat_factor(e.n, 0).factors, (p, q))

    def test_invalid_geometry_and_float_inputs_do_not_get_rounded_silently(self):
        for p, q in ((0, 19), (-1, 19), (19, 19), (181, 19)):
            with self.assertRaises(ValueError):
                pqmath.PQEllipse(p, q)
        with self.assertRaises(ValueError):
            pqmath.PQEllipse(2, 3).integer_bounds()
        for lo, hi in ((-1, 1), (1, 0), (0, 2)):
            with self.assertRaises(ValueError):
                pqmath.eccentricity_bounds(3439, lo, hi)
        with self.assertRaises(TypeError):
            pqmath.eccentricity_bounds(3439, .1, .2)
        with self.assertRaises(ValueError):
            pqmath.PQEllipse.from_area_squared(3439, 1)
        with self.assertRaises(ValueError):
            pqmath.PQEllipse.from_eccentricity(3439, '1/2')
        with self.assertRaises(ValueError):
            pqmath.PQEllipse(19, 181).focal_radius(2)


class RuntimeIntegrationTests(unittest.TestCase):
    def test_actual_traversal_prime_selection_calls_dynamic_rods(self):
        expected = sieve(144001)
        expected_primes = tuple(p for p in range(7, 144002) if expected[p] and 144000 % (p-1) == 0)
        thesis2.qualifying_primes.cache_clear()
        with patch.object(thesis2, 'rods_is_prime', wraps=pqmath.is_prime) as prime_check:
            plan = thesis2.Traversal(GENESIS)
            self.assertGreater(prime_check.call_count, 0)
            self.assertEqual(thesis2.qualifying_primes(), expected_primes)
            self.assertEqual(len(expected_primes), 35)
            self.assertEqual(set(plan.offsets), set(range(144000)))
            self.assertEqual(plan.description()['prime_selection'], 'DynamicRods certified-window primality')

    def test_math_inspection_exposes_exact_new_routines(self):
        report = thesis2.report(GENESIS)
        json.dumps(report)
        math = report['ellipse_and_rods']
        self.assertEqual(math['ellipse']['factor_from_loaded_rods_and_band'], (19, 181))
        self.assertEqual(math['rods_before_extension']['primes_in_19_to_361'], 65)
        self.assertFalse(math['rods_after_extension']['361_is_prime'])
        self.assertGreater(report['runtime_prime_rods']['exclusive_volume'], 144000)


if __name__ == '__main__':
    unittest.main()
