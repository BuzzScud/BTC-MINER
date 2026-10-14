import unittest
from math import isqrt
from btcminer import coreprimes as core, thesis2
from btcminer.diagnostics import GENESIS


def factor(n):
    result = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        result[n] = result.get(n, 0) + 1
    return result


def enumerate_circle(n, grid):
    # Independent coordinate count: solve a quadratic in y for each integer x.
    radius = isqrt(4*n//3) + 1
    count = 0
    for x in range(-radius, radius+1):
        disc = n-x*x if grid == 'square' else 4*n-3*x*x
        if disc < 0:
            continue
        root = isqrt(disc)
        if root*root == disc:
            if grid == 'square':
                count += 1 if root == 0 else 2
            else:
                count += sum((x+r) % 2 == 0 for r in {root, -root})
    return count


class CorePrimeTests(unittest.TestCase):
    def test_circle_counts_against_independent_coordinate_enumeration(self):
        for n in list(range(1, 301)) + [p*p for p in core.CORE] + [97*109]:
            for grid in ('square', 'hexagonal'):
                self.assertEqual(core.circle_count(factor(n), grid), enumerate_circle(n, grid), (n, grid))

    def test_scaling_hypotheses_and_coordinate_vs_radius(self):
        for grid in ('square', 'hexagonal'):
            for e in range(6):
                self.assertEqual(core.core_scale_multiplier(e, grid),
                                 core.circle_count({p:e for p in core.CORE}, grid)//core.circle_count({}, grid))
            with self.assertRaises(ValueError):
                core.prime_power_multiplier(19, 2, grid, base=19)
            with self.assertRaises(ValueError):
                core.core_scale_multiplier(2, grid, base=11)
        self.assertEqual(core.prime_power_multiplier(19, 2, 'hexagonal'), 3)
        self.assertEqual(core.prime_power_multiplier(19, 4, 'hexagonal'), 5)
        for p in (1, 18, 121):
            with self.assertRaises(ValueError):
                core.prime_power_multiplier(p, 2, 'square')

    def test_square_rods_roundtrip_and_irrecoverable_scaling(self):
        rods = core.SQUARE_RODS
        self.assertEqual(rods.capacity, 24615334061206009)
        for n in (-10**30, -1, 0, 1, 19, 10**30):
            self.assertEqual(rods.reconstruct(rods.reading(n)), n % rods.capacity)
            self.assertEqual(core.normalize_scaled(n*361, 361, 360), n % 360)
            self.assertEqual(core.normalize_scaled(n*2, 2, rods.capacity), n % rods.capacity)
        with self.assertRaises(ValueError):
            core.normalize_scaled(0, 361, rods.capacity)
        for p in core.CORE:
            for k in (1, 2, 30240, 144000):
                self.assertNotEqual(pow(p, k+1, p*p), p)

    def test_report_is_used_and_clock_conditions_are_preserved(self):
        result = thesis2.report(GENESIS)['core_primes']
        self.assertEqual(result['core_exponent'], 30240)
        self.assertEqual(result['pair_97_109_circle_points'], {'square':16, 'hexagonal':24})
        self.assertEqual(result['core_squared_radius_multipliers'], {'square':9, 'hexagonal':27})
        self.assertEqual(result['core_squared_coordinate_multipliers'], {'square':25, 'hexagonal':125})
        eligible = [v['prime'] for v in result['classification'] if v['qualifies_for_miner_clock']]
        self.assertEqual(eligible, [11,19,97])
        self.assertTrue(set(eligible) <= set(thesis2.qualifying_primes()))
        self.assertNotIn(71, thesis2.qualifying_primes())
        self.assertNotIn(109, thesis2.qualifying_primes())


if __name__ == '__main__':
    unittest.main()
