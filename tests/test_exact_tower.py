import math
import unittest
from unittest.mock import patch

from btcminer import exact_tower as tower
import thesis_mining as legacy


class ExactTowerTests(unittest.TestCase):
    def test_small_towers_against_unreduced_exponents(self):
        # The oracle constructs only the inner exponent, independently of
        # Euler periods, factorization, valuations, or CRT.
        for base in range(12):
            for modulus in range(1, 129):
                expected = (1 % modulus, base % modulus,
                            pow(base, base, modulus),
                            pow(base, base ** base, modulus))
                for height, residue in enumerate(expected):
                    self.assertEqual(tower.tetration_mod(base, height, modulus),
                                     residue, (base, height, modulus))

    def test_regression_and_non_coprime_thresholds(self):
        self.assertEqual(legacy._tetration_mod(3, 3, 7), 6)
        # Reducing at the same modulus was wrong; blindly applying Euler's
        # period to a nonunit is also wrong at a zero reduced exponent.
        self.assertEqual(pow(3, pow(3, 3, 7), 7), 1)
        self.assertEqual(pow(2, pow(2, 2, 2), 4), 1)
        self.assertEqual(tower.tetration_mod(2, 3, 4), 0)
        for base in (2, 3, 4, 6, 12):
            for modulus in (4, 8, 16, 32, 64, 128, 256, 1024,
                            3**12, 5**9, 2**12 * 3**7, 2**63,
                            3**40, 5**27, 2**25 * 3**20):
                self.assertEqual(tower.tetration_mod(base, 3, modulus),
                                 pow(base, base ** base, modulus))
        self.assertEqual(tower.tetration_mod(2, 3, 256), 16)
        self.assertEqual(tower.tetration_mod(2, 3, 16), 0)

    def test_actual_seed_modulus_against_direct_small_exponents(self):
        modulus = tower.UINT64_MAX
        for base in (0, 1, 2, 3, 5, 7, 11, 19, 73, 109, 257, 641):
            self.assertEqual(tower.tetration_mod(base, 3, modulus),
                             pow(base, base ** base, modulus), base)

    def test_large_seed_independent_squarefree_period_oracle(self):
        # For a squarefree modulus, adding a positive common period is safe
        # even on nonunit rods: divisible-base residues remain zero. This
        # global formula is independent of the implementation's CRT assembly.
        modulus = (1 << 64) - 1
        primes = (3, 5, 17, 257, 641, 65537, 6700417)
        period = math.lcm(*(p-1 for p in primes))
        self.assertEqual(math.prod(primes), modulus)
        for base in (65537, 6700417, 1_000_003, 1_000_000_007,
                     modulus-1, modulus):
            expected = pow(base, pow(base, base, period) + period, modulus)
            self.assertEqual(tower.tetration_mod(base, 3, modulus), expected, base)

    def test_domain_and_budget_fail_explicitly(self):
        for args in ((2, 4, 7), (-1, 3, 7), (2, -1, 7),
                     (2**64, 3, 7), (2, 3, 2**64), (2, 3, 0)):
            with self.assertRaises(ValueError, msg=str(args)):
                tower.tetration_mod(*args)
        for args in ((True, 3, 7), (2, 3.0, 7), (2, 3, False)):
            with self.assertRaises(TypeError):
                tower.tetration_mod(*args)
        tower._factor_small_or_budgeted.cache_clear()
        try:
            with patch.object(tower, 'MAX_FACTOR_TRIALS', 1):
                with self.assertRaises(tower.TowerBudgetError):
                    tower.tetration_mod(2, 3, 1_000_000_007)
        finally:
            tower._factor_small_or_budgeted.cache_clear()

    def test_native_setting_cannot_bypass_exact_mapping(self):
        with patch.object(legacy, 'use_c_nonce', return_value=True), \
             patch.object(legacy, '_nonce_from_c', return_value=123) as native, \
             patch.object(legacy, '_get_seed_prime_thesis', return_value=3):
            expected = pow(3, 27, tower.UINT64_MAX) & legacy.NONCE_MAX
            self.assertEqual(legacy.nonce_generate_unified_py(3, 0), expected)
            native.assert_not_called()
            self.assertEqual(legacy.get_base_nonce_source(), 'python')
            self.assertEqual(legacy.get_base_nonce_version(), 'exact-tower-v2')

    def test_backtest_and_nonce_wrapper_share_exact_seed(self):
        for seed in (3, 11, 19, 73, 109, 65537, 6700417):
            with patch.object(legacy, '_get_seed_prime_thesis', return_value=seed):
                for bits in (0, 1, 24, 64, 65):
                    direct = legacy._nonce_generate_unified_py_impl(900003, bits)
                    self.assertEqual(legacy.nonce_generate_unified_py(900003, bits), direct)
                    self.assertEqual(legacy.nonce_generate_for_backtest(900003, bits), direct)
                    self.assertTrue(0 <= direct <= legacy.NONCE_MAX)

    def test_clock_screen_matches_independent_primality(self):
        # Prime names must still mean prime after retaining legacy labels.
        def prime(n):
            return n >= 2 and all(n % d for d in range(2, math.isqrt(n)+1))
        for height in range(3000):
            candidate = legacy._clock_o1_seed_prime(height)
            if candidate is not None:
                self.assertTrue(prime(candidate), (height, candidate))


if __name__ == '__main__':
    unittest.main()
