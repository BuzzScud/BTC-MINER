import ctypes as C
import random
import unittest
from unittest.mock import patch

from btcminer.diagnostics import GENESIS, self_test
from btcminer.native import Hasher, hash256, U80, U32
from btcminer.settings import DEFAULTS


class NativeTests(unittest.TestCase):
    def test_selected_hasher_passes_consensus_and_scanner_checks(self):
        result = self_test(DEFAULTS)
        self.assertTrue(result["ok"], result)

    def test_python_fallback_passes_same_checks(self):
        result = self_test(dict(DEFAULTS, native_hasher=False))
        self.assertTrue(result["ok"], result)
        self.assertFalse(result["native_available"])

    def test_require_native_does_not_silently_pass_fallback(self):
        with patch("btcminer.native.C.CDLL", side_effect=OSError("unavailable")):
            result = self_test(DEFAULTS, require_native=True)
        self.assertFalse(result["ok"])

    def test_native_full_hash_matches_independent_hashlib(self):
        hasher = Hasher()
        if hasher.lib is None:
            self.skipTest(hasher.reason)
        fn = hasher.lib.double_sha256
        fn.argtypes = [C.POINTER(C.c_uint8), C.POINTER(C.c_uint8)]
        fn.restype = None
        rng = random.Random(17)
        for header in [GENESIS] + [bytes(rng.getrandbits(8) for _ in range(80)) for _ in range(100)]:
            result = U32()
            fn(U80(*header), result)
            self.assertEqual(bytes(result), hash256(header))

    def test_python_cancellation_reports_zero_attempts(self):
        self.assertEqual(Hasher(False).scan(GENESIS, 1, start=0, count=512,
                                           stop=lambda: True), (0, None))

    def test_invalid_header_target_and_batch_are_rejected(self):
        hasher = Hasher()
        for header, target, count in ((bytes(79), 1, 1), (GENESIS, -1, 1),
                                      (GENESIS, 1 << 256, 1), (GENESIS, 1, 0),
                                      (GENESIS, 1, 1000001)):
            with self.subTest(target=target, count=count), self.assertRaises(ValueError):
                hasher.scan(header, target, start=0, count=count)
