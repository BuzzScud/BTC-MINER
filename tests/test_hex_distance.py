"""Independent integer oracle and ABI boundary checks for E-coordinate distance."""
import ctypes as C
import random
import unittest
from btcminer.archive_math import hex_distance
from btcminer.shared_abacus import library


class HexDistanceTests(unittest.TestCase):
    def test_arbitrary_precision_and_coordinate_convention(self):
        points=[(0,0),(1,0),(1,1),(0,1),(-1,0),(-1,-1),(0,-1),(1,-1),(3,-2)]
        rng=random.Random(19)
        for bits in (64,127,512,4097,9000):
            a,b=rng.getrandbits(bits),rng.getrandbits(bits)
            points.extend((s*a,t*b) for s in (-1,1) for t in (-1,1))
        for a,b in points:
            with self.subTest(a_bits=abs(a).bit_length(),b_bits=abs(b).bit_length()):
                self.assertEqual(hex_distance(a,b),max(abs(a),abs(b),abs(a-b)))
        self.assertEqual(hex_distance(1,1),1)
        self.assertEqual(hex_distance(1,-1),2)
        for value in (True,1.5,'19'):
            with self.assertRaises(ValueError):hex_distance(value,0)

    def test_full_signed_input_abi_without_overflow(self):
        lib=library()
        exact=lib.lc_eis_hexdist_u64; exact.restype=C.c_uint64
        exact.argtypes=[C.c_int64,C.c_int64]
        legacy=lib.lc_eis_hexdist_i64; legacy.restype=C.c_int64
        legacy.argtypes=exact.argtypes
        extremes=(-(1<<63),-(1<<63)+1,-1,0,1,(1<<63)-2,(1<<63)-1)
        for a in extremes:
            for b in extremes:
                expected=max(abs(a),abs(b),abs(a-b))
                self.assertEqual(exact(a,b),expected)
                self.assertEqual(legacy(a,b),expected if expected < 1<<63 else -1)


if __name__=='__main__':unittest.main()
