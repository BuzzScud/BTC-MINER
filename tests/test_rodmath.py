import itertools
import unittest
from fractions import Fraction
from math import gcd, isqrt, lcm
from btcminer import rodmath as m
from btcminer.coreprimes import RADICAL


def enumerate_circle(modulus, grid):
    return sum((x*x+y*y+(x*y if grid == 'hexagonal' else 0)) % modulus == 1
               for x in range(modulus) for y in range(modulus))


class RodMathTests(unittest.TestCase):
    def test_prime_and_crt_counts_against_coordinates(self):
        for grid in ('square', 'hexagonal'):
            for p in (5, 7, 11, 19, 71, 97, 109):
                self.assertEqual(m.rod_circle_count(p, grid), enumerate_circle(p, grid))
            self.assertEqual(m.crt_circle_count((5, 7), grid), enumerate_circle(35, grid))
        for args in ((2,'square'), (3,'hexagonal'), (9,'square')):
            with self.assertRaises(ValueError):
                m.rod_circle_count(*args)
        with self.assertRaises(ValueError):
            m.crt_circle_count((7,7), 'square')

    def test_finite_prime_square_rod_scaling_instances(self):
        self.assertEqual(enumerate_circle(121,'square'),132)
        self.assertEqual(enumerate_circle(121,'hexagonal'),132)
        self.assertEqual(enumerate_circle(361,'hexagonal'),342)

    def test_shell_recurrence_against_geometric_enumeration(self):
        for d in range(5):
            for n in range(10):
                radius = isqrt(n)
                expected = sum(sum(x*x for x in point) == n for point in
                               itertools.product(range(-radius, radius+1), repeat=d))
                self.assertEqual(m.shell_count(d,n), expected)
        for n, expected in [(11,(0,24,96)), (19,(0,24,160)), (71,(0,0,576)),
                            (97,(8,48,784)), (109,(8,72,880)), (121,(4,78,1064)),
                            (209,(0,240,1920))]:
            self.assertEqual(tuple(m.shell_count(d,n) for d in (2,3,4)), expected)

    def test_towers_against_unreduced_exponents(self):
        for a in (1,7,11,19):
            for b in (1,5,7,11):
                for c in range(7):
                    self.assertEqual(m.tower3(a,b,c,360,12,2), pow(a,b**c,360))
                for c in (1,5,7):
                    for d in range(3):
                        self.assertEqual(m.tower4(a,b,c,d,360,12,2,1),pow(a,b**(c**d),360))
        for c in range(6):
            self.assertEqual(m.tower3(7,11,c,RADICAL,30240,72),pow(7,11**c,RADICAL))
        self.assertEqual(len({m.tower3(7,11,c,RADICAL,30240,72) for c in range(72)}),72)
        for args in [(2,5,3,360,12,2), (7,2,3,360,12,2), (7,5,-1,360,12,2)]:
            with self.assertRaises(ValueError):
                m.tower3(*args)
        self.assertEqual(m.tower3(1,0,0,1,1,1),0)

    def test_split_soundness_density_and_order_criterion(self):
        def order(a,p):
            return next(k for k in range(1,p) if pow(a,k,p)==1)
        for p,q in ((3,5),(7,11),(11,19),(19,31)):
            exponent=lcm(p-1,q-1)
            primes=tuple(r for r in (2,3,5,7) if exponent % r == 0)
            successful=0
            for base in range(p*q):
                factor=m.split_with(p*q,base,exponent,primes)
                if factor is not None:
                    self.assertTrue(1<factor<p*q and p*q % factor==0)
                    successful+=1
                if gcd(base,p*q)==1:
                    self.assertEqual(factor is not None,order(base,p)!=order(base,q))
            self.assertGreaterEqual(Fraction(successful,p*q),m.split_probability_lower_bound(p,q,exponent))
        self.assertEqual(m.split_probability_lower_bound(11,19,144000),Fraction(90,209))
        for args in ((209,2,144000,(2,3)),(209,2,0,(2,3,5)),(209,2,12,(4,3))):
            with self.assertRaises(ValueError):
                m.split_with(*args)
        for args in ((11,11,144000),(11,19,10),(9,19,144000)):
            with self.assertRaises(ValueError):
                m.split_probability_lower_bound(*args)

    def test_report_used_by_miner_math(self):
        from btcminer.thesis2 import report
        result=report(bytes(80))['rods_flowers_towers']
        self.assertEqual(result['factor_example']['factor'],11)
        self.assertEqual(result['tower_7_11_core_distinct_residues'],72)
        result['factor_example']['factor']=0
        self.assertEqual(m.report()['factor_example']['factor'],11)
