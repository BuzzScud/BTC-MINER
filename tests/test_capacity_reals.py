import random
import unittest
from fractions import Fraction

from btcminer.capacity_reals import (
    CapacityError, CapacityReals, DomainIndeterminate, Expr, RodInterval,
)


class CapacityRealTests(unittest.TestCase):
    def service(self, width=256, base=60):
        middle = 1 << width
        return CapacityReals((middle-1, middle, middle+1), base)

    def test_plan_is_exact_at_last_admitted_scale(self):
        for width in (2, 8, 31, 128, 1024):
            service = self.service(width)
            a = Expr.rational(Fraction(17, 3))
            for expr in (a, a*a, a.sqrt(), (a-a).scale(Fraction(-2, 7))):
                try:
                    plan = service.plan(expr)
                except CapacityError:
                    with self.assertRaises(CapacityError):
                        service.enclose(expr, 0)
                    continue
                if plan.max_places >= 0:
                    self.assertLess(2*plan.bound_at(plan.max_places), plan.capacity)
                    service.enclose(expr, plan.max_places)
                self.assertGreaterEqual(2*plan.bound_at(plan.max_places+1), plan.capacity)
                with self.assertRaises(CapacityError):
                    service.enclose(expr, plan.max_places+1)

    def test_random_rational_dags_enclose_exact_fraction(self):
        rng = random.Random(10919)
        service = self.service(512)
        for _ in range(80):
            values = [Fraction(rng.randrange(-100, 101), rng.randrange(1, 30)) for _ in range(3)]
            a, b, c = map(Expr.rational, values)
            expr = ((a+b)*c-a).scale(Fraction(-3, 19))
            exact = ((values[0]+values[1])*values[2]-values[0])*Fraction(-3, 19)
            for places in (0, 1, 3, 9):
                lo, hi = service.endpoints(service.enclose(expr, places))
                self.assertLessEqual(Fraction(lo, 60**places), exact)
                self.assertGreaterEqual(Fraction(hi, 60**places), exact)
            read = service.read(expr, 3)
            if read.certified:
                self.assertEqual(read.lower, (exact*60**3).__floor__())
            else:
                self.assertLessEqual(read.lower, (exact*60**3).__floor__())
                self.assertGreaterEqual(read.upper, (exact*60**3).__floor__())

    def test_sqrt_certificate_matches_independent_integer_root_inequality(self):
        service = self.service(1024)
        for value in (0, 1, 2, 5, 19, 361, 1 << 270):
            for places in (0, 1, 12):
                read = service.read(Expr.rational(value).sqrt(), places)
                self.assertTrue(read.certified)
                n = value * 60**(2*places)
                self.assertLessEqual(read.lower**2, n)
                self.assertGreater((read.lower+1)**2, n)

    def test_negative_rounding_and_shared_denominator_rods(self):
        service = CapacityReals((7, 11, 19, 73, 109))
        expr = Expr.rational(1).scale(Fraction(-1, 7))
        result = service.read(expr, 1)
        self.assertTrue(result.certified)
        self.assertEqual(result.lower, -9)  # floor(-60/7), not truncation.
        lo, hi = service.endpoints(service.enclose(expr, 1))
        self.assertEqual((lo, hi), (-9, -8))

    def test_unresolved_boundary_is_not_claimed_integer(self):
        service = self.service(32)
        phi = (Expr.rational(1)+Expr.rational(5).sqrt()).scale(Fraction(1, 2))
        result = service.read(phi*phi-phi-Expr.rational(1), 0)
        self.assertFalse(result.certified)
        self.assertEqual(result.status, 'uncertified_at_capacity')
        self.assertLessEqual(result.lower, 0)
        self.assertGreaterEqual(result.upper, 0)
        # A noninteger near the boundary may have the same failed status.
        perturbed = phi*phi-phi-Expr.rational(1)+Expr.rational(Fraction(1, 60**30))
        other = service.read(perturbed, 0)
        self.assertEqual(other.status, 'uncertified_at_capacity')

    def test_budget_is_separate_from_capacity(self):
        service = self.service(128)
        expr = Expr.rational(2).sqrt()
        limited = service.read(expr, 2, max_stages=1)
        self.assertEqual(limited.status, 'stage_budget_exhausted')
        self.assertGreater(limited.max_places, limited.working_places)
        self.assertTrue(service.read(expr, 2).certified)

    def test_intermediate_bound_prevents_wrapped_product(self):
        service = CapacityReals((11, 19, 73, 109))
        a = Expr.rational(100)
        expr = a*a-a*a
        plan = service.plan(expr)
        self.assertEqual(plan.quadratic, 10000)
        with self.assertRaises(CapacityError):
            service.enclose(expr, 1)
        # The final value is zero, but that alone cannot justify decoding products.
        self.assertTrue(service.read(expr, 0).certified)

    def test_deep_dag_uses_no_recursive_expression_walk(self):
        service = self.service(128)
        expr = Expr.rational(1)
        for _ in range(5000):
            expr = -expr
        result = service.read(expr, 0)
        self.assertTrue(result.certified)
        self.assertEqual(result.lower, 1)

    def test_repeated_squaring_rejected_before_huge_bound_allocation(self):
        service = self.service(16)
        expr = Expr.rational(2)
        for _ in range(1000):
            expr = expr*expr
        with self.assertRaises(CapacityError):
            service.plan(expr)

    def test_malformed_inputs_frame_alias_and_domain_fail_closed(self):
        for rods in ((), (7, 7), (6, 9), (True, 7)):
            with self.assertRaises((ValueError, TypeError)):
                CapacityReals(rods)
        with self.assertRaises(TypeError):
            Expr.rational(0.1)
        service = self.service(16)
        with self.assertRaises(DomainIndeterminate):
            service.enclose(Expr.rational(-1).sqrt(), 0)
        sample = service.enclose(Expr.rational(1), 0)
        bad = RodInterval(tuple(reversed(sample.rods)), 0, 60, sample.lower, sample.upper)
        with self.assertRaises(ValueError):
            service.endpoints(bad)
        bad = RodInterval(sample.rods, 0, 60, (sample.rods[0], 0, 0), sample.upper)
        with self.assertRaises(ValueError):
            service.endpoints(bad)
        with self.assertRaises(ValueError):
            service.read(Expr.rational(1), 0, max_stages=0)

    def test_frame_extension_reevaluates_at_more_places(self):
        small, large = self.service(16), self.service(64)
        expr = Expr.rational(19).sqrt()
        self.assertLess(small.plan(expr).max_places, large.plan(expr).max_places)
        with self.assertRaises(ValueError):
            large.endpoints(small.enclose(expr, 0))
        self.assertTrue(large.read(expr, small.plan(expr).max_places+1).certified)


if __name__ == '__main__':
    unittest.main()
