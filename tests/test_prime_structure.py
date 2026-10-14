import unittest
from itertools import product
from math import gcd
from btcminer.prime_structure import PERIODS, unit_coordinates, unit_from_coordinates
from btcminer.coreprimes import report
from btcminer.thesis2 import board_loop, Traversal


class PrimeStructureTests(unittest.TestCase):
    def test_complete_basis_and_group_composition(self):
        coordinates=list(product(*(range(n) for n in PERIODS)))
        values=[unit_from_coordinates(c) for c in coordinates]
        self.assertEqual(set(values),{x for x in range(360) if gcd(x,360)==1})
        self.assertEqual(len(set(values)),96)
        for c,v in zip(coordinates,values):self.assertEqual(unit_coordinates(v),c)
        for a,u in zip(coordinates,values):
            for b,v in zip(coordinates,values):
                composed=tuple((x+y)%n for x,y,n in zip(a,b,PERIODS))
                self.assertEqual(unit_from_coordinates(composed),u*v%360)

    def test_every_admitted_step_preserves_complete_board_traversal(self):
        field=board_loop()
        self.assertEqual(len(set(field)),360)
        expected={(a,b) for a in range(19) for b in range(19)}-{(0,0)}
        for step in range(360):
            if gcd(step,360)==1:
                self.assertEqual({field[(17+k*step)%360] for k in range(360)},expected)
            else:
                with self.assertRaises(ValueError):unit_coordinates(step)
        for invalid in (True,1.0,'19',-1,361):
            with self.assertRaises(ValueError):unit_coordinates(invalid)

    def test_clock_carriers_remain_distinct(self):
        rows={r['prime']:r for r in report()['classification']}
        self.assertEqual(rows[19]['square_norm_one_group_order'],20)
        self.assertEqual(rows[19]['hex_norm_one_group_order'],18)
        self.assertEqual(rows[71]['integer_unit_group_order'],70)
        self.assertEqual(rows[71]['hex_norm_one_group_order'],72)
        self.assertFalse(rows[71]['qualifies_for_miner_clock'])
        self.assertTrue(rows[71]['hex_power_lands_in_petals'])

    def test_traversal_prime_selector_rejects_noninteger_values(self):
        for value in (19.0, True, '19', None):
            with self.subTest(value=value):
                with self.assertRaises(ValueError):Traversal(bytes(80), prime=value)


if __name__=='__main__':unittest.main()
