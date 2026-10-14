import gc
import random
import unittest
from unittest.mock import patch
from concurrent.futures import ThreadPoolExecutor
from btcminer.shared_abacus import Frame, FramePool, Calculation, shared_pool
from btcminer.research_system import fib, study_level


class SharedAbacusTests(unittest.TestCase):
    def test_signed_large_coupled_programs_and_reuse(self):
        rng=random.Random(109); calc=Calculation()
        for bits in (32,256,4096,8192,16384):
            a=-rng.getrandbits(bits); b=rng.getrandbits(bits//2)
            calc.load(0,a).load(1,b).run([('mul',2,0,1),('add',3,2,0),('sub',3,3,1)])
            self.assertEqual(calc.columns[3].value(),a*b+a-b)
            ids=[id(c._data) for c in calc.columns]
            calc.clear()
            self.assertEqual([c.value() for c in calc.columns],[0]*4)
            self.assertEqual(ids,[id(c._data) for c in calc.columns])
        self.assertGreater(calc.growths,0)

    def test_operations_match_integers(self):
        f=shared_pool().frame(512)
        for a in (-31,-1,0,1,109):
            c=[f.column(a),f.column(19),f.column(),f.column()]
            for power in (0,1,2,3,10):
                f.program([('pow',2,0,0,0,power)],c)
                self.assertEqual(c[2].value(),a**power)
            f.program([('const',2,0,0,-71),('copy',3,2),('mulc',3,3,0,-11),('addc',3,3,0,97)],c)
            self.assertEqual(c[3].value(),71*11+97)

    def test_lossless_capacity_guard_and_no_partial_mutation(self):
        f=Frame((11,19));c=[f.column(100),f.column(100),f.column()]
        with self.assertRaises(OverflowError):f.program([('mul',2,0,1)],c)
        self.assertEqual(c[2].value(),0)
        with self.assertRaises(OverflowError):f.column(500)
        with self.assertRaises(ArithmeticError):Frame((9,15))
        with self.assertRaises(ValueError):f.view((0,0))
        with self.assertRaises(ValueError):f.program([('add',2,-1,0)],c)

    def test_independent_views_merge_without_recomputing_formula(self):
        root=Frame((11,19,71,97,109));a=root.view((0,1));b=root.view((2,3,4))
        merged=a.merge(b)
        ac=[a.column(100),a.column(101),a.column()]
        bc=[b.column(100),b.column(101),b.column()]
        for frame,cols in ((a,ac),(b,bc)):
            frame.program([('mul',2,0,1)],cols,exact=False)
        with self.assertRaises(OverflowError):ac[2].value()
        self.assertEqual(ac[2].merge(bc[2],merged).value(),10100)
        self.assertEqual(root.column(100).restrict(a).value(),100)
        del root;gc.collect()
        self.assertEqual(a.column(71).value(),71)

    def test_views_shared_across_threads_have_independent_columns(self):
        root=Frame(primes=64)
        def calculate(i):
            f=root.view(range(16));c=[f.column(i+11),f.column(),f.column()]
            f.program([('pow',1,0,0,0,3),('addc',2,1,0,-109)],c)
            return c[2].value()
        with ThreadPoolExecutor(max_workers=4) as executor:
            self.assertEqual(list(executor.map(calculate,range(200))),[(i+11)**3-109 for i in range(200)])

    def test_jump_matches_stepping_and_large_modular_depth(self):
        f=shared_pool().frame(8192)
        for coefficients,initial in (((1,1),(0,1)),((3,3,-6),(1,4,12)),((-2,),(3,))):
            values=list(initial);d=len(initial)
            for n in range(d,130):values.append(sum(coefficients[j]*values[n-1-j] for j in range(d)))
            for n in (0,1,2,7,63,129):
                self.assertEqual(f.jump(coefficients,initial,n,bound=1<<1024).value(),values[n])
        huge=f.jump((1,),(7,),10**18)
        self.assertEqual(huge.residues,tuple(7%m for m in f.moduli))
        with self.assertRaises(ValueError):huge.value()
        self.assertEqual(f.jump((1,1),(0,1),8192,bound=1<<8192).value(),fib(8192)[0])

    def test_montgomery_matches_python_for_large_odd_moduli(self):
        f=Frame(primes=300)
        for bits in (31,127,521,2048,4096):
            modulus=(1<<bits)-(3 if bits==31 else 1)
            for exponent in (0,1,19,109):
                self.assertEqual(f.powmod(123456789,exponent,modulus),pow(123456789,exponent,modulus))
        for args in ((-1,3,11),(7,-1,11),(7,3,10)):
            with self.assertRaises(ValueError):f.powmod(*args)

    def test_composite_rod_coprimality_rejected(self):
        # Nonzero p % rod does not imply gcd(p,rod)=1.
        from btcminer.shared_abacus import bigint, C
        f=Frame((1000005,2147483647,2147483629));p=bigint(3);err=C.c_int()
        ptr=f._lib.lc_rmont_new(f._pointer,1,1,C.byref(p),C.byref(err))
        self.assertFalse(ptr);self.assertNotEqual(err.value,0)

    def test_resident_pool_only_rebuilds_for_growth(self):
        pool=FramePool();a=pool.frame(8192);before=pool.builds
        self.assertIs(a,pool.frame(8192));small=pool.frame(640)
        self.assertEqual(pool.builds,before)
        larger=pool.frame(16384)
        self.assertGreater(larger.capacity,a.capacity)
        self.assertEqual(a.column(109).value(),109)
        self.assertEqual(small.column(97).value(),97)

    def test_progressive_level_uses_actual_shared_backend(self):
        row=study_level(4096)
        self.assertTrue(row['ok']);self.assertGreater(row['result_bits'],4096)
        self.assertEqual(row['bitcoin_exclusions'],0)

    def test_merge_rejects_distinct_inputs_with_equal_true_ranges(self):
        root=Frame((5,7));a=root.view((0,));b=root.view((1,))
        left=root.column(8).restrict(a);right=root.column(10).restrict(b)
        self.assertEqual(left.interval,right.interval)
        with self.assertRaisesRegex(ValueError,'lineage'):left.merge(right,a.merge(b))
        with self.assertRaises(OverflowError):left.value()
        same=root.column(8)
        self.assertEqual(same.restrict(a).merge(same.restrict(b),a.merge(b)).value(),8)

    def test_independent_frames_and_in_place_programs_share_denotation(self):
        a=Frame((11,19));b=Frame((71,97));merged=a.merge(b)
        outputs=[]
        for frame in (a,b):
            c=[frame.column(8),frame.column(10)]
            frame.program([('add',0,0,1),('mul',0,0,0),('sub',0,0,1)],c,exact=False)
            outputs.append(c[0])
        self.assertEqual(outputs[0].merge(outputs[1],merged).value(),(8+10)**2-10)
        # Same result or range alone is insufficient; no general expression
        # equivalence solver is being smuggled into the structural check.
        c=[b.column(10),b.column(8)]
        b.program([('add',0,0,1),('mul',0,0,0),('sub',0,0,0)],c,exact=False)
        with self.assertRaises(ValueError):outputs[0].merge(c[0],merged)

    def test_reload_does_not_reuse_old_lineage(self):
        root=Frame((5,7));c=root.column(8);a=root.view((0,));b=root.view((1,))
        old=c.restrict(a);c.load(10);new=c.restrict(b)
        with self.assertRaisesRegex(ValueError,'lineage'):old.merge(new,a.merge(b))
        c.load(8)
        self.assertEqual(old.merge(c.restrict(b),a.merge(b)).value(),8)

    def test_column_certificate_rejects_buffer_and_epoch_mutation(self):
        f=Frame((11,19));c=f.column(8)
        c._data[0]=9
        for operation in (c.value,lambda:c.restrict(f.view((0,))),lambda:f.program([('copy',0,0)],[c])):
            with self.assertRaisesRegex(ValueError,'metadata'):operation()
        c.load(8);c._epoch+=1
        with self.assertRaisesRegex(ValueError,'metadata'):c.value()
        c.clear();self.assertEqual(c.value(),0)

    def test_interval_is_read_only_and_stale_private_interval_rejected(self):
        f=Frame((5,7));c=f.column(8)
        with self.assertRaises(AttributeError):c.interval=(0,0)
        c._interval=(0,0)
        with self.assertRaisesRegex(ValueError,'metadata'):c.value()
        c.load(8);self.assertEqual(c.value(),8)

    def test_frame_metadata_mutation_rejected(self):
        f=Frame((5,7));c=f.column(8);f.capacity=10000
        with self.assertRaisesRegex(ValueError,'Frame metadata'):c.value()

    def test_false_recurrence_bounds_rejected_without_mutating_output(self):
        f=Frame((5,7));out=f.column(8);before=out.residues
        with self.assertRaisesRegex(ValueError,'not established'):
            f.jump((1,),(35,),0,bound=0,out=out)
        self.assertEqual(out.residues,before);self.assertEqual(out.value(),8)
        with self.assertRaisesRegex(ValueError,'not established'):
            Frame((23,)).jump((3,2),(1,4),2,bound=11)

    def test_absolute_recurrence_bound_all_orders_and_saturated_depth(self):
        rng=random.Random(71109);f=shared_pool().frame(512)
        for d in range(1,9):
            coefficients=tuple(rng.randrange(-2,3) for _ in range(d))
            initial=tuple(rng.randrange(-3,4) for _ in range(d))
            exact=list(initial);majorant=list(map(abs,initial))
            for n in range(d,24):
                exact.append(sum(coefficients[j]*exact[n-1-j] for j in range(d)))
                majorant.append(sum(abs(coefficients[j])*majorant[n-1-j] for j in range(d)))
            for n in (0,d-1,d,23):
                self.assertEqual(f.jump(coefficients,initial,n,bound=majorant[n]).value(),exact[n])
        depth=(1<<64)-1
        self.assertEqual(f.jump((1,),(7,),depth,bound=7).value(),7)
        self.assertEqual(f.jump((0,0),(7,-5),depth,bound=0).value(),0)
        with self.assertRaisesRegex(ValueError,'not established'):f.jump((2,),(1,),depth,bound=100)

    def test_cancellation_bound_requires_additional_justification(self):
        f=Frame((11,19))
        # u_n=2u_(n-1)-u_(n-2)=1, but its absolute companion grows.
        with self.assertRaisesRegex(ValueError,'not established'):f.jump((2,-1),(1,1),20,bound=1)
        modular=f.jump((2,-1),(1,1),20)
        self.assertEqual(modular.residues,(1,1))
        with self.assertRaises(ValueError):modular.value()

    def test_distributed_recurrences_require_identical_model(self):
        a=Frame((11,19));b=Frame((71,97));merged=a.merge(b)
        ca=a.jump((1,1),(0,1),10,bound=60)
        cb=b.jump((1,1),(0,1),10,bound=60)
        self.assertEqual(ca.merge(cb,merged).value(),55)
        different=b.jump((1,),(55,),10,bound=60)
        with self.assertRaisesRegex(ValueError,'lineage'):ca.merge(different,merged)

    def test_native_partial_failure_invalidates_written_destinations(self):
        f=Frame((11,19));c=[f.column(8),f.column(10)]
        def broken_run(frame,ops,count,slots,nslots):
            slots[1][0]=123
            return 1
        with patch.object(f._lib,'lc_abacus_run',side_effect=broken_run):
            with self.assertRaises(ArithmeticError):f.program([('add',1,0,1)],c)
        self.assertEqual(c[0].value(),8)
        with self.assertRaisesRegex(ValueError,'metadata'):c[1].value()
        c[1].clear();self.assertEqual(c[1].value(),0)

    def test_native_partial_jump_failure_cannot_reuse_prior_bound(self):
        f=Frame((11,19));c=f.column(8)
        def broken_jump(frame,data,*args):
            data[0]=123
            return 1
        with patch.object(f._lib,'lc_abacus_linrec',side_effect=broken_jump):
            with self.assertRaises(ArithmeticError):f.jump((1,),(7,),10,bound=7,out=c)
        with self.assertRaisesRegex(ValueError,'metadata'):c.value()

    def test_reserve_preserves_expression_lineage(self):
        calc=Calculation(bits=64);calc.load(0,11).load(1,19).run([('mul',2,0,1)])
        old=calc.columns[2]._lineage
        calc.reserve(512)
        self.assertIs(calc.columns[2]._lineage,old)
        self.assertEqual(calc.columns[2].value(),209)

    def test_deep_self_alias_dag_avoids_recursive_structural_comparison(self):
        a=Frame((11,19));b=Frame((71,97));outputs=[]
        for frame in (a,b):
            c=[frame.column(1)]
            frame.program([('addc',0,0,0,1)]*1500,c,exact=False)
            outputs.append(c[0])
        self.assertEqual(outputs[0].merge(outputs[1],a.merge(b)).value(),1501)

    def test_unit_powers_preserve_small_capacity(self):
        frame=Frame((11,19))
        for value in (-1,0,1):
            for exponent in (0,999999,1000000):
                columns=[frame.column(value),frame.column()]
                frame.program([('pow',1,0,0,0,exponent)],columns)
                self.assertEqual(columns[1].value(),value**exponent)
        calc=Calculation(bits=64);calc.load(0,1)
        original=calc.frame
        calc.run([('pow',1,0,0,0,1000000)])
        self.assertIs(calc.frame,original)
        self.assertEqual(calc.columns[1].value(),1)


if __name__=='__main__':unittest.main()
