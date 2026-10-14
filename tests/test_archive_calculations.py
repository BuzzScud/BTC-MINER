import math
import random
import unittest
from btcminer.shared_abacus import Frame
from btcminer.claim_calculus import ClaimCalculator, count_polynomial_roots
from btcminer.archive_math import integer_operation, recover_from_k, order_split, Flower, backend, ramanujan_coefficients


class ArchiveCalculations(unittest.TestCase):
    def test_natural_subtraction_keeps_truncation(self):
        calc=ClaimCalculator()
        for x in range(8):
            for y in range(8):
                result=calc.decide(('eq',('nsub',x,y),max(0,x-y)))
                self.assertTrue(result['truth'])
                self.assertEqual(result['readbacks'],2)
        with self.assertRaises(ValueError):calc.decide(('eq',('nsub',-1,2),0))

    def test_circle_geometry_and_large_translations(self):
        from btcminer.archive_math import CircleModel
        model=CircleModel((1,0,1))
        for circle,expected in [((1,0,1),'crossing'),((2,0,1),'tangent'),((3,0,1),'apart'),((0,0,1),'coincident_circle')]:
            self.assertEqual(model.pair((0,0,1),circle)['relation'],expected)
        self.assertFalse(model.triple((0,0,1),(1,0,1),(2,0,1))['applicable'])
        rng=random.Random(1971)
        for form in ((1,0,1),(1,1,1),(2,-1,3)):
            model=CircleModel(form);a,b,c=form
            for _ in range(15):
                point=(rng.randrange(-11,12),rng.randrange(-11,12))
                centers=((0,0),(3,0),(0,5))
                circles=[(x,y,a*(point[0]-x)**2+b*(point[0]-x)*(point[1]-y)+c*(point[1]-y)**2) for x,y in centers]
                for offset in (0,(1<<4096)+109):
                    shifted=[(x+offset,y-offset,r) for x,y,r in circles]
                    result=model.triple(*shifted)
                    self.assertTrue(result['concurrent'])
                    self.assertEqual(result['radical_centre'],(point[0]+offset,point[1]-offset))
                    bad=list(shifted);x,y,r=bad[-1];bad[-1]=(x,y,r+1)
                    result=model.triple(*bad);px,py=result['radical_centre']
                    direct=all(a*(px-x)**2+b*(px-x)*(py-y)+c*(py-y)**2==r for x,y,r in bad)
                    self.assertEqual(result['concurrent'],direct)
        for form in ((0,0,1),(1,3,1)):
            with self.assertRaises(ValueError):CircleModel(form)

    def test_packed_clock_symmetries_and_flags(self):
        from btcminer.archive_math import clock_flags
        generators,group,flags=clock_flags()
        self.assertEqual(len(group),1152*24)
        self.assertEqual(len(flags),1152*4)
        self.assertEqual(len(set(flags[i:i+4] for i in range(0,len(flags),4))),1152)
        identity=bytes(range(24))
        for generator in generators:
            self.assertEqual(bytes(generator[i] for i in generator),identity)
        for i in range(0,len(group),24):self.assertEqual(bytes(sorted(group[i:i+24])),identity)
        self.assertIs(clock_flags()[1],group)

    def test_complete_clock_geometry_paths(self):
        from btcminer.archive_math import clock_geometry
        roots,cells=clock_geometry()
        def rotate(v,n):
            for _ in range(n):
                a,b,c,d=v;v=(-d,a,b+d,c)
            return v
        orbit={rotate((1,0,0,0),n) for n in range(12)}
        for v in roots:
            step=1 if v in orbit else 5
            self.assertEqual(rotate(v,step*12),v)
            self.assertEqual(len({rotate(v,step*k) for k in range(12)}),12)
            for k in range(12):
                points=[rotate(v,step*(k+j)) for j in range(5)]
                self.assertTrue(any(set(points[:4])<=c for c in cells))
                self.assertFalse(any(set(points)<=c for c in cells))

    def test_periodic_clock_matches_independent_repeated_rotation(self):
        from btcminer.archive_math import Clock24
        clock=Clock24(); v=((1<<8192)-11,-19,71,-109); direct=v
        for depth in range(121):
            self.assertEqual(clock.rotate(v,depth),direct)
            a,b,c,d=direct;direct=(-d,a,b+d,c)
        enormous_depth=(1<<16384)+97
        self.assertEqual(clock.rotate(v,enormous_depth),clock.rotate(v,enormous_depth%12))
        self.assertIs(clock.tables,Clock24().tables)

    def test_theorem_instantiation_preserves_domain_and_premise(self):
        from btcminer.theorem_calculations import instantiate
        entry={'theorem':'example','supported':True,'proof_check':'passed',
               'variables':[{'name':'n','domain':'Nat'}],
               'premises':[['le',1,'n']],'conclusion':['le',1,['mul','n','n']]}
        self.assertTrue(instantiate(entry,{'n':19})['result']['truth'])
        self.assertFalse(instantiate(entry,{'n':0})['applicable'])
        self.assertIsNone(instantiate(entry,{'n':0})['result'])
        for values in ({'n':-1},{'n':True},{'n':19,'x':1},{},[],None):
            with self.assertRaises(ValueError):instantiate(entry,values)
        with self.assertRaises(ValueError):instantiate(dict(entry,proof_check='pending'),{'n':1})

    def test_ramanujan_against_independent_divisor_recurrence(self):
        tau=ramanujan_coefficients(60)
        sigma=lambda n,k:sum(d**k for d in range(1,n+1) if n%d==0)
        oracle=[1]
        for n in range(1,60):
            numerator=-24*sum(sigma(k,1)*oracle[n-k] for k in range(1,n+1))
            self.assertEqual(numerator%n,0);oracle.append(numerator//n)
        self.assertEqual(tau,oracle)
        for n,t in enumerate(tau,1):
            self.assertEqual((t-sigma(n,11))%691,0)
            self.assertEqual((t-n*sigma(n,3))%7,0)
        frame=Frame((16,9,5,7,13))
        coeff=[0]*17;coeff[4]=-1;coeff[16]=1
        self.assertEqual(count_polynomial_roots(frame,coeff)['count'],65520)

    def test_sha_carries_on_shared_model(self):
        from btcminer.research_system import audit_sha_carries
        self.assertEqual(audit_sha_carries(32,64)['integer_claims_checked'],312)

    def test_claims_against_direct_integer_semantics_and_reuse(self):
        calc=ClaimCalculator(); generator=random.Random(110197)
        data_ids=[id(c._data) for c in calc.calculation.columns]
        for _ in range(100):
            a=generator.randrange(-100000,100000); b=generator.randrange(-100000,100000)
            variables={'a':a,'b':b}
            expression=('sub',('mul','a','a'),('mul','b','b'))
            n=a*a-b*b
            for claim,expected in [(('eq',expression,n),True),(('le',expression,0),n<=0),
                                   (('dvd',11,expression),n%11==0),(('dvd',13,expression),n%13==0),
                                   (('not',('eq',expression,n+1)),True)]:
                self.assertEqual(calc.decide(claim,variables)['truth'],expected)
        self.assertEqual(data_ids,[id(c._data) for c in calc.calculation.columns])
        self.assertEqual(calc.decide(('dvd',11,121))['readbacks'],0)
        self.assertEqual(calc.decide(('le',-1,0))['readbacks'],1)
        self.assertEqual(calc.decide(('dvd',13,26))['readbacks'],1)

    def test_capacity_alias_does_not_pass_equality(self):
        calc=ClaimCalculator(); capacity=calc.calculation.frame.capacity
        self.assertFalse(calc.decide(('eq',capacity,0))['truth'])
        self.assertTrue(calc.decide(('eq',('pow',2,8192),1<<8192))['truth'])

    def test_crt_counts_match_complete_domain_enumeration(self):
        frame=Frame((4,9,5))
        for coeff in ((-1,0,1),(0,-1,1),(3,4,5,6),(0,)):
            expected=sum(sum(c*x**i for i,c in enumerate(coeff))%frame.capacity==0 for x in range(frame.capacity))
            self.assertEqual(count_polynomial_roots(frame,coeff)['count'],expected)
        with self.assertRaises(ValueError):count_polynomial_roots(Frame((10009,)),(1,1))

    def test_native_large_arithmetic(self):
        a=(1<<8192)-19; b=(1<<4096)+71
        for op, expected in [('add',a+b),('sub',a-b),('mul',a*b),('gcd',math.gcd(a,b)),('lcm',math.lcm(a,b))]:
            self.assertEqual(integer_operation(op,a,b),expected)
        self.assertEqual(integer_operation('sqrt',a*a+1),a)
        self.assertEqual(integer_operation('powmod',109,97,b),pow(109,97,b))
        self.assertEqual(integer_operation('invmod',19,65520),pow(19,-1,65520))
        with self.assertRaises(ArithmeticError):integer_operation('invmod',3,9)
        with self.assertRaises(ValueError):integer_operation('powmod',2,-1,17)

    def test_conditional_factor_recovery(self):
        primes=[n for n in range(2,150) if all(n%d for d in range(2,math.isqrt(n)+1))]
        for i,p in enumerate(primes):
            for q in primes[i:]:self.assertEqual(recover_from_k(p*q,math.lcm(p-1,q-1)),(p,q))
        result=order_split(11*19,2,90,(2,3,5))
        g,h,k=result['factors_and_k']
        self.assertEqual(g*h,209);self.assertEqual(k,90)
        self.assertIsNone(recover_from_k(209,1))

    def test_persistent_flower_signed_large_coordinates(self):
        flower=Flower(2); table=flower.base.digit
        pointer=__import__('ctypes').cast(table,__import__('ctypes').c_void_p).value
        for a,b in [(0,0),(-19,71),((1<<8192)-109,-(1<<4096)+97)]:
            self.assertEqual(flower.address(a,b,33)['restored'],(a,b))
        self.assertEqual(pointer,__import__('ctypes').cast(flower.base.digit,__import__('ctypes').c_void_p).value)

    def test_binary_dial(self):
        lib=backend()
        for w in (11,12,33,63):
            for x in (0,11,19,71,97,109,(1<<64)-1):
                self.assertEqual(lib.lc_mersenne_mod(x,w),x%((1<<w)-1))
        for p in (11,19,71,97,109):
            self.assertEqual(lib.lc_dial12_inv(p),pow(p,-1,65520) if math.gcd(p,65520)==1 else 0)


if __name__=='__main__':unittest.main()
