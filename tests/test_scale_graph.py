import ctypes as C
import itertools
from array import array
from collections import Counter
from fractions import Fraction
import random
import struct
import unittest

from btcminer.scale_graph import Frame, FormulaValue, Column, traversal_trace
from btcminer.archive_math import Flower, flower_boundary, flower_nonce_labels
from btcminer.thesis2 import Traversal, OffsetDescriptor, qualifying_primes, board_loop, BIG_CLOCK
from btcminer.native import Hasher
from btcminer.diagnostics import GENESIS
from btcminer.rodmath import prime_power_circle_count, finite_dynamics


class ScaleGraphTests(unittest.TestCase):
    def test_projection_fibres_and_capacity_for_all_small_depths(self):
        for depths in itertools.product(range(4),repeat=3):
            shallow=Frame((2,3,5),depths)
            for i,b in enumerate(shallow.bases):
                deep=shallow.deepen(i)
                self.assertEqual(deep.capacity,shallow.capacity*b)
                for r in range(shallow.moduli[i]):
                    fibre=shallow.fibre(i,r)
                    self.assertEqual(len(fibre),b)
                    self.assertEqual({x%shallow.moduli[i] for x in fibre},{r})
                for n in (-999,-1,0,1,999,2**80+123):
                    self.assertEqual(deep.encode(n).project(shallow),shallow.encode(n))

    def test_formula_projection_and_signed_unique_readback(self):
        formula=('sub',('pow',('add','x',17),3),('mul','x','y'))
        rng=random.Random(361)
        for _ in range(100):
            x,y=rng.randrange(-1000,1001),rng.randrange(-1000,1001)
            env={'x':x,'y':y}; bounds={'x':(-1000,1000),'y':(-1000,1000)}
            shallow=Frame((2,3,5),(3,2,1)); deep=Frame((2,3,5),(16,10,8))
            a=deep.evaluate(formula,env,bounds)
            self.assertEqual(a.readback(),(x+17)**3-x*y)
            self.assertEqual(a.project(shallow).residues,shallow.evaluate(formula,env,bounds).residues)
            with self.assertRaises(ValueError):a.project(shallow).readback()
        # Two integers have the same shallow residues; refinement must use inputs.
        self.assertEqual(shallow.encode(1).residues,shallow.encode(361).residues)
        self.assertNotEqual(deep.encode(1).residues,deep.encode(361).residues)
        with self.assertRaises(ValueError): shallow.encode(1).project(deep)
        with self.assertRaises(ArithmeticError): Column(shallow,(2,2,2),(0,1)).readback()

    def test_magnitude_scale_is_independent_of_modulus_depth(self):
        frame=Frame((2,3,5),(12,8,6)); f=FormulaValue(('add','x',2),60)
        env={'x':19}; bounds={'x':(0,100)}
        self.assertEqual(f.value(frame,env,bounds),Fraction(7,20))
        self.assertEqual(f.rescale(60).value(frame,env,bounds),Fraction(7,20))
        self.assertEqual(f.multiply(f).value(frame,env,bounds),Fraction(49,400))
        self.assertEqual(frame.capacity,2**12*3**8*5**6)
        for bases,depths in (((2,4),(1,1)),((2,3),(-1,1)),((True,3),(1,1))):
            with self.assertRaises(ValueError): Frame(bases,depths)
        with self.assertRaises(ValueError): frame.evaluate('x',{'x':101},bounds)

    def test_arbitrary_precision_by_depth_not_fixed_word_truncation(self):
        n=10**200+123
        shallow=Frame((2,3,5),(1,1,1)); deep=Frame((2,3,5),(700,1,1))
        f=FormulaValue(('add','x',1)); inputs={'x':n}; bounds={'x':(0,2*n)}
        with self.assertRaises(ValueError): f.value(shallow,inputs,bounds)
        self.assertEqual(f.value(deep,inputs,bounds),n+1)


class FlowerIntegrationTests(unittest.TestCase):
    def test_geometric_address_classes_match_native_address_roundtrip(self):
        f=Flower(2)
        ds=[tuple(x) for x in f.base.digit[:19]]
        self.assertEqual(len(set(ds)),19)
        classes=set()
        for a,b in ds:
            for c,d in ds:
                z=(a+5*c-2*d,b+2*c+3*d)
                address=f.address(*z,depth=2)
                self.assertEqual(address['digits'],[[a,b],[c,d]])
                self.assertEqual(address['remainder'],(0,0))
                classes.add((z[0]+292*z[1])%361)
        self.assertEqual(classes,set(range(361)))
        self.assertEqual(set(flower_nonce_labels()),set(range(360)))
        # The nonzero quotient includes all 18 multiples of 19; none are filtered.
        self.assertEqual(sum((n+1)%19==0 for n in flower_nonce_labels()),18)
        self.assertNotEqual(tuple(a+19*b-1 for a,b in board_loop()),flower_nonce_labels())

    def test_boundary_matrix_by_all_digit_differences(self):
        units=((1,0),(1,1),(0,1),(-1,0),(-1,-1),(0,-1))
        for k in range(1,15):
            ds={(a,b) for a in range(-k,k+1) for b in range(-k,k+1) if max(abs(a),abs(b),abs(a-b))<=k}
            diffs=Counter((a-c,b-d) for a,b in ds for c,d in ds)
            beta=(2*k+1,k); M=[]
            for a,b in units:
                x,y=beta[0]*a-beta[1]*b,beta[0]*b+beta[1]*a-beta[1]*b
                M.append([diffs[(x-c,y-d)] for c,d in units])
            result=flower_boundary(k)
            self.assertEqual(M,result['contact_matrix'])
            self.assertEqual(set(map(sum,M)),{2*k+1})
        for k in (0,-1,True,1.5):
            with self.assertRaises(ValueError):flower_boundary(k)

    def test_conic_counts_and_finite_graphs(self):
        for p in (3,5,7):
            for j in (1,2):
                m=p**j
                for grid in ('square','hexagonal'):
                    counts=Counter((a*a+b*b+(a*b if grid=='hexagonal' else 0))%m for a in range(m) for b in range(m))
                    for c in range(1,m):
                        if c%p:self.assertEqual(prime_power_circle_count(p,j,grid,c),counts[c])
        with self.assertRaises(ValueError):prime_power_circle_count(2,2,'square')
        with self.assertRaises(ValueError):prime_power_circle_count(3,2,'hexagonal',3)
        dyn=finite_dynamics(); self.assertEqual(dyn['multiply19_mod7200_cycles'],{1:18,2:171,4:90,8:90,10:144,20:72,40:72})
        self.assertEqual(dyn['squaring_graphs'][-1],{'modulus':360,'cyclic_nodes':16,'image_size':36})

    def test_descriptors_reject_invalid_and_preserve_both_orders(self):
        for order in ('field','flower'):
            for step,prime in ((1,7),(7,19),(359,24001)):
                plan=Traversal(GENESIS,step,prime,order=order)
                desc=OffsetDescriptor.from_packed(plan.descriptor.packed())
                self.assertEqual(len(desc.packed()),24)
                self.assertEqual(desc.order,order)
                self.assertEqual([desc.offset(i) for i in range(144000)],list(plan.iter_offsets()))
                self.assertEqual(set(plan.iter_offsets()),set(range(144000)))
                for i in (0,1,359,360,143999):
                    trace=traversal_trace(plan.phase,plan.cell_phase,prime,plan.residues,i)
                    self.assertEqual(trace['offset'],desc.offset(i))
                    self.assertLess(trace['readback_bound'][1],trace['deep_frame']['capacity'])
        for data in (b'',bytes(23),bytes(24),struct.pack('<6I',3,0,0,0,7,19),struct.pack('<6I',1,0,0,0,6,19),struct.pack('<6I',1,0,0,0,7,20)):
            with self.assertRaises(ValueError): OffsetDescriptor.from_packed(data)
        for prime in qualifying_primes():
            plan=Traversal(bytes(80),prime=prime,order='flower')
            self.assertEqual(len(set(plan.iter_offsets())),144000)

    def test_native_rod_program_matches_python_at_partial_and_final_boundaries(self):
        h=Hasher()
        self.assertIsNotNone(h.fill_factored,'New traversal native export is required for this test')
        for order in ('field','flower'):
            plan=Traversal(GENESIS,order=order)
            self.assertIsNone(plan._offsets)
            expected=list(itertools.islice(plan.nonces(),10000))
            actual=list(next(h.traversal_batches(plan,10000))['nonces'])
            self.assertEqual(actual,expected);self.assertIsNone(plan._offsets)
            labels=(C.c_uint16*360).from_buffer(plan.residues)
            for first in (0,29825,29826):
                partial=(29826-first)%29827
                positions={0,1,359,360,143999,partial*144000,max(0,partial*144000-64),(partial+1)*144000-64,29827*144000-64,29827*144000}
                for pos in positions:
                    cursor=C.c_uint64(pos); out=(C.c_uint32*256)()
                    count=h.fill_factored(labels,plan.phase,plan.cell_phase,plan.prime,first,C.byref(cursor),256,out)
                    at=pos; reference=[]
                    while at<29827*144000 and len(reference)<256:
                        turn,index=divmod(at,144000); nonce=((first+turn)%29827)*144000+plan.descriptor.offset(index); at+=1
                        if nonce<2**32:reference.append(nonce)
                    self.assertEqual(list(out[:count]),reference);self.assertEqual(cursor.value,at)
            # Native absence must preserve the selected flower order as well.
            h.fill_factored=None
            self.assertEqual(list(next(h.traversal_batches(plan,10000))['nonces']),expected)
            h=Hasher()

    def test_native_rod_formulas_match_complete_tiles_at_parameter_extremes(self):
        h=Hasher(); self.assertIsNotNone(h.fill_factored)
        for order in ('field','flower'):
            for args in ((0,0,0,1,7),(143999,359,399,359,24001),(42424,123,37,7,19),
                         (143999,0,399,1,4294967291)):
                desc=OffsetDescriptor(*args,order=order); residues=desc.residues()
                labels=(C.c_uint16*360).from_buffer(residues)
                out=(C.c_uint32*144000)(); cursor=C.c_uint64(0)
                count=h.fill_factored(labels,desc.phase,desc.cell_phase,desc.prime,0,C.byref(cursor),144000,out)
                self.assertEqual(count,144000);self.assertEqual(cursor.value,144000)
                self.assertEqual(list(out),[desc.offset(i) for i in range(144000)])


if __name__=='__main__': unittest.main()
