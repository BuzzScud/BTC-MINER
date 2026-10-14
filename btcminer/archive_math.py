"""Resident native calculation adapters for archived arithmetic theorems.

Uses the same loaded library as the shared abacus. C/Python correspondence is
tested, not formally verified. Conditional factor recovery is not a SHA filter.
"""
import ctypes as C
from functools import lru_cache
from math import isqrt, lcm, log
from .shared_abacus import Big, bigint, integer, checked, library


def flower_boundary(k):
    """Derived all-k contact system; area is in Eisenstein lattice cells.

    Dimension numerically evaluates the exact logarithmic expression. This is
    the October 11 user derivation and independent review, not a Lean receipt.
    """
    if type(k) is not int or k<1: raise ValueError('Flower radius must be a positive integer')
    N=3*k*k+3*k+1
    return {'k':k,'beta':[2*k+1,k],'digit_count':N,
            'neighbours':[[1,0],[1,1],[0,1],[-1,0],[-1,-1],[0,-1]],
            'contact_matrix':[[k+1 if i==j else k if j==(i+1)%6 else 0 for j in range(6)] for i in range(6)],
            'spectral_radius':2*k+1,'area_lattice_cells':1,
            'boundary_dimension':2*log(2*k+1)/log(N),
            'proof_status':'derived_all_k; independently tested; not Lean compiled',
            'bitcoin_exclusion_authority':False}


@lru_cache(maxsize=1)
def flower_nonce_labels():
    """360 labels from nonzero two-digit 19-flower address classes.

    beta=5+2*omega, beta^2=21+16*omega, norm=361. The exact quotient map
    a+b*omega -> a+292*b mod 361 has kernel (beta^2). Order the two digits
    geometrically by shell, omit only the zero class, then subtract one.
    This quotient is Z/361, not the field GF(19^2). Nonunits remain included.
    """
    units=((1,0),(1,1),(0,1),(-1,0),(-1,-1),(0,-1))
    digits=[(0,0)]
    for radius in (1,2):
        for side in range(6):
            u,v=units[side],units[(side+1)%6]
            digits.extend(((radius-t)*u[0]+t*v[0],(radius-t)*u[1]+t*v[1]) for t in range(radius))
    labels=[]
    for a1,b1 in digits:
        for a0,b0 in digits:
            a,b=a0+5*a1-2*b1,b0+2*a1+3*b1
            value=(a+292*b)%361
            if value: labels.append(value-1)
    if len(digits)!=19 or len(set(digits))!=19 or sorted(labels)!=list(range(360)):
        raise ArithmeticError('Flower address labels failed full coverage')
    return tuple(labels)


@lru_cache(maxsize=1)
def clock_tables():
    """All twelve exact powers of DialShadow.clockRot; immutable and shared."""
    rotation=((0,0,0,-1),(1,0,0,0),(0,1,0,1),(0,0,1,0))
    identity=tuple(tuple(int(i==j) for j in range(4)) for i in range(4))
    table=[]; current=identity
    for _ in range(12):
        table.append(current)
        current=tuple(tuple(sum(current[i][k]*rotation[k][j] for k in range(4))
                            for j in range(4)) for i in range(4))
    if current != identity:raise ArithmeticError('Clock table failed its period check')
    return tuple(table)


@lru_cache(maxsize=1)
def clock_geometry():
    """Complete finite 24-cell model in the archive's integer clock basis."""
    from itertools import product
    gram=((2,1,1,0),(1,2,1,1),(1,1,2,1),(0,1,1,2))
    box=tuple(product((-1,0,1),repeat=4))
    roots=tuple(v for v in box if sum(v[i]*gram[i][j]*v[j]
                                     for i in range(4) for j in range(4))==2)
    cells=[]
    for f in box:
        readings=tuple(sum(x*y for x,y in zip(f,v)) for v in roots)
        if max(readings)<=1:
            face=frozenset(v for v,d in zip(roots,readings) if d==1)
            if len(face)==6:cells.append(face)
    if len(roots)!=24 or len(set(cells))!=24:
        raise ArithmeticError('24-cell census failed')
    return roots,tuple(cells)


@lru_cache(maxsize=1)
def clock_flags():
    """Packed F4 action and complete flag census, built once and kept resident.

    Each permutation uses 24 bytes; each flag uses four one-byte indices.
    The final tuples/bytes are immutable. This geometry does not reject nonces.
    """
    roots,cells=clock_geometry(); index={v:i for i,v in enumerate(roots)}
    matrices=(
        ((0,1,0,1),(1,0,0,-1),(0,0,1,0),(0,0,0,1)),
        ((1,0,0,0),(0,0,1,0),(0,1,0,0),(0,0,0,1)),
        ((1,0,1,0),(0,1,0,0),(0,0,-1,0),(0,0,1,1)),
        ((1,0,0,-1),(0,1,0,1),(0,0,1,1),(0,0,0,-1)))
    generators=tuple(bytes(index[tuple(sum(a*b for a,b in zip(row,v)) for row in m)]
                           for v in roots) for m in matrices)
    group=[bytes(range(24))]; seen=set(group)
    for perm in group:
        for generator in generators:
            composed=bytes(generator[i] for i in perm)
            if composed not in seen:
                seen.add(composed);group.append(composed)
                if len(group)>1152:raise ArithmeticError('F4 closure exceeded its proved finite order')
    gram=((2,1,1,0),(1,2,1,1),(1,1,2,1),(0,1,1,2))
    neighbors=tuple(frozenset(j for j,u in enumerate(roots)
                   if sum(v[a]*gram[a][b]*u[b] for a in range(4) for b in range(4))==1)
                    for v in roots)
    cell_indices=tuple(frozenset(index[v] for v in c) for c in cells)
    cell_lookup={c:i for i,c in enumerate(cell_indices)}
    flags=frozenset((v,u,t,c) for v in range(24) for u in neighbors[v]
                    for t in neighbors[v]&neighbors[u] for c,cell in enumerate(cell_indices)
                    if {v,u,t}<=cell)
    base=(index[(-1,1,0,0)],index[(0,1,0,0)],index[(0,0,0,1)])
    base_cell=frozenset(index[v] for v in
        ((-1,1,0,0),(0,0,-1,1),(0,0,0,1),(0,1,-1,0),(0,1,0,0),(1,0,-1,1)))
    orbit=frozenset((*[p[v] for v in base],cell_lookup[frozenset(p[v] for v in base_cell)])
                    for p in group)
    if len(group)!=1152 or len(flags)!=1152 or orbit!=flags:
        raise ArithmeticError('F4 flag census/transitivity disagrees with the archive')
    return generators,b''.join(group),bytes(x for flag in sorted(flags) for x in flag)


class Clock24:
    """Periodic 4D lattice rotation, applied to arbitrary-precision rod columns.

    The period shortcut is a proved property of this particular matrix; it is
    not a rule for reducing SHA rounds or Bitcoin nonce candidates.
    """
    def __init__(self, pool=None):
        from .shared_abacus import Calculation
        self.tables=clock_tables(); self.workspace=Calculation(slots=9,pool=pool)

    def rotate(self, coordinates, depth):
        coordinates=tuple(coordinates)
        if len(coordinates)!=4 or any(type(x) is not int for x in coordinates):
            raise ValueError('Supply four integer coordinates')
        if type(depth) is not int or depth < 0:raise ValueError('Depth must be a natural number')
        self.workspace.clear()
        for i,x in enumerate(coordinates):self.workspace.load(i,x)
        operations=[]
        for i,row in enumerate(self.tables[depth%12]):
            for j,coefficient in enumerate(row):
                if coefficient:
                    operations += [('mulc',8,j,0,coefficient),('add',4+i,4+i,8)]
        self.workspace.run(operations)
        return tuple(self.workspace.columns[4+i].value() for i in range(4))


def ramanujan_coefficients(count=60):
    """SharedModels.Ramanujan.deltaProd, computed on resident integer rods.

    Returns tau(1)..tau(count). Each truncated factor is multiplied in place,
    descending in degree; the table/frame stays loaded across all factors.
    Finite calculations do not prove a congruence for every natural number.
    """
    from .shared_abacus import Calculation
    if type(count) is not int or not 1 <= count <= 128:
        raise ValueError('Use 1..128 coefficients within the explicit work budget')
    calc=Calculation(slots=count,bits=24*count+4)
    calc.load(0,1)
    operations=[]
    for n in range(1,count):
        for _ in range(24):
            operations.extend(('sub',j,j,j-n) for j in range(count-1,n-1,-1))
    calc.run(operations)
    return [c.value() for c in calc.columns]


@lru_cache(maxsize=1)
def backend():
    lib = library(); B = C.POINTER(Big); U = C.POINTER(C.c_uint32)
    signatures = {f'lc_int_{op}': (C.c_int, [B, B, B])
                  for op in ('add', 'sub', 'mul', 'gcd', 'lcm', 'invmod')}
    signatures.update({
        'lc_int_sqrt': (C.c_int, [B, B]),
        'lc_int_powmod': (C.c_int, [B, B, B, B]),
        'lc_int_qtok': (C.c_int, [B, B, B, B, B, B, U, C.c_size_t, C.POINTER(C.c_size_t)]),
        'lc_mersenne_mod': (C.c_uint64, [C.c_uint64, C.c_uint]),
        'lc_dial12_inv': (C.c_uint32, [C.c_uint32]),
    })
    for name, (result, arguments) in signatures.items():
        fn = getattr(lib, name); fn.restype = result; fn.argtypes = arguments
    return lib


def integer_operation(op, *values):
    arities = {'add': 2, 'sub': 2, 'mul': 2, 'gcd': 2, 'lcm': 2,
               'invmod': 2, 'sqrt': 1, 'powmod': 3}
    if op not in arities or len(values) != arities[op]:
        raise ValueError('Unknown operation or arity')
    if any(type(n) is not int or abs(n).bit_length() > 240000 for n in values):
        raise ValueError('Expected integers within the configured arithmetic memory budget')
    if op == 'powmod' and (values[1] < 0 or values[2] <= 0):
        raise ValueError('Require nonnegative exponent and positive modulus')
    out = Big(); inputs = [bigint(n) for n in values]; lib = backend()
    try:
        checked(getattr(lib, 'lc_int_'+op)(C.byref(out), *(C.byref(n) for n in inputs)))
        return integer(out)
    finally: lib.lc_int_clear(C.byref(out))


def recover_from_k(n, k):
    """PQRecovery.recoverFromK: at most four roots, GIVEN the closing exponent.

    Natural subtraction truncates at zero, as in the archived Lean function.
    Every returned pair is checked against n; a failed search returns None.
    """
    if type(n) is not int or type(k) is not int or n < 4 or k <= 0:
        raise ValueError('Require n >= 4 and a supplied positive k')
    for g in range(max(0, n//k-3), max(0, n//k-3)+4):
        s = max(0, n+1-g*k); r = isqrt(max(0, s*s-4*n))
        p, q = max(0, s-r)//2, (s+r)//2
        if 2 <= p <= q and p*q == n: return p, q
    return None


def order_split(n, base, exponent, prime_factors):
    """Sound factors whenever returned; completeness requires the Lean hypotheses.

    The supplied exponent and factor list are inputs, not hidden free oracles.
    A returned k is independently checked as lcm(g-1,h-1). If g,h are
    distinct primes, it equals lambda(n); this is a sufficient guarantee,
    not an iff characterization. Their primality is not checked here.
    """
    factors = tuple(prime_factors)
    if any(type(x) is not int or x < 0 or x.bit_length() > 16384 for x in (n, base, exponent)) or n < 2 or exponent == 0:
        raise ValueError('Use nonnegative bounded inputs, n >= 2 and exponent > 0')
    if not 1 <= len(factors) <= 64 or any(type(p) is not int or not 2 <= p < 2**32 for p in factors):
        raise ValueError('Supply 1..64 factor bases in [2, 2^32)')
    values = [bigint(v) for v in (n, base, exponent)]
    outputs = [Big(), Big(), Big()]; steps = C.c_size_t(); lib = backend()
    try:
        status = lib.lc_int_qtok(*(C.byref(v) for v in outputs),
                                *(C.byref(v) for v in values),
                                (C.c_uint32*len(factors))(*factors),len(factors),C.byref(steps))
        if status < 0: checked(status)
        result = [integer(v) for v in outputs] if status else None
        if result and not (1 < result[0] < n and result[0]*result[1] == n):
            raise ArithmeticError('Native factor failed independent product check')
        if result and result[2] != lcm(result[0]-1, result[1]-1):
            raise ArithmeticError('Native k failed independent lcm check')
        return {'factors_and_k': result, 'gcd_steps': steps.value,
                'conditional_on': 'Known suitable E, its complete prime factors, differing base orders for completeness; distinct prime returned factors suffice for Carmichael lambda(n) interpretation (primality not checked)'}
    finally:
        for v in outputs: lib.lc_int_clear(C.byref(v))


class Eisenstein(C.Structure):
    _fields_ = [('a', Big), ('b', Big)]


def hex_distance(a, b):
    """Exact E-coordinate distance max(|a|, |b|, |a-b|), on native big integers.

    This is graph distance, distinct from a*a-a*b+b*b (squared Euclidean norm).
    Z6 coordinates require converting the second coordinate's sign first.
    """
    if any(type(n) is not int or abs(n).bit_length() > 240000 for n in (a,b)):
        raise ValueError('Expected integer coordinates within the arithmetic memory budget')
    lib=library(); fn=lib.lc_eis_hexdist
    fn.restype=C.c_int; fn.argtypes=[C.POINTER(Big), C.POINTER(Eisenstein)]
    point=Eisenstein(bigint(a),bigint(b)); result=Big()
    try:
        checked(fn(C.byref(result),C.byref(point)))
        return integer(result)
    finally:
        lib.lc_int_clear(C.byref(result))


class HexBase(C.Structure):
    _fields_ = [('k', C.c_uint), ('N', C.c_uint32), ('root', C.c_uint32),
                ('digit', C.POINTER(C.c_int32*2)), ('beta', Eisenstein), ('beta_conj', Eisenstein)]


class Flower:
    """Reusable exact lattice digit table, arbitrary-precision coordinates."""
    def __init__(self, k=2):
        if type(k) is not int or not 1 <= k <= 64:
            raise ValueError('Flower table radius must be 1..64')
        self.lib = library(); self.base = HexBase(); self.ready = False
        H = C.POINTER(HexBase); E = C.POINTER(Eisenstein); D = C.POINTER(C.c_int32*2)
        specs = {'lc_hexbase_init': (C.c_int,[H,C.c_uint]),
                 'lc_hexbase_clear': (None,[H]), 'lc_eis_clear': (None,[E]),
                 'lc_hexbase_address': (C.c_int,[H,E,C.c_size_t,D,E]),
                 'lc_hexbase_from_address': (C.c_int,[H,E,C.c_size_t,D,E])}
        for name,(res,args) in specs.items():
            fn=getattr(self.lib,name);fn.restype=res;fn.argtypes=args
        checked(self.lib.lc_hexbase_init(C.byref(self.base), k)); self.ready = True

    def __del__(self):
        if getattr(self,'ready',False): self.lib.lc_hexbase_clear(C.byref(self.base))

    def boundary(self):
        return flower_boundary(self.base.k)

    def address(self, a, b, depth=16):
        if type(depth) is not int or not 0 <= depth <= 4096:
            raise ValueError('Address depth must be 0..4096')
        if any(type(v) is not int or abs(v).bit_length() > 240000 for v in (a,b)):
            raise ValueError('Coordinates exceed the configured arithmetic memory budget')
        z=Eisenstein(bigint(a),bigint(b)); rem=Eisenstein(); restored=Eisenstein()
        digits=((C.c_int32*2)*depth)()
        try:
            checked(self.lib.lc_hexbase_address(C.byref(self.base),C.byref(z),depth,digits,C.byref(rem)))
            checked(self.lib.lc_hexbase_from_address(C.byref(self.base),C.byref(restored),depth,digits,C.byref(rem)))
            value=(integer(restored.a),integer(restored.b))
            if value != (a,b): raise ArithmeticError('Flower address failed reconstruction')
            return {'digits':[list(d) for d in digits], 'remainder':(integer(rem.a),integer(rem.b)),
                    'restored':value,'base_norm':self.base.N}
        finally:
            self.lib.lc_eis_clear(C.byref(rem)); self.lib.lc_eis_clear(C.byref(restored))


class CircleModel:
    """Exact pair and triple relationships in a positive-definite integer form.

    Radii are squared radii. The workspace stays loaded and clears between
    expressions. Degenerate centres are handled explicitly, never discarded.
    """
    def __init__(self, form=(1,1,1), pool=None):
        from .claim_calculus import ClaimCalculator
        self.form=tuple(form)
        if len(self.form)!=3 or any(type(x) is not int for x in self.form):
            raise ValueError('Expected three integer form coefficients')
        a,b,c=self.form
        if a<=0 or 4*a*c-b*b<=0:raise ValueError('The form must be positive definite')
        self.calculator=ClaimCalculator(pool=pool,slots=512)

    def _value(self, expression):
        calc=self.calculator;calc.calculation.clear();calc.next_slot=0
        slot=calc.formula(expression,{})
        return calc.calculation.columns[slot].value()

    def _q(self,x,y):
        a,b,c=self.form
        return ('add',('add',('mul',a,('mul',x,x)),('mul',b,('mul',x,y))),('mul',c,('mul',y,y)))

    @staticmethod
    def _circle(value):
        value=tuple(value)
        if len(value)!=3 or any(type(x) is not int for x in value) or value[2]<0:
            raise ValueError('Circle requires integer x,y and nonnegative squared radius')
        return value

    def pair(self, first, second):
        x,y,r=self._circle(first);u,v,s=self._circle(second)
        if (x,y)==(u,v):
            return {'relation':('coincident_point' if r==0 else 'coincident_circle') if r==s else 'apart',
                    'discriminant':None,'degenerate_centres':True}
        d=self._q(('sub',x,u),('sub',y,v));gap=('sub',('sub',d,r),s)
        delta=self._value(('sub',('mul',gap,gap),('mul',4,('mul',r,s))))
        return {'relation':'crossing' if delta<0 else 'tangent' if delta==0 else 'apart',
                'discriminant':delta,'degenerate_centres':False}

    def triple(self, first, second, third):
        from fractions import Fraction
        x,y,r=self._circle(first);u,v,s=self._circle(second);z,w,t=self._circle(third)
        a,b,c=self.form
        dx,dy=self._value(('sub',u,x)),self._value(('sub',v,y))
        ex,ey=self._value(('sub',z,x)),self._value(('sub',w,y))
        A=self._value(('add',('mul',2*a,dx),('mul',b,dy)))
        B=self._value(('add',('mul',b,dx),('mul',2*c,dy)))
        C=self._value(('add',('mul',2*a,ex),('mul',b,ey)))
        D=self._value(('add',('mul',b,ex),('mul',2*c,ey)))
        determinant=self._value(('sub',('mul',A,D),('mul',C,B)))
        if not determinant:
            return {'applicable':False,'reason':'Collinear centres: the concurrence theorem requires nonzero determinant'}
        k=self._value(('add',('sub',r,s),self._q(dx,dy)))
        ell=self._value(('add',('sub',r,t),self._q(ex,ey)))
        wx=self._value(('sub',('mul',k,D),('mul',ell,B)))
        wy=self._value(('sub',('mul',A,ell),('mul',C,k)))
        polynomial=self._value(('sub',self._q(wx,wy),('mul',r,('mul',determinant,determinant))))
        point=(Fraction(x)+Fraction(wx,determinant),Fraction(y)+Fraction(wy,determinant))
        return {'applicable':True,'concurrent':polynomial==0,'polynomial':polynomial,
                'determinant':determinant,'radical_centre':point}
