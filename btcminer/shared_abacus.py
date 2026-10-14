"""Resident coprime frames, shared views and independent reusable columns.

Programs evaluate on small rods. Integer read-back requires an explicit interval
shorter than the CRT capacity; congruence alone is never integer equality.
Distributed merges also require matching structural expression lineage. Recurrence
intervals are derived from a saturating absolute companion bound, not asserted.
The native ABI has an 8192-rod memory guard, not a 4096-bit arithmetic limit.
"""
import ctypes as C
from functools import lru_cache
from math import prod, gcd
from threading import RLock
from weakref import WeakValueDictionary
from . import ROOT
from .coreprimes import CORE


class Big(C.Structure):
    _fields_ = [('sign', C.c_int), ('len', C.c_size_t), ('cap', C.c_size_t),
                ('d', C.POINTER(C.c_uint32))]


class Op(C.Structure):
    _fields_ = [('kind', C.c_int), ('dst', C.c_int), ('a', C.c_int), ('b', C.c_int),
                ('c', C.c_int64), ('e', C.c_uint64)]


def checked(code):
    if code:
        raise ArithmeticError('Native shared abacus error %s' % code)


@lru_cache(maxsize=1)
def library():
    import sys
    path = ROOT/'native'/__import__('btcminer.platform_support', fromlist=['native_name']).native_name('libabacus')
    if not path.exists():
        raise RuntimeError('Build the shared abacus with bash native/build.sh')
    lib = C.CDLL(str(path)); V = C.c_void_p; U = C.POINTER(C.c_uint32)
    S = C.c_size_t; I = C.c_int; B = C.POINTER(Big)
    signatures = {
        'lc_abacus_new': (V, [U, S, C.POINTER(I)]),
        'lc_abacus_primes': (V, [S, C.POINTER(I)]),
        'lc_abacus_release': (None, [V]), 'lc_abacus_size': (S, [V]),
        'lc_abacus_moduli': (U, [V]), 'lc_abacus_origin': (S, [V, S]),
        'lc_abacus_view': (V, [V, C.POINTER(S), S, C.POINTER(I)]),
        'lc_abacus_merge': (V, [V, V, C.POINTER(I)]),
        'lc_abacus_encode': (I, [V, U, B]), 'lc_abacus_decode': (I, [V, B, U]),
        'lc_abacus_run': (I, [V, C.POINTER(Op), S, C.POINTER(U), S]),
        'lc_abacus_linrec': (I, [V, U, C.POINTER(C.c_int64), C.POINTER(C.c_int64), S, C.c_uint64]),
        'lc_int_clear': (None, [B]), 'lc_rmont_fit': (S, [V, B]),
        'lc_rmont_new': (V, [V, S, S, B, C.POINTER(I)]),
        'lc_rmont_free': (None, [V]), 'lc_rmont_powmod': (I, [V, B, B, B]),
    }
    for name, (result, arguments) in signatures.items():
        fn = getattr(lib, name); fn.restype = result; fn.argtypes = arguments
    return lib


def bigint(n):
    if type(n) is not int:
        raise TypeError('Expected an integer')
    length = (abs(n).bit_length()+31)//32
    limbs = (C.c_uint32*length)(*((abs(n) >> (32*i)) & 0xffffffff for i in range(length)))
    # ctypes keeps the Python-owned limb allocation alive. Native calls only read it.
    return Big((n > 0)-(n < 0), length, length, limbs)


def integer(value):
    return value.sign*sum(int(value.d[i]) << (32*i) for i in range(value.len))


def i64(n):
    if type(n) is not int or not -(1 << 63) <= n < 1 << 63:
        raise ValueError('Coefficient must fit signed 64 bits; use an input column for larger constants')
    return n


class _Expression:
    """Interned immutable syntax, not an evaluated integer or a proof hash."""
    __slots__ = ('kind', 'arguments', '__weakref__')

    def __init__(self, kind, arguments):
        object.__setattr__(self, 'kind', kind)
        object.__setattr__(self, 'arguments', arguments)

    def __setattr__(self, name, value):
        raise AttributeError('Expression lineage is immutable')


_expressions = WeakValueDictionary()
_expression_lock = RLock()


def _expression(kind, *arguments):
    # Dictionary hashes only locate candidates: exact tuple equality decides
    # interning. Parent nodes use identity, avoiding recursive DAG comparison.
    key = (kind, arguments)
    with _expression_lock:
        result = _expressions.get(key)
        if result is None:
            result = _Expression(kind, arguments)
            _expressions[key] = result
        return result


def _recurrence_bound(coefficients, initial, depth, bound):
    """Sufficient |u_depth| bound, saturated at bound+1 in O(log depth).

    Coefficients are latest-first, matching lc_abacus_linrec. Absolute values
    give a nonnegative companion recurrence dominating the signed recurrence.
    Saturation commutes with its sums/products, including multiplication by 0.
    This can reject a small true bound when cancellation is essential.
    """
    cap = bound + 1
    d = len(initial)
    if depth < d:
        return min(cap, abs(initial[depth]))
    matrix = [[0] * d for _ in range(d)]
    matrix[0] = [min(cap, abs(c)) for c in coefficients]
    for i in range(1, d): matrix[i][i-1] = 1
    state = [min(cap, abs(v)) for v in reversed(initial)]

    def dot(a, b):
        total = 0
        for x, y in zip(a, b):
            total = min(cap, total + x*y)
            if total == cap: break
        return total

    exponent = depth - (d-1)
    while exponent:
        if exponent & 1:
            state = [dot(row, state) for row in matrix]
        exponent >>= 1
        if exponent:
            columns = list(zip(*matrix))
            matrix = [[dot(row, column) for column in columns] for row in matrix]
    return state[0]


class Frame:
    """Immutable native frame. Views retain the root, including across threads.

    No manual close: Python owners keep frames alive throughout native calls;
    native atomic reference counts retain roots when a view outlives its parent.
    """
    def __init__(self, moduli=None, *, primes=None, _pointer=None):
        self._lib = library(); self._pointer = None; err = C.c_int()
        if _pointer is not None:
            pointer = _pointer
        elif primes is not None:
            if type(primes) is not int or not 1 <= primes <= 8192:
                raise ValueError('Native frame supports 1..8192 rods within its memory budget')
            pointer = self._lib.lc_abacus_primes(primes, C.byref(err))
        else:
            moduli = tuple(moduli)
            if not 1 <= len(moduli) <= 8192 or any(type(m) is not int or not 2 <= m < 1 << 31 for m in moduli):
                raise ValueError('Rods must be integers in [2, 2^31), with at most 8192 rods')
            pointer = self._lib.lc_abacus_new((C.c_uint32*len(moduli))(*moduli), len(moduli), C.byref(err))
        checked(err.value)
        if not pointer:
            raise MemoryError('Could not allocate abacus')
        self._pointer = pointer
        self.size = self._lib.lc_abacus_size(pointer)
        self.moduli = tuple(self._lib.lc_abacus_moduli(pointer)[i] for i in range(self.size))
        self.capacity = prod(self.moduli)
        self.origins = tuple(self._lib.lc_abacus_origin(pointer, i) for i in range(self.size))
        self._shape = (self._pointer, self.size, self.moduli, self.capacity, self.origins)
        self._crt_plan = None  # Lazily retained per immutable frame for large read-backs.

    def _check_shape(self):
        if self._shape != (self._pointer, self.size, self.moduli, self.capacity, self.origins):
            raise ValueError('Frame metadata changed after construction')

    def __del__(self):
        if getattr(self, '_pointer', None):
            self._lib.lc_abacus_release(self._pointer)

    def view(self, indices):
        self._check_shape()
        indices = tuple(indices)
        if not indices or len(set(indices)) != len(indices) or any(type(i) is not int or not 0 <= i < self.size for i in indices):
            raise ValueError('View requires distinct, in-range indices')
        err = C.c_int()
        pointer = self._lib.lc_abacus_view(self._pointer, (C.c_size_t*len(indices))(*indices), len(indices), C.byref(err))
        checked(err.value)
        return Frame(_pointer=pointer)

    def merge(self, other):
        self._check_shape(); other._check_shape()
        if self.size+other.size > 8192:
            raise ValueError('Merge exceeds configured native memory budget')
        err = C.c_int()
        pointer = self._lib.lc_abacus_merge(self._pointer, other._pointer, C.byref(err))
        checked(err.value)
        return Frame(_pointer=pointer)

    def column(self, value=0):
        return Column(self).load(value)

    def program(self, instructions, columns, *, exact=True):
        """Execute CONST/COPY/ADD/SUB/MUL/POW/MULC/ADDC; check bounds first.

        Instructions: (operation, destination, a=0, b=0, constant=0, exponent=0).
        Wraparound is never returned as an exact integer. Inputs/outputs belong
        to one workspace and must not be mutated concurrently.
        """
        self._check_shape()
        if not columns or len({id(c) for c in columns}) != len(columns):
            raise ValueError('Slots must be distinct columns (use COPY for aliasing)')
        for column in columns: column._check_certificate()
        if any(c.frame is not self or c.interval is None for c in columns):
            raise ValueError('Exact programs require bounded columns on this frame')
        names = ('const', 'copy', 'add', 'sub', 'mul', 'pow', 'mulc', 'addc')
        bounds = [c.interval for c in columns]
        expressions = [c._lineage for c in columns]; operations = []; destinations = set()
        for instruction in instructions:
            name, dst, a, b, constant, exponent = tuple(instruction)+(0,)*(6-len(instruction))
            if name not in names or any(type(i) is not int or not 0 <= i < len(columns) for i in (dst, a, b)):
                raise ValueError('Invalid program operation or slot')
            i64(constant)
            if type(exponent) is not int or not 0 <= exponent <= 1_000_000:
                raise ValueError('Bounded program exponent must be in 0..1000000')
            lo, hi = bounds[a]; bl, bh = bounds[b]
            if name == 'const': out = (constant, constant)
            elif name == 'copy': out = (lo, hi)
            elif name == 'add': out = (lo+bl, hi+bh)
            elif name == 'sub': out = (lo-bh, hi-bl)
            elif name in ('mul', 'mulc'):
                if name == 'mulc': bl = bh = constant
                v = (lo*bl, lo*bh, hi*bl, hi*bh); out = (min(v), max(v))
            elif name == 'addc': out = (lo+constant, hi+constant)
            else:
                # Bound size before allocating a possibly enormous integer.
                magnitude = max(abs(lo), abs(hi))
                bits = 1 if magnitude <= 1 else magnitude.bit_length()*exponent
                if bits > (self.capacity.bit_length() if exact else 240000):
                    raise OverflowError('Power needs a larger frame')
                v = (lo**exponent, hi**exponent)
                out = (0 if lo <= 0 <= hi and exponent > 0 and exponent % 2 == 0 else min(v), max(v))
            if exact and out[1]-out[0] >= self.capacity:
                raise OverflowError('Formula exceeds CRT capacity; reserve more rods before running')
            left, right = expressions[a], expressions[b]
            if name == 'const': expression = _expression('input', constant)
            elif name == 'copy': expression = left
            elif name in ('addc', 'mulc'):
                expression = _expression(name[:-1], left, _expression('input', constant))
            elif name == 'pow': expression = _expression('pow', left, exponent)
            else: expression = _expression(name, left, right)
            bounds[dst] = out
            expressions[dst] = expression; destinations.add(dst)
            operations.append(Op(names.index(name), dst, a, b, constant, exponent))
        slots = (C.POINTER(C.c_uint32)*len(columns))(*(c._data for c in columns))
        # A native error may leave partial writes. No old range/lineage may
        # remain usable on any destination until the entire call succeeds.
        for dst in destinations: columns[dst]._invalidate()
        checked(self._lib.lc_abacus_run(self._pointer, (Op*len(operations))(*operations), len(operations), slots, len(columns)))
        for dst in destinations: columns[dst]._seal(bounds[dst], expressions[dst])

    def jump(self, coefficients, initial, depth, *, bound=None, out=None):
        self._check_shape()
        coefficients = tuple(map(i64, coefficients)); initial = tuple(map(i64, initial))
        if not 1 <= len(initial) == len(coefficients) <= 8 or type(depth) is not int or not 0 <= depth < 1 << 64:
            raise ValueError('Recurrence requires order 1..8 and unsigned 64-bit depth')
        column = out if out is not None else Column(self)
        if column.frame is not self: raise ValueError('Wrong recurrence output frame')
        interval = None
        if bound is not None:
            if type(bound) is not int or bound < 0 or 2*bound >= self.capacity:
                raise OverflowError('Recurrence bound needs a larger frame')
            if _recurrence_bound(coefficients, initial, depth, bound) > bound:
                raise ValueError('Requested recurrence bound is not established by the absolute companion recurrence')
            interval = (-bound, bound)
        array = C.c_int64*len(initial)
        column._invalidate()
        checked(self._lib.lc_abacus_linrec(self._pointer, column._data, array(*coefficients), array(*initial), len(initial), depth))
        column._seal(interval, _expression('jump', coefficients, initial, depth))
        return column

    def powmod(self, base, exponent, modulus):
        self._check_shape()
        if any(type(v) is not int for v in (base, exponent, modulus)) or min(base, exponent) < 0 or modulus <= 1 or modulus % 2 == 0:
            raise ValueError('Rod Montgomery requires nonnegative base/exponent and odd modulus > 1')
        p = bigint(modulus); k = self._lib.lc_rmont_fit(self._pointer, C.byref(p))
        if not k or any(gcd(modulus, m) != 1 for m in self.moduli[:k]):
            raise ValueError('Frame does not satisfy Montgomery capacity/coprimality conditions')
        err = C.c_int(); context = self._lib.lc_rmont_new(self._pointer, k, k, C.byref(p), C.byref(err))
        checked(err.value); result = Big()
        try:
            b = bigint(base); e = bigint(exponent)
            checked(self._lib.lc_rmont_powmod(context, C.byref(result), C.byref(b), C.byref(e)))
            return integer(result)
        finally:
            self._lib.lc_int_clear(C.byref(result)); self._lib.lc_rmont_free(context)

    def description(self):
        return {'rods': self.size, 'capacity_bits': self.capacity.bit_length()-1,
                'column_bytes': self.size*4, 'immutable': True,
                'readback': 'Unique integer only within a justified interval shorter than capacity'}


class Column:
    def __init__(self, frame):
        frame._check_shape()
        self._frame = frame; self._data = (C.c_uint32*frame.size)(); self._epoch = 0
        self._seal((0, 0), _expression('input', 0))

    @property
    def frame(self): return self._frame

    @property
    def interval(self): return self._interval

    def _invalidate(self):
        self._epoch += 1
        self._certificate = None; self._interval = None; self._lineage = None

    def _seal(self, interval, lineage):
        self._interval = interval; self._lineage = lineage
        # Exact byte comparison, not a digest equality or a cryptographic claim.
        self._certificate = (self._epoch, self.frame, interval, lineage, bytes(self._data))

    def _check_certificate(self):
        self.frame._check_shape()
        if self._certificate is None or self._certificate != (
                self._epoch, self.frame, self._interval, self._lineage, bytes(self._data)):
            raise ValueError('Column bytes or metadata no longer match their range and expression lineage')

    def load(self, value):
        self.frame._check_shape()
        if type(value) is not int: raise TypeError('Expected integer')
        # Whole bit-length envelope rather than carrying the answer as a singleton bound.
        limit = (1 << abs(value).bit_length())-1
        interval = (-limit, 0) if value < 0 else (0, limit)
        if limit >= self.frame.capacity: raise OverflowError('Input needs a larger frame')
        big = bigint(value)
        self._invalidate()
        checked(self.frame._lib.lc_abacus_encode(self.frame._pointer, self._data, C.byref(big)))
        self._seal(interval, _expression('input', value))
        return self

    def clear(self):
        self.frame._check_shape(); self._invalidate()
        C.memset(self._data, 0, C.sizeof(self._data)); self._seal((0, 0), _expression('input', 0))
        return self

    @property
    def residues(self): return tuple(self._data)

    def value(self):
        self._check_certificate()
        if self.interval is None: raise ValueError('Unbounded recurrence is a modular column, not an exact integer')
        if self.interval[1]-self.interval[0] >= self.frame.capacity:
            raise OverflowError('Modular column is ambiguous; merge sufficient coprime rods before integer read-back')
        if self.frame.size >= 64:
            # Small frames retain the native fast path. The reusable balanced
            # tree avoids native sequential Garner decode on larger frames.
            from .product_tree_crt import ProductTreeCRT
            if self.frame._crt_plan is None:
                self.frame._crt_plan = ProductTreeCRT(self.frame.moduli)
            if (type(self.frame._crt_plan) is not ProductTreeCRT or
                    self.frame._crt_plan.moduli != self.frame.moduli or
                    self.frame._crt_plan.capacity != self.frame.capacity):
                raise ValueError('Cached CRT plan does not match the certified frame')
            return self.frame._crt_plan.decode_interval(self.residues, *self.interval)
        result = Big()
        try:
            checked(self.frame._lib.lc_abacus_decode(self.frame._pointer, C.byref(result), self._data))
            residue = integer(result); low, high = self.interval
            value = low+(residue-low) % self.frame.capacity
            if value > high: raise ArithmeticError('Residues contradict the declared interval')
            return value
        finally: self.frame._lib.lc_int_clear(C.byref(result))

    def restrict(self, view):
        self._check_certificate(); view._check_shape()
        # Restriction must be a view of the same ordered rods, not merely same length.
        indices = {m: i for i, m in enumerate(self.frame.moduli)}
        if any(m not in indices for m in view.moduli): raise ValueError('Not a subframe')
        column = Column(view)
        for i, m in enumerate(view.moduli): column._data[i] = self._data[indices[m]]
        column._seal(self.interval, self._lineage)
        return column

    def merge(self, other, frame):
        self._check_certificate(); other._check_certificate(); frame._check_shape()
        if frame.moduli != self.frame.moduli+other.frame.moduli:
            raise ValueError('Merged frame must concatenate the source rods')
        if self.interval != other.interval:
            raise ValueError('Merge requires the same justified interval')
        if self._lineage is not other._lineage:
            raise ValueError('Merge requires the same input and expression lineage')
        column = Column(frame)
        column._data[:] = self.residues+other.residues
        column._seal(self.interval, self._lineage)
        return column


class FramePool:
    """Shared resident roots grow geometrically; small views reuse inverse tables."""
    def __init__(self):
        self._lock = RLock(); self.root = None; self._views = {}; self.builds = 0

    def frame(self, bits=8192):
        if type(bits) is not int or not 1 <= bits <= 240000:
            raise ValueError('Native pool memory budget permits requests of 1..240000 bits')
        with self._lock:
            required = max(272, (bits+29)//30)
            if self.root is None or self.root.capacity <= 1 << bits:
                count = required if self.root is None else max(required, min(8000, 2*(self.root.size-5)))
                primes = Frame(primes=count)
                self.root = Frame(tuple(p*p for p in CORE)+primes.moduli)
                self._views.clear(); self.builds += 1
            key = bits
            if key not in self._views:
                capacity = 1; n = 0
                for rod in self.root.moduli:
                    capacity *= rod; n += 1
                    if capacity > 1 << bits: break
                self._views[key] = self.root.view(range(n))
            return self._views[key]


@lru_cache(maxsize=1)
def shared_pool(): return FramePool()


class Calculation:
    """Reusable slots; only capacity growth migrates values to a larger view."""
    def __init__(self, slots=4, bits=64, pool=None):
        if type(slots) is not int or not 1 <= slots <= 4096:
            raise ValueError('Use 1..4096 calculation slots')
        self.pool = pool or shared_pool(); self.frame = self.pool.frame(bits)
        self.columns = [self.frame.column() for _ in range(slots)]
        self.growths = 0; self.runs = 0

    def reserve(self, bits):
        if type(bits) is not int or not 1 <= bits <= 240000:
            raise ValueError('Native calculation memory budget permits 1..240000 bits')
        if self.frame.capacity > 1 << bits: return
        values = [c.value() for c in self.columns]
        frame = self.pool.frame(bits)
        columns = [frame.column(v) for v in values]
        # A verified read/re-encode migrates the same denotation. Do not retain
        # the intermediate decoded answer as a new literal lineage leaf.
        for old, new in zip(self.columns, columns):
            new._seal(old.interval, old._lineage)
        self.frame, self.columns = frame, columns; self.growths += 1

    def load(self, slot, value):
        if type(value) is not int: raise TypeError('Expected integer')
        self.reserve(max(1, abs(value).bit_length()+1))
        self.columns[slot].load(value)
        return self

    def run(self, instructions):
        instructions = tuple(instructions)
        while True:
            try:
                self.frame.program(instructions, self.columns); self.runs += 1
                return self
            except OverflowError:
                self.reserve(min(240000, 2*self.frame.capacity.bit_length()))
                if self.frame.capacity.bit_length() >= 240000:
                    # One last attempt; do not loop at the configured resource limit.
                    self.frame.program(instructions, self.columns); self.runs += 1
                    return self

    def clear(self):
        for column in self.columns: column.clear()
        return self
