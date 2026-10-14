"""Capacity-derived, outward-rounded algebraic intervals on coprime rods.

Scope: rational constants, negation, addition, subtraction, multiplication,
exact-rational scaling and nonnegative square roots. This is not the provider's
unavailable tm_real implementation and supplies no transcendental evaluator.
Arithmetic uses Python arbitrary precision; interval endpoints are residue
columns. Comparisons, rounding and roots reconstruct bounded representatives.
The policy is conservative: it proves every representative-sensitive raw
intermediate fits, rather than treating capacity bits as a precision heuristic.
Runtime checks and the separate Lean arithmetic lemmas are not a formal
verification of Python, allocation, or the whole CRT implementation.
"""
from dataclasses import dataclass
from fractions import Fraction
from math import isqrt

from .pqmath import RodAbacus, _integer, _rational


class CapacityError(ValueError):
    """The fixed rod frame cannot hold the requested scaled intermediates."""


class DomainIndeterminate(ValueError):
    """The enclosure cannot establish an operation's required domain."""


def _ceil_div(n, d):
    return -((-n) // d)


def _ceil_sqrt(n):
    root = isqrt(n)
    return root + (root * root != n)


@dataclass(frozen=True)
class Expr:
    """Immutable expression DAG. Floating-point constants are rejected."""
    kind: str
    args: tuple = ()
    constant: Fraction = Fraction(0)

    def __post_init__(self):
        arities = {'rat': 0, 'neg': 1, 'add': 2, 'sub': 2,
                   'mul': 2, 'scale': 1, 'sqrt': 1}
        if self.kind not in arities:
            raise ValueError('Unsupported algebraic expression')
        args = tuple(self.args)
        if len(args) != arities[self.kind] or any(not isinstance(x, Expr) for x in args):
            raise TypeError('Expression operands must match the operation arity')
        object.__setattr__(self, 'args', args)
        object.__setattr__(self, 'constant', _rational(self.constant, 'constant'))

    @classmethod
    def rational(cls, value):
        return cls('rat', constant=_rational(value, 'constant'))

    def __neg__(self):
        return Expr('neg', (self,))

    def __add__(self, other):
        return Expr('add', (self, other))

    def __sub__(self, other):
        return Expr('sub', (self, other))

    def __mul__(self, other):
        return Expr('mul', (self, other))

    def scale(self, value):
        return Expr('scale', (self,), _rational(value, 'scale'))

    def sqrt(self):
        return Expr('sqrt', (self,))


def _postorder(expr):
    """Iterative DAG traversal; syntax depth is not a mathematical limit."""
    if not isinstance(expr, Expr):
        raise TypeError('Expected an Expr')
    result, seen, stack = [], set(), [(expr, False)]
    while stack:
        node, ready = stack.pop()
        key = id(node)
        if key in seen:
            continue
        if ready:
            seen.add(key)
            result.append(node)
        else:
            stack.append((node, True))
            stack.extend((child, False) for child in reversed(node.args))
    return result


@dataclass(frozen=True)
class PrecisionPlan:
    """All endpoints <= magnitude*P; all stored intermediates <= peak(P).

    peak(P) = max(linear*P, quadratic*P*P), P = base**G.
    A product's pre-division bound and a root's scaled radicand are quadratic.
    Constants/denominators are exact parameters outside the rod frame.
    """
    capacity: int
    base: int
    magnitude: int
    linear: int
    quadratic: int
    max_places: int
    node_count: int

    def bound_at(self, places):
        _integer(places, 'working places', 0)
        p = self.base ** places
        return max(self.linear * p, self.quadratic * p * p)

    def admits(self, places):
        _integer(places, 'working places', 0)
        return places <= self.max_places


@dataclass(frozen=True)
class RodInterval:
    """An immutable interval plus its exact frame and scale identities."""
    rods: tuple
    places: int
    base: int
    lower: tuple
    upper: tuple


@dataclass(frozen=True)
class Reading:
    status: str
    places: int
    working_places: int
    max_places: int
    lower: int
    upper: int
    stages: int

    @property
    def certified(self):
        return self.status == 'certified'


class CapacityReals:
    """Fixed-frame algebraic interval service, without a magic guard count.

    Add rods by constructing a new service and reevaluating the expression.
    Reinterpreting old residues on a larger frame is expressly unsupported.
    A stage budget is separate from mathematical capacity and may be supplied
    to read(). Failure to certify never asserts that the value is an integer.
    """
    __slots__ = ('_frame', '_base')

    def __init__(self, rods, base=60):
        _integer(base, 'base', 2)
        self._frame = RodAbacus(tuple(rods))
        if not self.frame.rods:
            raise ValueError('A real interval frame needs at least one rod')
        self._base = base

    @property
    def frame(self):
        return self._frame

    @property
    def base(self):
        return self._base

    def _bounds(self, nodes):
        magnitudes, linear, quadratic = {}, 1, 0
        limit = (self.frame.capacity - 1) // 2

        def product(a, b):
            # Reject before allocating an enormous coefficient. Such a product
            # cannot fit even at P=1, so no requested precision could repair it.
            if b and a > limit // b:
                raise CapacityError('An intermediate exceeds capacity even at scale one')
            return a * b

        for node in nodes:
            args = [magnitudes[id(child)] for child in node.args]
            if node.kind == 'rat':
                bound = _ceil_div(abs(node.constant.numerator), node.constant.denominator)
            elif node.kind == 'neg':
                bound = args[0]
            elif node.kind in ('add', 'sub'):
                bound = args[0] + args[1]
            elif node.kind == 'mul':
                bound = product(args[0], args[1])
                quadratic = max(quadratic, bound)
            elif node.kind == 'scale':
                raw = product(args[0], abs(node.constant.numerator))
                linear = max(linear, raw)
                bound = _ceil_div(raw, node.constant.denominator)
            else:  # sqrt
                quadratic = max(quadratic, args[0])
                bound = _ceil_sqrt(args[0])
            if bound > limit:
                raise CapacityError('An endpoint bound exceeds capacity even at scale one')
            magnitudes[id(node)] = bound
            linear = max(linear, bound)
        return magnitudes, linear, quadratic

    def plan(self, expr):
        nodes = _postorder(expr)
        magnitudes, linear, quadratic = self._bounds(nodes)
        # Strict 2*B<M, computed without logarithms or approximate bit counts.
        limit = (self.frame.capacity - 1) // 2
        scale_limit = limit // linear
        if quadratic:
            scale_limit = min(scale_limit, isqrt(limit // quadratic))
        gmax = -1
        while scale_limit:
            gmax += 1
            scale_limit //= self.base
        return PrecisionPlan(self.frame.capacity, self.base, magnitudes[id(expr)],
                             linear, quadratic, gmax, len(nodes))

    def _encode(self, value):
        if 2 * abs(value) >= self.frame.capacity:
            raise CapacityError('Signed representative exceeds the strict frame range')
        return self.frame.reading(value)

    def _decode(self, column):
        value = self.frame.reconstruct(column)
        if 2 * value > self.frame.capacity:
            value -= self.frame.capacity
        if 2 * abs(value) >= self.frame.capacity:
            raise CapacityError('Half-capacity representatives are not admitted')
        return value

    def endpoints(self, interval):
        if not isinstance(interval, RodInterval):
            raise TypeError('Expected a RodInterval')
        if interval.rods != self.frame.rods or interval.base != self.base:
            raise ValueError('Interval frame or scale-base mismatch')
        _integer(interval.places, 'working places', 0)
        for column in (interval.lower, interval.upper):
            if len(column) != len(self.frame.rods):
                raise ValueError('Incomplete residue column')
            for r, m in zip(column, self.frame.rods):
                _integer(r, 'residue', 0)
                if r >= m:
                    raise ValueError('Noncanonical residue')
        lo, hi = self._decode(interval.lower), self._decode(interval.upper)
        if lo > hi:
            raise ValueError('Reversed interval endpoints')
        return lo, hi

    def enclose(self, expr, places):
        _integer(places, 'working places', 0)
        plan = self.plan(expr)
        if not plan.admits(places):
            raise CapacityError('Requested scale exceeds the expression/frame capacity')
        nodes = _postorder(expr)
        magnitudes, _, _ = self._bounds(nodes)
        p, intervals = self.base ** places, {}

        def store(lo, hi, bound):
            if lo > hi or max(abs(lo), abs(hi)) > bound:
                raise ArithmeticError('Interval violated its proved envelope')
            return (self._encode(lo), self._encode(hi))

        def local(left, right, operation, bound):
            column = tuple(operation(a, b) % m for a, b, m in
                           zip(left, right, self.frame.rods))
            value = self._decode(column)
            if abs(value) > bound:
                raise ArithmeticError('Rod operation exceeded its reserved bound')
            return value

        for node in nodes:
            args = [intervals[id(child)] for child in node.args]
            bound = magnitudes[id(node)] * p
            if node.kind == 'rat':
                q = node.constant
                lo, hi = q.numerator * p // q.denominator, _ceil_div(q.numerator * p, q.denominator)
            elif node.kind == 'neg':
                lo, hi = -self._decode(args[0][1]), -self._decode(args[0][0])
            elif node.kind in ('add', 'sub'):
                if node.kind == 'add':
                    lo = local(args[0][0], args[1][0], lambda a, b: a+b, bound)
                    hi = local(args[0][1], args[1][1], lambda a, b: a+b, bound)
                else:
                    lo = local(args[0][0], args[1][1], lambda a, b: a-b, bound)
                    hi = local(args[0][1], args[1][0], lambda a, b: a-b, bound)
            elif node.kind == 'mul':
                raw_bound = magnitudes[id(node.args[0])] * magnitudes[id(node.args[1])] * p * p
                corners = [local(a, b, lambda x, y: x*y, raw_bound)
                           for a in args[0] for b in args[1]]
                lo, hi = min(corners) // p, _ceil_div(max(corners), p)
            elif node.kind == 'scale':
                q = node.constant
                # Exact rational parameters need no modular denominator inverse.
                # A denominator sharing factors with a rod remains valid here.
                endpoints = [self._decode(x) * q.numerator for x in args[0]]
                for value in endpoints:
                    self._encode(value)  # Check the reserved raw numerator range.
                lo, hi = min(endpoints) // q.denominator, _ceil_div(max(endpoints), q.denominator)
            else:
                left, right = (self._decode(x) for x in args[0])
                if left < 0:
                    raise DomainIndeterminate('Square root requires a nonnegative enclosure')
                raw = (left*p, right*p)
                for value in raw:
                    self._encode(value)
                lo, hi = isqrt(raw[0]), _ceil_sqrt(raw[1])
            intervals[id(node)] = store(lo, hi, bound)
        lo_col, hi_col = intervals[id(expr)]
        return RodInterval(self.frame.rods, places, self.base, lo_col, hi_col)

    def read(self, expr, places, max_stages=None):
        """Certify a floor-scaled reading, or return an explicit unknown.

        Every scale from places to Gmax may be tried. Width alone cannot predict
        the next useful scale or prove boundary equality. No fixed-point failure
        is recast as an exactness violation. max_stages limits work, not truth.
        """
        _integer(places, 'output places', 0)
        if max_stages is not None:
            _integer(max_stages, 'stage budget', 1)
        plan = self.plan(expr)
        if not plan.admits(places):
            raise CapacityError('Output places exceed the expression/frame capacity')
        for stages, working in enumerate(range(places, plan.max_places + 1), 1):
            interval = self.enclose(expr, working)
            lo, hi = self.endpoints(interval)
            factor = self.base ** (working - places)
            lower, upper = lo // factor, hi // factor
            certificate = lo % factor + (hi - lo) < factor
            if certificate != (lower == upper):
                raise ArithmeticError('Euclidean floor certificate mismatch')
            if certificate:
                return Reading('certified', places, working, plan.max_places, lower, upper, stages)
            if max_stages is not None and stages >= max_stages and working < plan.max_places:
                return Reading('stage_budget_exhausted', places, working, plan.max_places, lower, upper, stages)
        return Reading('uncertified_at_capacity', places, working, plan.max_places, lower, upper, stages)
