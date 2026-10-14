"""Executable integer claims from SharedClaims, on the miner's resident rods.

Conditions are explicit: modular equality is not integer equality; order needs
read-back. This evaluator establishes arithmetic claims, not SHA implications.
"""
from math import gcd, prod
from .shared_abacus import Calculation


class ClaimCalculator:
    """One reusable workspace per caller; immutable frames share the pool."""
    def __init__(self, pool=None, slots=128, bits=64):
        self.calculation = Calculation(slots=slots, bits=bits, pool=pool)
        self.next_slot = 0
        self.readbacks = 0; self.local_atoms = 0

    def formula(self, expression, variables):
        """Integers, variables, or add/sub/mul/pow/nsub formulas. nsub reads back and truncates at zero."""
        if self.next_slot >= len(self.calculation.columns):
            raise ValueError('Formula exceeds configured reusable slots')
        slot = self.next_slot; self.next_slot += 1
        if type(expression) is int:
            self.calculation.load(slot, expression)
        elif isinstance(expression, str):
            self.calculation.load(slot, variables[expression])
        else:
            if not isinstance(expression, (list, tuple)) or len(expression) != 3:
                raise ValueError('Expected a three-element integer formula')
            op, left, right = expression
            if op not in ('add', 'sub', 'mul', 'pow', 'nsub'):
                raise ValueError('Unsupported formula operation')
            a = self.formula(left, variables)
            if op == 'pow':
                if type(right) is not int or not 0 <= right <= 1000000:
                    raise ValueError('Power requires a bounded nonnegative integer exponent')
                instruction = (op, slot, a, 0, 0, right)
            else:
                b = self.formula(right, variables)
                if op == 'nsub':
                    x=self.calculation.columns[a].value(); y=self.calculation.columns[b].value()
                    self.readbacks += 2
                    if x < 0 or y < 0:raise ValueError('Natural subtraction requires nonnegative operands')
                    self.calculation.load(slot,max(0,x-y))
                    return slot
                instruction = (op, slot, a, b)
            self.calculation.run([instruction])
        return slot

    def decide(self, claim, variables=None):
        """eq/le/dvd atoms, and/or/not. Reports all reconstruction operations."""
        if variables is not None and not isinstance(variables, dict):
            raise ValueError("Variables must be a JSON object of integer assignments")
        self.calculation.clear(); self.next_slot = 0
        self.readbacks = 0; self.local_atoms = 0
        truth = self._claim(claim, variables or {})
        return {'truth': truth, 'local_atoms': self.local_atoms,
                'readbacks': self.readbacks, 'slots_used': self.next_slot,
                'capacity_bits': self.calculation.frame.capacity.bit_length(),
                'scope': 'Integer claim only; no Bitcoin exclusion implied'}

    def _claim(self, claim, variables):
        if not isinstance(claim, (tuple, list)) or not claim:
            raise ValueError('Expected a claim')
        op, *args = claim
        if op == 'not' and len(args) == 1:
            return not self._claim(args[0], variables)
        if op in ('and', 'or') and len(args) == 2:
            a = self._claim(args[0], variables)
            b = self._claim(args[1], variables)
            return a and b if op == 'and' else a or b
        if op not in ('eq', 'le', 'dvd') or len(args) != 2:
            raise ValueError('Unknown claim or arity')
        if op == 'dvd':
            divisor, expression = args
            if type(divisor) is not int or divisor <= 0:
                raise ValueError('Divisor must be a positive integer')
            slot = self.formula(expression, variables)
            column = self.calculation.columns[slot]
            if column.frame.capacity % divisor == 0:
                self.local_atoms += 1
                return all(r % gcd(divisor, m) == 0
                           for r, m in zip(column.residues, column.frame.moduli))
            self.readbacks += 1
            return column.value() % divisor == 0
        slot = self.formula(('sub', args[0], args[1]), variables)
        column = self.calculation.columns[slot]
        low, high = column.interval
        if op == 'eq' and -column.frame.capacity < low <= high < column.frame.capacity:
            self.local_atoms += 1
            return not any(column.residues)
        self.readbacks += 1
        value = column.value()
        return value == 0 if op == 'eq' else value <= 0


def count_polynomial_roots(frame, coefficients, max_rod=10000):
    """CRT root count of a univariate integer polynomial modulo capacity.

    This counts the complete residue domain, not an arbitrary nonce interval.
    Coefficients are low-degree first. No reconstruction or global enumeration.
    """
    coefficients = tuple(coefficients)
    if not coefficients or any(type(c) is not int for c in coefficients):
        raise ValueError('Expected integer polynomial coefficients')
    if any(m > max_rod for m in frame.moduli):
        raise ValueError('Per-rod enumeration exceeds configured work bound')
    counts = []
    for m in frame.moduli:
        count = 0
        for x in range(m):
            y = 0
            for c in reversed(coefficients): y = (y*x+c) % m
            count += y == 0
        counts.append(count)
    return {'count': prod(counts), 'per_rod': counts,
            'domain': frame.capacity, 'evaluations': sum(frame.moduli),
            'scope': 'Roots modulo complete CRT capacity; not Bitcoin winners'}
