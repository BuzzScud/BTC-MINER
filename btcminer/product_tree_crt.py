"""Reusable arbitrary-precision product-tree CRT over pairwise coprime rods.

The tree is balanced by leaf count (not by bit width). At every internal node
merge(a,b) = a + L * (((b-a) * inverse(L,R)) mod R). Python integers retain
all bits. Construction validates coprimality at every sibling product; this
covers every pair of leaves at their lowest common ancestor. No primality or
machine-word bound is needed. Empty frames have capacity 1 and decode to 0.

A plan stores O(log n) levels, n-1 inverses, and O(B log n) product bits for
B = sum(bit_length(m_i)); it does not claim constant-time arithmetic. Plans
belong to reusable frames, with no unbounded process-global plan cache.
"""
from dataclasses import dataclass, field
from math import gcd


def _integer(value, label):
    if type(value) is not int:
        raise TypeError(label + ' must be an integer (not bool)')
    return value


@dataclass(frozen=True)
class ProductTreeCRT:
    moduli: tuple = ()
    capacity: int = field(init=False)
    levels: tuple = field(init=False, repr=False)
    products: tuple = field(init=False, repr=False)

    def __post_init__(self):
        moduli = tuple(self.moduli)
        for modulus in moduli:
            if _integer(modulus, 'modulus') < 2:
                raise ValueError('CRT moduli must be at least 2')
        products = [moduli]
        levels = []
        current = moduli
        while len(current) > 1:
            nodes, following = [], []
            for i in range(0, len(current), 2):
                left = current[i]
                if i + 1 == len(current):
                    nodes.append((left, None, None))
                    following.append(left)
                else:
                    right = current[i+1]
                    if gcd(left, right) != 1:
                        raise ValueError('CRT moduli must be pairwise coprime')
                    nodes.append((left, right, pow(left, -1, right)))
                    following.append(left * right)
            levels.append(tuple(nodes))
            current = tuple(following)
            products.append(current)
        object.__setattr__(self, 'moduli', moduli)
        object.__setattr__(self, 'capacity', current[0] if current else 1)
        object.__setattr__(self, 'levels', tuple(levels))
        object.__setattr__(self, 'products', tuple(products))

    def encode(self, value):
        """Remainder-tree encoding, including negative/unbounded integers."""
        _integer(value, 'value')
        if not self.moduli:
            return ()
        values = [value % self.capacity]
        for products in reversed(self.products[:-1]):
            values = [values[i//2] % modulus for i, modulus in enumerate(products)]
        return tuple(values)

    def decode(self, residues):
        """Canonical representative in [0,M); arbitrary residues normalize."""
        residues = tuple(residues)
        if len(residues) != len(self.moduli):
            raise ValueError('Provide exactly one residue per modulus')
        values = [_integer(r, 'residue') % m for r, m in zip(residues, self.moduli)]
        for nodes in self.levels:
            following = []
            for i, (left, right, inverse) in enumerate(nodes):
                a = values[2*i]
                if right is None:
                    following.append(a)
                else:
                    b = values[2*i+1]
                    following.append(a + left * (((b-a)*inverse) % right))
            values = following
        return values[0] if values else 0

    def decode_interval(self, residues, low, high):
        """Unique lift into inclusive [low,high], whose width must be < M.

        An interval supplied by a caller is an assumption, not evidence of the
        original integer's range. Shared columns derive and seal their ranges.
        If the congruence has no representative in the interval, reject it.
        """
        _integer(low, 'low'); _integer(high, 'high')
        if low > high:
            raise ValueError('Interval endpoints are reversed')
        if high-low >= self.capacity:
            raise OverflowError('Interval is ambiguous at this CRT capacity')
        residue = self.decode(residues)
        value = low + (residue-low) % self.capacity
        if value > high:
            raise ArithmeticError('Residues contradict the declared interval')
        return value
