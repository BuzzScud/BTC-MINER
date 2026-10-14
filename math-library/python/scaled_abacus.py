"""Resident, exact Q dictionaries and dynamically sized CRT workspaces.

Q denotes a supported product p*q here; k=lcm(p-1,q-1). The within-k
index is essential: k alone cannot recover Q. Dictionary bytes are not free.
"""
from array import array
from bisect import bisect_left
from functools import lru_cache
from itertools import combinations
from math import isqrt, lcm
from .pqmath import RodAbacus, _integer

SCALES = (144000, 3024000, 33264000)


class QCodec:
    def __init__(self, modulus):
        if modulus not in SCALES:
            raise ValueError('Use a reviewed Q scale: ' + str(SCALES))
        self.modulus = modulus
        divisors = set()
        for d in range(1, isqrt(modulus)+1):
            if modulus % d == 0:
                divisors.update((d, modulus//d))
        primes = [d+1 for d in sorted(divisors)
                  if all((d+1) % t for t in range(2, isqrt(d+1)+1))]
        pairs = sorted((p*q, lcm(p-1, q-1), p, q) for p, q in combinations(primes, 2))
        self.values = array('Q', (r[0] for r in pairs))
        self.clocks = array('Q', (r[1] for r in pairs))
        self.small_factors = array('I', (r[2] for r in pairs))
        self.groups = {}
        for i, k in enumerate(self.clocks):
            self.groups.setdefault(k, array('I')).append(i)
        self.bits = (len(pairs)-1).bit_length()

    def code(self, value):
        _integer(value, 'Q', 0)
        if value > 0xffffffffffffffff:
            return None
        i = bisect_left(self.values, value)
        return i if i < len(self.values) and self.values[i] == value else None

    def decode(self, code):
        _integer(code, 'code', 0)
        if code >= len(self.values):
            raise ValueError('Code outside this dictionary')
        return self.values[code]

    def coordinates(self, value):
        i = self.code(value)
        if i is None:
            return None  # caller retains an explicit raw-value escape
        k = self.clocks[i]
        p = self.small_factors[i]
        return {'k': k, 'index': self.groups[k].index(i), 'p': p, 'q': value//p}

    def from_coordinates(self, k, index):
        _integer(index, 'within-k index', 0)
        group = self.groups.get(k)
        if group is None or index >= len(group):
            raise ValueError('Unknown k/index pair')
        return self.decode(group[index])

    def pack(self, values):
        out = bytearray(); acc = used = count = 0
        for value in values:
            code = self.code(value)
            if code is None:
                raise ValueError('Q is outside this dictionary; retain it as a raw value')
            acc |= code << used; used += self.bits; count += 1
            while used >= 8:
                out.append(acc & 255); acc >>= 8; used -= 8
        if used:
            out.append(acc)
        return bytes(out), count

    def unpack(self, data, count):
        _integer(count, 'count', 0)
        if len(data) != (count*self.bits+7)//8:
            raise ValueError('Invalid packed length')
        out = []; acc = used = pos = 0
        for _ in range(count):
            while used < self.bits:
                acc |= data[pos] << used; used += 8; pos += 1
            out.append(self.decode(acc & ((1 << self.bits)-1)))
            acc >>= self.bits; used -= self.bits
        if acc:
            raise ValueError('Noncanonical padding')
        return out

    def description(self):
        tables = [self.values, self.clocks, self.small_factors, *self.groups.values()]
        return {'M': self.modulus, 'products': len(self.values), 'index_bits': self.bits,
                'k_classes': len(self.groups),
                'table_payload_bytes': sum(len(a)*a.itemsize for a in tables),
                'memory_note': 'Array payload only; Python object overhead is additional',
                'scope': 'Reversible supported-family encoding; unknown Q retained raw'}


@lru_cache(maxsize=3)
def q_codec(modulus=33264000):
    return QCodec(modulus)


class PrecisionAbacus:
    """Three coprime binary rods with cached CRT weights; no fixed integer width.

    Unsigned values grow the capacity before encoding. Signed values use an
    explicit sign. clear() reuses the workspace and the loaded CRT model.
    Allocation is proportional to the requested precision, subject to memory.
    This is integer arithmetic, not a fast arbitrary-size primality test.
    """
    def __init__(self, bits=8192):
        self.model = None; self.readings = [0, 0, 0]
        self.sign = 1; self.growths = 0; self.operations = 0
        self.reserve(bits)

    def reserve(self, bits):
        _integer(bits, 'bits', 1)
        if self.model is not None and self.model.capacity > (1 << bits):
            return
        previous = self.value() if self.model is not None else 0
        # 2^(3w)-2^w is strictly larger than every requested bits-bit value.
        w = max(2, (bits+3)//3)
        middle = 1 << w
        self.model = RodAbacus((middle-1, middle, middle+1))
        self.growths += 1
        self.clear()
        self.sign = -1 if previous < 0 else 1
        self.readings[:] = self.model.reading(abs(previous))

    def clear(self):
        self.readings[:] = (0, 0, 0); self.sign = 1

    def load(self, value):
        _integer(value, 'value')
        magnitude = abs(value)
        self.reserve(max(1, magnitude.bit_length()))
        self.sign = -1 if value < 0 else 1
        self.readings[:] = self.model.reading(magnitude)
        self.operations += 1
        return self

    def value(self):
        return self.sign*self.model.reconstruct(self.readings)

    def calculate(self, operation, a, b):
        _integer(a, 'a'); _integer(b, 'b')
        if operation not in ('add', 'multiply'):
            raise ValueError('Use add or multiply')
        # Signed addition needs cancellation; magnitude arithmetic still runs on
        # rods, after reserving an upper bound that prevents modular wraparound.
        self.reserve(max(1, max(abs(a).bit_length(), abs(b).bit_length())+1
                         if operation == 'add' else abs(a).bit_length()+abs(b).bit_length()+1))
        magnitude_bound = abs(a)+abs(b) if operation == 'add' else abs(a)*abs(b)
        signed_negative = (a+b < 0) if operation == 'add' else (a != 0 and b != 0 and ((a < 0) != (b < 0)))
        residues_a = self.model.reading(a); residues_b = self.model.reading(b)
        residues = [(x+y if operation == 'add' else x*y) % r
                    for x, y, r in zip(residues_a, residues_b, self.model.rods)]
        value = self.model.reconstruct(residues)
        if signed_negative:
            value -= self.model.capacity
        if abs(value) > magnitude_bound:
            raise ArithmeticError('CRT reconstruction exceeded the reserved range')
        self.load(value)
        return value

    def description(self):
        return {'capacity_bits': self.model.capacity.bit_length()-1,
                'rod_bits': [r.bit_length() for r in self.model.rods],
                'growths': self.growths, 'operations': self.operations,
                'dynamic_precision': True, 'signed': True, 'resident_workspace': True}
