"""Aristotle recurrence certificates, scoped to their specified integer orbits.

The C implementation is an independent secondary check. Both checks must
agree when C is available. It cannot decide anything about a Bitcoin nonce.
"""
import ctypes as C
from functools import lru_cache
from math import gcd, prod
import platform
from . import ROOT

FLOWER = dict(F=((5, 4), (6, 5)), starts=((1, 2), (3, 4)), coord=1,
              b=2, e=5, bpow=32, rods=(5, 7, 31), L=32, Q=60)
FIBONACCI = dict(F=((0, 1), (1, 1)), starts=((0, 1),), coord=1,
                 b=2, e=4, bpow=16, rods=(3,), L=24, Q=2)


def matrix_product(a, b, modulus):
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(2)) % modulus
                       for j in range(2)) for i in range(2))


def matrix_power(a, n, modulus):
    out = ((1, 0), (0, 1))
    while n:
        if n & 1:
            out = matrix_product(out, a, modulus)
        a = matrix_product(a, a, modulus); n >>= 1
    return out


def validate_parameters(c):
    try:
        b, e, bpow, L, Q, coord = (c[k] for k in ('b', 'e', 'bpow', 'L', 'Q', 'coord'))
        if any(type(x) is not int for x in (b, e, bpow, L, Q, coord)):
            return False
        if not (2 <= b <= 0xffffffff and 1 <= e <= 31 and 0 < bpow <= 0xffffffff
                and 1 <= L <= 10000 and 1 <= Q <= 10000 and coord in (0, 1)):
            return False
        if b**e != bpow or len(c['rods']) > 32 or not 1 <= len(c['starts']) <= 64:
            return False
        # Resource bounds are separate from mathematical validity; reject
        # unsupported certificates instead of letting an unbounded C loop run.
        if len(c['starts'])*L*Q > 2000000:
            return False
        capacity = bpow
        for r in c['rods']:
            if type(r) is not int or not 2 <= r <= 0xffffffff or gcd(capacity, r) != 1:
                return False
            capacity *= r
        if len(c['F']) != 2 or any(len(row) != 2 for row in (*c['F'], *c['starts'])):
            return False
        return all(type(v) is int and -(1 << 63) <= v < 1 << 63
                   for row in (*c['F'], *c['starts']) for v in row)
    except (KeyError, TypeError, OverflowError):
        return False


def python_verify(c):
    if not validate_parameters(c):
        return False
    odd = prod(c['rods']); modulus = c['bpow']*odd
    if matrix_power(c['F'], c['L'], modulus) != ((1, 0), (0, 1)):
        return False
    if pow(c['b'], c['Q'], odd) != 1 % odd:
        return False
    powers = {pow(c['b'], j, odd) for j in range(c['Q'])}
    for start in c['starts']:
        x, y = (v % modulus for v in start)
        for _ in range(c['L']):
            value = (x, y)[c['coord']]
            if value % c['bpow'] == 0 and value % odd in powers:
                return False
            x, y = ((c['F'][0][0]*x+c['F'][0][1]*y) % modulus,
                    (c['F'][1][0]*x+c['F'][1][1]*y) % modulus)
    return True


class Certificate(C.Structure):
    _fields_ = [('b', C.c_uint32), ('e', C.c_uint32), ('bpow', C.c_uint32),
                ('nrods', C.c_size_t), ('rods', C.c_uint32*32),
                ('L', C.c_uint32), ('Q', C.c_uint64)]


@lru_cache(maxsize=1)
def native_verifier():
    path = ROOT/'native'/__import__('btcminer.platform_support', fromlist=['native_name']).native_name('librodsieve')
    try:
        lib = C.CDLL(str(path))
        fn = lib.lc_rodsieve_verify
        fn.argtypes = [C.POINTER(Certificate), C.POINTER(C.c_int64*2),
                       C.POINTER(C.c_int64*2), C.c_size_t, C.c_int]
        fn.restype = C.c_int
        return fn
    except (OSError, AttributeError):
        return None


def verify(c):
    py = python_verify(c)
    fn = native_verifier(); native = None
    if fn is not None and validate_parameters(c):
        cert = Certificate(c['b'], c['e'], c['bpow'], len(c['rods']),
                           (C.c_uint32*32)(*c['rods']), c['L'], c['Q'])
        matrix = ((C.c_int64*2)*2)(*((C.c_int64*2)(*r) for r in c['F']))
        starts = ((C.c_int64*2)*len(c['starts']))(*((C.c_int64*2)(*r) for r in c['starts']))
        native = fn(C.byref(cert), matrix, starts, len(c['starts']), c['coord'])
    return {'valid': py and (native is None or native == 1), 'python_valid': py,
            'native_result': native, 'native_available': fn is not None,
            'scope': 'Specified recurrence orbits only; excludes powers b^j for j >= e',
            'bitcoin_nonce_exclusions': 0}


@lru_cache(maxsize=1)
def published_certificates():
    return {'flower': verify(FLOWER), 'fibonacci': verify(FIBONACCI)}
