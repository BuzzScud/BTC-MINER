"""Exact coordinates for the 96 allowed traversal steps on the 360 dial.

This is the finite multiplicative group of units modulo 360. The exponent
periods are group coordinates, not pairwise-coprime CRT moduli. Independent
Lean contracts are retained in the distillation workspace; this Python port
has finite correspondence tests, not a universal implementation proof.
"""
from functools import lru_cache
from itertools import product
from math import gcd

BASIS=(11,19,73,109)
PERIODS=(6,2,4,2)


def unit_from_coordinates(coordinates):
    coordinates=tuple(coordinates)
    if len(coordinates)!=4 or any(type(v) is not int or not 0<=v<n
                                  for v,n in zip(coordinates,PERIODS)):
        raise ValueError('Expected canonical exponent coordinates in 6 x 2 x 4 x 2')
    value=1
    for prime,exponent in zip(BASIS,coordinates):
        value=value*pow(prime,exponent,360)%360
    return value


@lru_cache(maxsize=1)
def _basis_table():
    table={unit_from_coordinates(c):c for c in product(*(range(n) for n in PERIODS))}
    if len(table)!=96 or set(table)!={u for u in range(360) if gcd(u,360)==1}:
        raise ArithmeticError('The prime-coordinate table does not cover the 360-dial units')
    return table


def unit_coordinates(step):
    if type(step) is not int or not 1<=step<360 or step not in _basis_table():
        raise ValueError('Traversal step must be a canonical unit modulo 360')
    return _basis_table()[step]
