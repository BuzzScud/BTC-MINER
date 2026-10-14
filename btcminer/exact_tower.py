"""Bounded exact modular towers for the legacy miner's height-three seed.

T(0)=1, T(h+1)=a**T(h), with 0**0=1. This implementation supports
heights 0..3 and unsigned 64-bit operands. It never constructs a**a.
Factorization is exact, but deliberately bounded; unsupported factorization
work raises TowerBudgetError instead of returning an approximate residue.
This is tested Python arithmetic, not Lean-extracted or constant-time code.
"""
from functools import lru_cache
from math import prod

TOWER_VERSION = "exact-tower-v2"
UINT64_MAX = (1 << 64) - 1
MAX_FACTOR_TRIALS = 100_000
UINT64_FACTORS = ((3, 1), (5, 1), (17, 1), (257, 1), (641, 1),
                  (65537, 1), (6700417, 1))


class TowerBudgetError(ValueError):
    """The requested exact calculation exceeds the declared resource domain."""


def _natural(value, name, maximum):
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(name + " must be an integer")
    if not 0 <= value <= maximum:
        raise TowerBudgetError(name + " is outside the supported range 0.." + str(maximum))


@lru_cache(maxsize=128)
def _factor_small_or_budgeted(n):
    """Exact trial division, capped at MAX_FACTOR_TRIALS trial divisors."""
    remaining, divisor, trials = n, 2, 0
    factors = []
    while divisor * divisor <= remaining:
        if trials >= MAX_FACTOR_TRIALS:
            raise TowerBudgetError("Exact modulus factorization exceeded the trial budget")
        trials += 1
        exponent = 0
        while remaining % divisor == 0:
            remaining //= divisor
            exponent += 1
        if exponent:
            factors.append((divisor, exponent))
        divisor = 3 if divisor == 2 else divisor + 2
    if remaining > 1:
        factors.append((remaining, 1))
    return tuple(factors)


@lru_cache(maxsize=1)
def _checked_uint64_factors():
    # Validate the fixed table once with independent exact trial division.
    if prod(p ** e for p, e in UINT64_FACTORS) != UINT64_MAX:
        raise ArithmeticError("Invalid UINT64_MAX factor product")
    for p, e in UINT64_FACTORS:
        if e != 1 or _factor_small_or_budgeted(p) != ((p, 1),):
            raise ArithmeticError("Invalid UINT64_MAX prime factor")
    return UINT64_FACTORS


def _capped_power(base, exponent, cap):
    """Return min(base**exponent, cap) without a large intermediate integer.

    Called with cap<=64. For base>=2, at most ceil(log2(cap)) products
    are required before saturation; zero and one are handled explicitly.
    """
    if exponent == 0:
        return min(1, cap)
    if base < 2:
        return min(base, cap)
    result = 1
    while exponent and result < cap:
        result = min(result * base, cap)
        exponent -= 1
    return result


def tetration_mod(base, height, modulus):
    """Return the exact right-associated tower modulo a positive modulus.

    For height3, write modulus as pairwise coprime prime powers q=p**e.
    If p does not divide a, Euler's period phi(q) allows replacing the outer
    exponent a**a by pow(a,a,phi(q)). If p divides a, v_p(a**E)=v_p(a)*E;
    the residue is zero once E reaches ceil(e/v_p(a)). Below that threshold
    E is computed exactly by the capped power. CRT combines the residues.

    No inner Euler shortcut is used: a need not be coprime to phi(q).
    rodmath.tower3 requires an additional inner-period identity that these
    inputs do not generally satisfy. Its unchecked use would reintroduce
    the same class of bug.
    """
    _natural(base, "base", UINT64_MAX)
    _natural(height, "height", 3)
    _natural(modulus, "modulus", UINT64_MAX)
    if modulus == 0:
        raise ValueError("modulus must be positive")
    if modulus == 1:
        return 0
    if height == 0:
        return 1
    if height == 1:
        return base % modulus
    if height == 2:
        return pow(base, base, modulus)
    if base < 2:
        return base  # height3: 0**(0**0)=0 and 1**(1**1)=1.

    factors = (_checked_uint64_factors() if modulus == UINT64_MAX
               else _factor_small_or_budgeted(modulus))
    result, capacity = 0, 1
    for p, e in factors:
        q = p ** e
        if base % p:
            period = (p - 1) * p ** (e - 1)
            residue = pow(base, pow(base, base, period), q)
        else:
            valuation, remaining = 0, base
            while remaining % p == 0:
                remaining //= p
                valuation += 1
            threshold = (e + valuation - 1) // valuation
            exponent = _capped_power(base, base, threshold)
            residue = 0 if exponent == threshold else pow(base, exponent, q)
        result += capacity * ((residue - result) * pow(capacity, -1, q) % q)
        capacity *= q
    return result
