"""Tested Python counterparts of Aristotle's rods/flowers/towers research.

These diagnostics are not Lean-extracted code and never filter Bitcoin nonces.
"""
from fractions import Fraction
from functools import lru_cache
from math import gcd, isqrt, lcm, prod
from .pqmath import _integer, is_prime
from .coreprimes import CORE, RADICAL, character


def prime_power_circle_count(prime, exponent, grid, rhs=1):
    """Unit-level conic count with the smooth Hensel hypotheses enforced."""
    _integer(prime,'prime',3); _integer(exponent,'exponent',1); _integer(rhs,'right hand side')
    if not is_prime(prime) or prime==2 or rhs%prime==0:
        raise ValueError('Requires an odd prime and a unit right hand side')
    if grid not in ('square','hexagonal'): raise ValueError('Unknown circle grid')
    if grid=='hexagonal' and prime==3:
        return 2*3**exponent if rhs%3==1 else 0
    return prime**(exponent-1)*rod_circle_count(prime,grid)


@lru_cache(maxsize=1)
def finite_dynamics():
    """Exact finite graphs from the compression reference; inspection only."""
    from collections import Counter, deque
    seen=set(); cycles=Counter()
    for x in range(7200):
        if x in seen: continue
        y=x; length=0
        while y not in seen: seen.add(y); length+=1; y=19*y%7200
        cycles[length]+=1
    graphs=[]
    for modulus in (8,9,5,360):
        successor=[x*x%modulus for x in range(modulus)]
        indegree=Counter(successor); queue=deque(x for x in range(modulus) if not indegree[x]); removed=0
        while queue:
            y=successor[queue.popleft()]; removed+=1; indegree[y]-=1
            if not indegree[y]: queue.append(y)
        graphs.append({'modulus':modulus,'cyclic_nodes':modulus-removed,'image_size':len(set(successor))})
    return {'multiply19_mod7200_cycles':dict(sorted(cycles.items())), 'squaring_graphs':graphs,
            'smooth_hensel_fibre_size':'p for a nonzero gradient modulo p',
            'bitcoin_exclusion_authority':False}


def rod_circle_count(prime, grid):
    """Number of solutions of x²+y²=1 or x²+xy+y²=1 modulo a prime.

    Excludes the ramified primes 2 (square) and 3 (hexagonal).
    """
    chi = character(prime, grid)
    if chi == 0:
        raise ValueError('Circle formula requires an unramified prime')
    return prime - chi


def crt_circle_count(primes, grid):
    """Multiply circle counts on distinct prime rods using CRT."""
    primes = tuple(primes)
    if len(set(primes)) != len(primes):
        raise ValueError('CRT requires distinct prime rods')
    if grid not in ('square', 'hexagonal'):
        raise ValueError('Grid must be square or hexagonal')
    return prod(rod_circle_count(p, grid) for p in primes)


def shell_count(dimensions, squared_radius):
    """Exact signed integer-coordinate count, by the Lean shell recurrence.

    The source checks this recurrence; its geometric interpretation is tested
    independently here, not proved by ShellEnrichment.lean.
    """
    _integer(dimensions, 'dimensions', 0)
    _integer(squared_radius, 'squared radius', 0)
    counts = [1] + [0] * squared_radius
    squares = [i*i for i in range(1, isqrt(squared_radius)+1)]
    for _ in range(dimensions):
        counts = [counts[n] + 2*sum(counts[n-s] for s in squares if s <= n)
                  for n in range(squared_radius+1)]
    return counts[squared_radius]


def _period(base, period, modulus):
    _integer(base, 'base', 0)
    _integer(period, 'period', 1)
    _integer(modulus, 'modulus', 1)
    if pow(base, period, modulus) != 1 % modulus:
        raise ValueError('Required modular period identity does not hold')


def tower3(a, b, c, modulus, outer_period, inner_period):
    """a^(b^c) modulo modulus, checking both period hypotheses first."""
    _integer(c, 'exponent', 0)
    _period(a, outer_period, modulus)
    _period(b, inner_period, outer_period)
    return pow(a, pow(b, c % inner_period, outer_period), modulus)


def tower4(a, b, c, d, modulus, outer_period, middle_period, inner_period):
    """a^(b^(c^d)) modulo modulus, under three checked identities."""
    _integer(d, 'exponent', 0)
    _period(a, outer_period, modulus)
    _period(b, middle_period, outer_period)
    _period(c, inner_period, middle_period)
    exponent = pow(b, pow(c, d % inner_period, middle_period), outer_period)
    return pow(a, exponent, modulus)


def split_with(n, base, exponent, exponent_primes):
    """Port OrderSplit.splitWith; return a proper factor or None.

    The density guarantee additionally needs n=p*q for distinct primes and
    lcm(p-1,q-1) dividing exponent. This is not general-purpose factoring.
    """
    _integer(n, 'modulus', 2)
    _integer(base, 'base', 0)
    _integer(exponent, 'exponent', 1)
    primes = tuple(exponent_primes)
    remaining = exponent
    for r in primes:
        _integer(r, 'exponent prime', 2)
        if not is_prime(r):
            raise ValueError('Exponent factors must be prime')
        while remaining % r == 0:
            remaining //= r
    if remaining != 1:
        raise ValueError('List must include all prime factors of the exponent')
    for r in primes:
        m, power = exponent, 0
        while m % r == 0:
            m //= r
            power += 1
        x = pow(base, m, n)
        for _ in range(power+1):
            factor = gcd(x+n-1, n)
            if 1 < factor < n:
                return factor
            x = pow(x, r, n)
    return None


def split_probability_lower_bound(p, q, exponent):
    """Uniform-base lower bound phi(p*q)/(2*p*q), with known prime factors."""
    for value in (p, q):
        _integer(value, 'prime factor', 2)
        if not is_prime(value):
            raise ValueError('Known factors must be prime')
    _integer(exponent, 'exponent', 1)
    if p == q or exponent % lcm(p-1, q-1):
        raise ValueError('Need distinct primes and a multiple of their key exponent')
    return Fraction((p-1)*(q-1), 2*p*q)


@lru_cache(maxsize=1)
def _report():
    from .archive_math import flower_boundary
    return {
        'source': 'reference/aristotle-rods-towers/',
        'compression_reference_geometry':{
            'flowers':[flower_boundary(k) for k in (1,2,4,14)],
            'finite_dynamics':finite_dynamics(),
            'prime_power_circles':[{'prime':p,'exponent':j,'grid':g,'count':prime_power_circle_count(p,j,g)}
                                   for p in (3,5,7,11,19) for j in (1,2,3) for g in ('square','hexagonal')],
            'reference':'COMPRESSION.md and the user all-k derivation; independently reviewed 2026-10-11',
            'scope':'Exact formulas and finite graphs; mathematical derivation plus tests, not a new Lean receipt'},
        'task_id': '81f0a318-7967-4c28-80cd-dd06e558ae4d',
        'prime_rod_circles': [{'prime': p, **{g: rod_circle_count(p, g)
                                for g in ('square', 'hexagonal')}} for p in CORE],
        'core_crt_circles': {g: crt_circle_count(CORE, g) for g in ('square', 'hexagonal')},
        'integer_shells': [{'squared_radius': n, **{str(d): shell_count(d, n)
                              for d in (2, 3, 4)}} for n in (1, *CORE, 121, 209)],
        'tower_7_11_core_period': 72,
        'tower_7_11_core_distinct_residues': len({tower3(7, 11, c, RADICAL, 30240, 72) for c in range(72)}),
        'factor_example': {'n': 11*19, 'base': 2, 'exponent': 144000,
                           'factor': split_with(11*19, 2, 144000, (2, 3, 5)),
                           'uniform_base_probability_lower_bound': str(split_probability_lower_bound(11, 19, 144000))},
        'scope': 'Tested Python ports, not formally verified Python. No SHA256d speedup or nonce exclusion. Shell geometry is independently tested; the source proves recurrence values.',
    }


def report():
    from copy import deepcopy
    return deepcopy(_report())
