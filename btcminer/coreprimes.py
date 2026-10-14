"""Exact executable counterparts of selected CorePrimes.lean results.

Used by the miner's math diagnostics. These Python ports are regression tested,
not formally extracted. Circle counts do not predict Bitcoin hash outcomes.
"""
from math import gcd, prod
from .pqmath import RodAbacus, _integer, is_prime

CORE = (11, 19, 71, 97, 109)
RADICAL = prod(CORE)
SQUARE_RODS = RodAbacus(tuple(p*p for p in CORE))


def character(prime, grid):
    _integer(prime, 'prime', 2)
    if grid not in ('square', 'hexagonal'):
        raise ValueError('Grid must be square or hexagonal')
    if not is_prime(prime):
        raise ValueError('The scale factor must be prime')
    modulus = 4 if grid == 'square' else 3
    if prime == (2 if grid == 'square' else 3):
        return 0
    return 1 if prime % modulus == 1 else -1


def prime_power_multiplier(prime, exponent, grid, base=1):
    """Count multiplier for squared radius base*p**exponent; p must not divide base."""
    _integer(exponent, 'exponent', 0)
    _integer(base, 'base squared radius', 1)
    chi = character(prime, grid)
    if base % prime == 0:
        raise ValueError('Scaling law requires the prime not to divide the base')
    if chi == 0:
        return 1
    return exponent + 1 if chi == 1 else int(exponent % 2 == 0)


def circle_count(factors, grid):
    """Exact lattice count from a supplied positive integer prime factorization.

    Keys are distinct primes, values their exponents. This does not recover
    the factors of an unknown integer. The empty factorization represents 1.
    """
    if grid not in ('square', 'hexagonal'):
        raise ValueError('Grid must be square or hexagonal')
    return (4 if grid == 'square' else 6) * prod(
        prime_power_multiplier(p, e, grid) for p, e in factors.items())


def core_scale_multiplier(exponent, grid, base=1):
    _integer(exponent, 'exponent', 0)
    _integer(base, 'base squared radius', 1)
    if gcd(base, RADICAL) != 1:
        raise ValueError('Core scaling requires a base coprime to every core prime')
    if grid not in ('square', 'hexagonal'):
        raise ValueError('Grid must be square or hexagonal')
    return (exponent + 1) ** (2 if grid == 'square' else 3) if exponent % 2 == 0 else 0


def normalize_scaled(value, scale, modulus):
    """Undo modular scaling only when the scale is invertible."""
    _integer(value, 'value')
    _integer(scale, 'scale', 1)
    _integer(modulus, 'modulus', 2)
    if gcd(scale, modulus) != 1:
        raise ValueError('Scale loses information on these rods and cannot be normalized')
    return value * pow(scale, -1, modulus) % modulus


def report(clock=144000):
    from .rodmath import rod_circle_count
    _integer(clock, 'clock', 1)
    exponent = 1
    for p in CORE:
        exponent = exponent * (p-1) // gcd(exponent, p-1)
    return {
        'source': 'reference/aristotle-core-primes/CorePrimes.lean',
        'core_primes': list(CORE), 'radical': RADICAL,
        'square_rods': list(SQUARE_RODS.rods), 'crt_capacity': SQUARE_RODS.capacity,
        'classification': [{'prime': p, 'mod12': p % 12,
                            'square_splits': character(p, 'square') == 1,
                            'hexagonal_splits': character(p, 'hexagonal') == 1,
                            'qualifies_for_miner_clock': clock % (p-1) == 0,
                            'integer_unit_group_order':p-1,
                            'square_norm_one_group_order':rod_circle_count(p,'square'),
                            'hex_norm_one_group_order':rod_circle_count(p,'hexagonal'),
                            'hex_petal_spoke':(p+3)//6,
                            'hex_circle_clock_closes':clock % rod_circle_count(p,'hexagonal') == 0,
                            'hex_power_lands_in_petals':clock % ((p+3)//6) == 0} for p in CORE],
        'nineteen_squared_radius_multipliers': {g: prime_power_multiplier(19, 2, g) for g in ('square', 'hexagonal')},
        'core_squared_radius_multipliers': {g: core_scale_multiplier(2, g) for g in ('square', 'hexagonal')},
        'core_squared_coordinate_multipliers': {g: core_scale_multiplier(4, g) for g in ('square', 'hexagonal')},
        'scaling_precondition': 'Base squared radius must be positive and coprime to the scale primes.',
        'pair_97_109_circle_points': {g: circle_count({97: 1, 109: 1}, g) for g in ('square', 'hexagonal')},
        'core_exponent': exponent,
        'nineteen_squared_mod360': pow(19, 2, 360),
        'nineteen_squared_on_own_square_rod': pow(19, 2, 19*19),
        'square_rod_exponent_warning': 'p^(k+1) is not p modulo p^2 for any k >= 1; prime-rod exponent identities do not extend to squares.',
        'scope': 'Exact rod and lattice diagnostics; no demonstrated SHA256d advantage or nonce exclusion rule.',
    }
