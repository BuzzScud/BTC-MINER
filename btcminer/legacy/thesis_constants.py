"""
Thesis constants for miner: PHI, lattice dimensions, 12-fold clock position sets.

Single source for nonce/lattice constants used by thesis_mining. For the full
Custom Math set (φ, π×φ, lunar, Fib, retracements) the reference is:
  - Strategy Documents/Python Strategy 1 /custom_math/constants.py
  - Strategy Documents/CUSTOM_MATH_GOLDEN_FIB_LUNAR_SUMMARY.txt
"""
from __future__ import annotations

import math

# Phi (golden ratio) — aligned with Strategy constants.py for parity
PHI = 1.61803398874989484820
PHI_SQUARED = PHI * PHI
PHI_INVERSE = 1.0 / PHI

# Pi × Phi — Custom Math MATH_PI_TIMES_PHI (~5.083)
PI_TIMES_PHI = math.pi * PHI

# 500D lattice and sphere (platonic) radius — miner-specific
PLATONIC_RADIUS = 500
CLOCK_LATTICE_500D_DIMS = 500
TWO_PI = 2.0 * math.pi

# 12-fold clock position semantics (Custom Math thesis):
#
# CLOCK_O1_POSITIONS (3, 6, 9): Used for Clock Lattice O(1) seed prime.
#   Crystalline thesis: block_height % 12 in {3, 6, 9} yields deterministic
#   prime candidates (base + magnitude*12). Same "prime-aligned" set as
#   Strategy clock_lattice.is_prime_aligned_position (trading uses 3,6,9 for
#   ring/price mapping).
#
# SPHERE_PRIME_POSITIONS (1, 5, 7, 11): Used for sphere step count in
#   build_candidate_list (duality ordering over 12 spheres). Positions that
#   get more steps (40 vs 35). "Prime" here means the other four positions
#   on the 12-fold clock used for sphere hierarchy, not the same as O(1) set.
#
CLOCK_O1_POSITIONS = (3, 6, 9)
SPHERE_PRIME_POSITIONS = (1, 5, 7, 11)

# ---------------------------------------------------------------------------
# Crystalline thesis constants (Grok "Lunar Cycle Stability" conversation).
#
# The 12-fold clock is a 2D projection of a 12D hyper-torus whose axes are
# prime-modular circles.  The constants below capture the fractal, twin-prime,
# and modular-lunar layers that normalize the structure.
# ---------------------------------------------------------------------------

# Key primes that appear as boundary markers in the Crystalline prime-modular
# structure.  They emerge from the dualistic 0/1 oscillation (0-based vs
# 1-based counting always shifts the boundary to hit a prime).
CRYSTALLINE_PRIMES = (
    7, 11, 13, 29, 31, 41, 43, 47, 59, 61, 71, 89, 97,
    359, 431, 433, 719, 761, 4201, 4217, 4219, 21601, 43201,
    143999, 432001,
)

# Twin-prime pairs that flank key modular boundaries (the polarity-balancing
# rule: multiply/divide by 3 → twin primes appear, symmetric boundaries).
TWIN_PRIME_PAIRS = (
    (11, 13), (29, 31), (41, 43), (59, 61), (71, 73),
    (431, 433), (4217, 4219),
)

# Fractal ring distances from the 12-center-3 triangle.  Each ring is a
# self-similar copy of the prime-boundary structure (Platonic layers).
FRACTAL_RINGS = (7, 12, 20, 24, 30, 42)

# Lunar prime (synodic month ~29.53 days, 29 is prime) — "level 3 of the
# recursive zero-paired structure."
LUNAR_PRIME = 29

# Combined modular-lunar cycle: 61 × 12 + 29 = 762 units.
# 61 = prime boundary of the 60-minute layer; 12 = clock fold; 29 = lunar.
COMBINED_CYCLE = 762

# 12² = 144 (quadratic boundary); 144 × 3 = 432 (the normalizer).
# 432 sits as a fundamental set boundary inside the fractal; twin primes
# 431/433 flank it.
QUADRATIC_BOUNDARY = 144
NORMALIZER_432 = 432

# ---------------------------------------------------------------------------
# Polar prime lattice (E-S-F fabric model / Lattice-Twist Cascade).
#
# Each prime p_n occupies a polar position (r_n, θ_n) where:
#   r_n = cumulative product of previous primes (mod nonce space)
#   θ_n = 2π × (cumulative / p_n) mod 2π
# Conjugate positions fill gaps via harmonics:
#   θ_{n,k,m} = k × 2π × (p_m / p_n) mod 2π
#
# Nonce candidates from the lattice: int(r × |sin(θ)| % NONCE_MAX).
# The prime-harmonic resonance lock multiplies Q-factor by the prime product
# of the base triple (3 × 7 × 11 = 231).
# Cascade amplification occurs at back-reaction primes (e.g., 167).
# ---------------------------------------------------------------------------

POLAR_LATTICE_PRIMES = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31)
BACK_REACTION_PRIME = 167
PRIME_HARMONIC_Q = 231  # 3 × 7 × 11
POLAR_LATTICE_HARMONICS = 3
