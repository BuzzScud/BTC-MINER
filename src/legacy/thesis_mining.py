"""
Thesis-aligned mining logic integrated from C miner.

Provides: deterministic base nonce, recovery suggested nonce, sphere hopping,
duality ordering, golden-ratio spiral, candidate list generation.
500D lattice and quadrant partition for 4-worker nonce search (full 32-bit
space; thesis ch.15 unbiased search preserved).

12-fold clock: positions 3,6,9 = clock-screened seed prime; positions 1,5,7,11 =
sphere step count (duality). See thesis_constants and Strategy
Documents/PYTHON STRAT/CLOCK LATTICE.txt.
"""
from __future__ import annotations

import math
import os
import sys
import threading
from ctypes import CDLL, POINTER, Structure, byref, c_bool, c_double, c_int, c_size_t, c_uint32, c_uint64
from typing import Optional

from btcminer.exact_tower import TOWER_VERSION, tetration_mod
from config import use_c_candidates, use_c_nonce
from thesis_constants import (
    BACK_REACTION_PRIME,
    CLOCK_LATTICE_500D_DIMS,
    CLOCK_O1_POSITIONS,
    COMBINED_CYCLE,
    CRYSTALLINE_PRIMES,
    FRACTAL_RINGS,
    LUNAR_PRIME,
    NORMALIZER_432,
    PHI,
    PLATONIC_RADIUS,
    POLAR_LATTICE_HARMONICS,
    POLAR_LATTICE_PRIMES,
    PRIME_HARMONIC_Q,
    QUADRATIC_BOUNDARY,
    SPHERE_PRIME_POSITIONS,
    TWIN_PRIME_PAIRS,
    TWO_PI,
)

# Probe timeout: if C nonce call does not return within this many seconds, disable C path.
_NONCE_C_PROBE_TIMEOUT_SEC = 8.0

NONCE_MAX = 0xFFFFFFFF

# Optional historical C helpers. Base-nonce generation uses the exact Python
# tower until a separate C implementation has passed the same arithmetic gates.
_libnonce = None
_base_nonce_source: str = "python"
_recovery_loaded: Optional[bool] = None  # set on first recovery_suggested_nonce attempt
_last_seed_prime_path: Optional[str] = None  # "clock_o1" or "sft"

# First 500 primes (aligned with C clock_lattice_500d); filled on first use
_CLOCK_LATTICE_FREQUENCIES_500D: list[int] = []


class _NonceConfig(Structure):
    _fields_ = [
        ("block_height", c_uint64),
        ("difficulty_bits", c_uint32),
        ("tetration_depth", c_uint32),
        ("max_reassessments", c_uint32),
        ("entropy_cut_min", c_double),
        ("entropy_cut_max", c_double),
    ]


class _NonceResult(Structure):
    _fields_ = [
        ("nonce", c_uint64),
        ("seed_prime", c_uint64),
        ("reassessments", c_uint32),
        ("success", c_bool),
        ("final_entropy", c_double),
    ]


def _find_c_math_root() -> str | None:
    """Return project root containing 'c. math' so C lib loads from any run context."""
    from pathlib import Path
    from btcminer import ROOT
    root = ROOT
    candidates = [root / "optional", root]
    for parent in candidates:
        if (parent / "c. math" / "algorithms").is_dir():
            return str(parent)
    return None


def _load_libnonce() -> bool:
    """Load libalgorithms (C micro model) when available. Returns True if loaded."""
    global _libnonce
    if _libnonce is not None:
        return _libnonce is not False
    project_root = _find_c_math_root()
    if not project_root:
        _libnonce = False
        return False
    c_math = os.path.join(project_root, "c. math")
    alg_dir = os.path.join(c_math, "algorithms")
    math_lib_dir = os.path.join(c_math, "math", "lib")
    for name in ("libalgorithms.dylib", "libalgorithms.so"):
        path = os.path.join(alg_dir, name)
        if os.path.isfile(path):
            try:
                math_so = os.path.join(math_lib_dir, "libcrystallinemath.so")
                if os.path.isfile(math_so):
                    CDLL(math_so)
                _libnonce = CDLL(path)
                break
            except Exception:
                pass
    if _libnonce is None:
        _libnonce = False
        return False

    _libnonce.nonce_config_init.argtypes = [
        POINTER(_NonceConfig),
        c_uint64,
        c_uint32,
    ]
    _libnonce.nonce_config_init.restype = None
    _libnonce.nonce_generate_deterministic.argtypes = [
        POINTER(_NonceConfig),
        POINTER(_NonceResult),
    ]
    _libnonce.nonce_generate_deterministic.restype = c_bool

    if hasattr(_libnonce, "build_candidate_list_sphere"):
        _libnonce.build_candidate_list_sphere.argtypes = [
            c_uint32,
            c_uint32,
            c_uint32,
            c_uint32,
            POINTER(c_uint32),
            c_size_t,
            POINTER(c_size_t),
        ]
        _libnonce.build_candidate_list_sphere.restype = c_int

    # One-time probe: C nonce can hang on some platforms (e.g. slow abacus_mod_exp). If it
    # does not return within timeout, disable C so the miner always uses Python.
    probe_ok = [None]

    def _probe() -> None:
        try:
            cfg = _NonceConfig()
            res = _NonceResult()
            _libnonce.nonce_config_init(byref(cfg), c_uint64(3), c_uint32(24))
            if _libnonce.nonce_generate_deterministic(byref(cfg), byref(res)):
                probe_ok[0] = True
            else:
                probe_ok[0] = False
        except Exception:
            probe_ok[0] = False

    th = threading.Thread(target=_probe, daemon=True)
    th.start()
    th.join(timeout=_NONCE_C_PROBE_TIMEOUT_SEC)
    if probe_ok[0] is not True:
        _libnonce = False  # already global at function start
        return False
    return True


def _nonce_from_c(block_height: int, difficulty_bits: int) -> Optional[int]:
    """Return base nonce from C micro model, or None if unavailable/failed."""
    if not _load_libnonce() or _libnonce is False:
        return None
    try:
        config = _NonceConfig()
        result = _NonceResult()
        _libnonce.nonce_config_init(
            byref(config), c_uint64(block_height), c_uint32(difficulty_bits)
        )
        if not _libnonce.nonce_generate_deterministic(byref(config), byref(result)):
            return None
        return (result.nonce & NONCE_MAX)
    except Exception:
        return None


def _fill_frequencies_500d() -> None:
    global _CLOCK_LATTICE_FREQUENCIES_500D
    if _CLOCK_LATTICE_FREQUENCIES_500D:
        return
    count = 0
    n = 2
    while count < CLOCK_LATTICE_500D_DIMS:
        if _is_prime(n):
            _CLOCK_LATTICE_FREQUENCIES_500D.append(n)
            count += 1
        n += 1


def _get_frequencies_500d() -> list[int]:
    _fill_frequencies_500d()
    return _CLOCK_LATTICE_FREQUENCIES_500D


def nonce_to_base_angle(nonce: int) -> float:
    """Base angle for 500D lattice: (nonce * PI * PHI) mod 2*PI."""
    return (nonce * math.pi * PHI) % TWO_PI


def quadrant_from_nonce(nonce: int) -> int:
    """Quadrant 0..3 for 4-worker partition. Worker w takes quadrant w."""
    base_angle = nonce_to_base_angle(nonce & NONCE_MAX)
    return int(4.0 * base_angle / TWO_PI) % 4


def nonce_to_lattice_500d(nonce: int) -> list[float]:
    """Map nonce to 500D position (same formula as C)."""
    _fill_frequencies_500d()
    base_angle = nonce_to_base_angle(nonce & NONCE_MAX)
    freqs = _get_frequencies_500d()
    return [
        math.cos(base_angle * freqs[d]) * (PHI ** (d % 5))
        for d in range(CLOCK_LATTICE_500D_DIMS)
    ]


def _is_prime(n: int) -> bool:
    """Simple primality check for n >= 2."""
    if n < 2:
        return False
    if n <= 3:
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0:
            return False
        i += 6
    return True


def bits_compact_to_difficulty_bits(bits_int: int) -> int:
    """
    Convert Bitcoin compact 'bits' to difficulty_bits (1-64) for entropy scaling.
    C nonce_apply_difficulty_bounds expects 1-64; raw compact bits (e.g. 0x207fffff)
    would skip entropy reduction. Extract exponent and map to 1-64.
    """
    exp = (bits_int >> 24) & 0xFF
    return min(64, max(1, exp))


def _primes_up_to(limit: int) -> list[int]:
    """Return primes <= limit for the clock's growing trial-factor screen."""
    if limit < 2:
        return []
    out: list[int] = [2]
    n = 3
    while n <= limit:
        if _is_prime(n):
            out.append(n)
        n += 2
    return out


def _has_interference_o1(base: int, magnitude: int) -> bool:
    """
    Check if candidate = base + magnitude*12 is composite via interference.
    The historical name is retained for compatibility. Trial work grows with
    the square root of the candidate; no O(1) prime-generation claim is made.
    """
    candidate = base + magnitude * 12
    if candidate < 2:
        return True
    if candidate in (2, 3):
        return False
    if candidate % 2 == 0 or candidate % 3 == 0:
        return True
    limit = math.isqrt(candidate)
    primes = _primes_up_to(limit)
    for p in primes:
        if p <= 3:
            continue
        try:
            inv12 = pow(12, -1, p)
        except ValueError:
            continue
        interference_mod = (-base * inv12) % p
        if magnitude % p == interference_mod:
            return True
    return False


def _clock_o1_seed_prime(block_height: int) -> int | None:
    """
    Clock-screened seed prime, at positions in CLOCK_O1_POSITIONS (3, 6, 9).
    Historical identifier retained; screening and integer costs are not O(1).
    Returns None if position not in {3,6,9} or candidate is composite.
    """
    position = block_height % 12
    magnitude = block_height // 12
    if position not in CLOCK_O1_POSITIONS:
        return None
    base_map = {3: 5, 6: 7, 9: 11}
    base = base_map[position]
    if _has_interference_o1(base, magnitude):
        return None
    return base + magnitude * 12


# --- SFT (Symbolic Field Theory) - from c. math algorithms/src/symbolic_field_theory.c ---


def _sft_omega(x: int) -> int:
    """ω(x) = number of distinct prime factors."""
    if x <= 1:
        return 0
    if x == 2:
        return 1
    count = 0
    n = x
    if n % 2 == 0:
        count += 1
        while n % 2 == 0:
            n //= 2
    i = 3
    while i * i <= n:
        if n % i == 0:
            count += 1
            while n % i == 0:
                n //= i
        i += 2
    if n > 1:
        count += 1
    return count


def _sft_psi_hybrid(x: int) -> int:
    """ψ(x) = (x mod 6) - ω(x)."""
    return (x % 6) - _sft_omega(x)


def _sft_kappa(x: int, psi: int) -> int:
    """κ(x) = ⌊(x - ψ)² / x⌋."""
    if x == 0:
        return 0
    diff = x - psi
    diff_sq = diff * diff
    return diff_sq // x


def _sft_find_collapse_zones(start: int, end: int) -> list[tuple[int, int, int, int]]:
    """Find collapse zones (local minima of κ). Returns list of (start, end, min_kappa, candidate)."""
    if start >= end:
        return []
    zones: list[tuple[int, int, int, int]] = []
    prev_psi = _sft_psi_hybrid(start)
    prev_kappa = _sft_kappa(start, prev_psi)
    curr_psi = _sft_psi_hybrid(start + 1)
    curr_kappa = _sft_kappa(start + 1, curr_psi)
    in_zone = False
    zone_start = 0
    min_kappa = (1 << 63) - 1
    min_candidate = 0
    for x in range(start + 2, end + 1):
        next_psi = _sft_psi_hybrid(x)
        next_kappa = _sft_kappa(x, next_psi)
        if curr_kappa < prev_kappa and curr_kappa < next_kappa:
            if not in_zone:
                zone_start = x - 1
                min_kappa = curr_kappa
                min_candidate = x - 1
                in_zone = True
            else:
                if curr_kappa < min_kappa:
                    min_kappa = curr_kappa
                    min_candidate = x - 1
        elif in_zone and curr_kappa > prev_kappa:
            zones.append((zone_start, x - 1, min_kappa, min_candidate))
            in_zone = False
            min_kappa = (1 << 63) - 1
        prev_psi, prev_kappa = curr_psi, curr_kappa
        curr_psi, curr_kappa = next_psi, next_kappa
    if in_zone:
        zones.append((zone_start, end, min_kappa, min_candidate))
    return zones


def _sft_deterministic_prime_map(start: int, end: int, max_primes: int = 100) -> list[int]:
    """SFT prime discovery: collapse zones -> primality test. Returns sorted unique primes."""
    if start >= end or max_primes <= 0:
        return []
    zones = _sft_find_collapse_zones(start, end)
    primes_set: set[int] = set()
    for _zs, _ze, _mk, candidate in zones:
        if candidate < start or candidate > end:
            continue
        if candidate > 2 and candidate % 2 == 0:
            continue
        if _is_prime(candidate):
            primes_set.add(candidate)
        for offset in (-2, -1, 1, 2):
            test = candidate + offset
            if test < start or test > end or test <= 1:
                continue
            if test > 2 and test % 2 == 0:
                continue
            if _is_prime(test):
                primes_set.add(test)
    out = sorted(primes_set)
    return out[:max_primes]


def _crystalline_boundary_prime(block_height: int) -> int | None:
    """
    Check if block_height sits on a Crystalline structural boundary (multiple
    of 144 or 432, or is itself a Crystalline prime, or is adjacent to a
    twin-prime pair).  Returns the nearest prime >= block_height that aligns
    with the Crystalline structure, or None.
    """
    _crystalline_set = set(CRYSTALLINE_PRIMES)

    if block_height in _crystalline_set and _is_prime(block_height):
        return block_height

    for lo, hi in TWIN_PRIME_PAIRS:
        if block_height == lo:
            return lo
        if block_height == hi:
            return hi

    for divisor in (NORMALIZER_432, QUADRATIC_BOUNDARY):
        remainder = block_height % divisor
        if remainder <= 2 or remainder >= divisor - 2:
            for delta in (0, 1, -1, 2, -2):
                candidate = block_height + delta
                if candidate >= 2 and _is_prime(candidate):
                    return candidate

    return None


def _get_seed_prime_thesis(block_height: int) -> int:
    """
    Seed prime: clock trial-factor screen, then Crystalline boundary check,
    then the bounded SFT candidate scan with explicit primality tests.
    block_height < 2 -> 2.
    """
    global _last_seed_prime_path
    if block_height < 2:
        _last_seed_prime_path = "sft"
        return 2
    candidate = _clock_o1_seed_prime(block_height)
    if candidate is not None:
        _last_seed_prime_path = "clock_o1"
        return candidate
    crystalline = _crystalline_boundary_prime(block_height)
    if crystalline is not None:
        _last_seed_prime_path = "crystalline"
        return crystalline
    _last_seed_prime_path = "sft"
    primes = _sft_deterministic_prime_map(
        block_height, block_height + 10000, max_primes=1
    )
    if primes:
        return primes[0]
    return 2


def _tetration_mod(base: int, depth: int, modulus: int) -> int:
    """Exact tower on the documented height0..3 / unsigned64-bit domain."""
    return tetration_mod(base, depth, modulus)


# Entropy reduction bounds aligned with C nonce_apply_difficulty_bounds (0.18–0.45)
ENTROPY_CUT_MIN = 0.18
ENTROPY_CUT_MAX = 0.45


def get_entropy_bounds() -> tuple[float, float]:
    """Return (min, max) entropy bounds. Reads BTC_ENTROPY_CUT_MIN/MAX from env when set."""
    min_val = ENTROPY_CUT_MIN
    max_val = ENTROPY_CUT_MAX
    env_min = os.environ.get("BTC_ENTROPY_CUT_MIN", "").strip()
    env_max = os.environ.get("BTC_ENTROPY_CUT_MAX", "").strip()
    if env_min:
        try:
            min_val = float(env_min)
            min_val = max(0.0, min(1.0, min_val))
        except ValueError:
            pass
    if env_max:
        try:
            max_val = float(env_max)
            max_val = max(0.0, min(1.0, max_val))
        except ValueError:
            pass
    if min_val > max_val:
        max_val = min_val
    return (min_val, max_val)

# Max reassessments (must match C NonceConfig default)
_NONCE_MAX_REASSESSMENTS = 5

# Fixed seed modulus. Sharing a modulus does not establish C/Python parity.
_TETRATION_MODULUS = (1 << 64) - 1


def _nonce_validate_difficulty_py(nonce: int, difficulty_bits: int) -> bool:
    """Match C nonce_validate_difficulty: True if leading zero bits >= difficulty_bits."""
    if difficulty_bits <= 0 or difficulty_bits > 64:
        return True
    mask = 1 << 63
    leading_zeros = 0
    n = nonce & NONCE_MAX
    while leading_zeros < 64 and (n & mask) == 0:
        leading_zeros += 1
        mask >>= 1
    return leading_zeros >= difficulty_bits


def _nonce_reassess_py(block_height: int, attempt: int, previous_nonce: int) -> int:
    """Match C nonce_reassess: deterministic adjustment by attempt * block_height."""
    adjustment = attempt * block_height
    return (previous_nonce ^ adjustment) & NONCE_MAX


def nonce_generate_unified_py(block_height: int, difficulty_bits: int) -> int:
    """
    Deterministic base nonce from block height and difficulty.
    Uses the exact-tower-v2 Python mapping. Historical C nonce generation has
    no current exact-tower parity receipt and cannot override this result,
    including when BTC_USE_C_NONCE is set. Optional candidate helpers are separate.
    Returns base nonce in [0, 0xFFFFFFFF].
    """
    global _base_nonce_source
    _base_nonce_source = "python"
    return _nonce_generate_unified_py_impl(block_height, difficulty_bits)


def _nonce_generate_unified_py_impl(
    block_height: int, difficulty_bits: int, entropy_bounds: Optional[tuple[float, float]] = None
) -> int:
    """Exact-tower-v2 seed with the existing bounded mask/reassessment heuristic.
    These nonce-value transformations do not certify Bitcoin header difficulty.
    """
    seed_prime = _get_seed_prime_thesis(block_height)
    tetration_val = _tetration_mod(seed_prime, 3, _TETRATION_MODULUS)
    if difficulty_bits <= 0 or difficulty_bits > 64:
        return (tetration_val & NONCE_MAX)
    emin, emax = entropy_bounds if entropy_bounds is not None else get_entropy_bounds()
    entropy_factor = emin + (emax - emin) * (difficulty_bits / 64.0)
    # Match C: mask = (1ULL << difficulty_bits) - 1
    mask = (1 << difficulty_bits) - 1
    if mask > (1 << 64) - 1:
        mask = (1 << 64) - 1
    reduced = tetration_val & mask
    reduced = int(float(reduced) * (1.0 - entropy_factor))
    candidate = reduced & NONCE_MAX
    for attempt in range(_NONCE_MAX_REASSESSMENTS):
        if _nonce_validate_difficulty_py(candidate, difficulty_bits):
            return candidate
        candidate = _nonce_reassess_py(block_height, attempt + 1, candidate)
    return candidate


def nonce_generate_for_backtest(
    block_height: int, difficulty_bits: int, overrides: Optional[dict] = None
) -> int:
    """
    Base nonce for backtest with optional parameter overrides.
    Always uses Python impl; overrides.entropy_min/entropy_max when provided.
    """
    bounds: Optional[tuple[float, float]] = None
    if overrides:
        emin = overrides.get("entropy_min")
        emax = overrides.get("entropy_max")
        if emin is not None and emax is not None:
            try:
                emin_f = max(0.0, min(1.0, float(emin)))
                emax_f = max(0.0, min(1.0, float(emax)))
                if emin_f > emax_f:
                    emax_f = emin_f
                bounds = (emin_f, emax_f)
            except (TypeError, ValueError):
                pass
    return _nonce_generate_unified_py_impl(block_height, difficulty_bits, entropy_bounds=bounds)


def get_minimal_nonce_list(
    block_height: int,
    difficulty_bits: int,
    bits_bytes: bytes,
) -> list[int]:
    """
    Minimal nonce set for single-nonce-first mining: base nonce plus recovery
    if available (1–2 elements, deduplicated). Use before expanding to candidates.

    This is only a candidate-ordering heuristic; it does not establish that
    one or two hashes find a valid block. Set single_nonce_only=True (or
    BTC_SINGLE_NONCE_ONLY=1) to try only this set and skip candidate/fallback
    (thesis validation mode).
    """
    base = nonce_generate_unified_py(block_height, difficulty_bits)
    out: list[int] = [base]
    rec = recovery_suggested_nonce(bits_bytes)
    if rec is not None and rec != base:
        out.append(rec)
    return out


def is_prime_position(pos: int) -> bool:
    """True for clock positions in SPHERE_PRIME_POSITIONS (1, 5, 7, 11) mod 12; sphere step count."""
    return (pos % 12) in SPHERE_PRIME_POSITIONS


def fold_to_q1(pos: int) -> int:
    """Quadrant fold: map position to Q1 equivalent (0, 1, 2)."""
    p = pos % 12
    quad = p // 3
    return p % 3


def recovery_suggested_nonce(bits_bytes: bytes) -> Optional[int]:
    """
    Run OBJECTIVE 28 recovery with target bits; return suggested nonce or None.
    Requires c. math/python recovery and librecovery_core built.
    When using multiprocessing, call only from the main process; pass the result
    to workers so they do not load recovery or C libs.
    Set BTC_DISABLE_RECOVERY=1 or CI=1 to skip loading (e.g. in tests) and avoid native lib segfaults.
    """
    global _recovery_loaded
    if len(bits_bytes) < 4:
        return None
    if os.environ.get("BTC_DISABLE_RECOVERY", "").strip() in ("1", "true", "yes") or os.environ.get("CI", "").strip() in ("1", "true", "yes"):
        _recovery_loaded = False
        return None
    _here = os.path.dirname(os.path.abspath(__file__))
    project_root = _find_c_math_root()
    if not project_root:
        _recovery_loaded = False
        return None
    c_math = os.path.join(project_root, "c. math")
    recovery_core_dir = os.path.join(c_math, "lib", "recovery_core")
    if not os.path.isdir(recovery_core_dir):
        _recovery_loaded = False
        return None
    lib_path = os.path.join(recovery_core_dir, "librecovery_core.so")
    if not os.path.isfile(lib_path):
        lib_path = os.path.join(recovery_core_dir, "librecovery_core.dylib")
    if not os.path.isfile(lib_path):
        _recovery_loaded = False
        return None
    try:
        os.environ["RECOVERY_LIB_PATH"] = recovery_core_dir
        if c_math not in sys.path:
            sys.path.insert(0, os.path.join(c_math, "python"))
        from recovery.core import RecoveryContext, RECOVERY_METHOD_CRYPTO  # type: ignore

        _recovery_loaded = True
        ctx = RecoveryContext(
            max_iterations=500,
            method=RECOVERY_METHOD_CRYPTO,
        )
        ctx.set_q(bits_bytes)
        result = ctx.run()
        if result.converged and len(result.data) >= 4:
            return int.from_bytes(result.data[:4], "little") & NONCE_MAX
    except Exception:
        _recovery_loaded = False
    return None


# ---------------------------------------------------------------------------
# Polar prime lattice (E-S-F fabric model).
# ---------------------------------------------------------------------------

_POLAR_LATTICE_CACHE: list[dict] | None = None


def _compute_polar_lattice() -> list[dict]:
    """
    Build the polar prime lattice from POLAR_LATTICE_PRIMES.

    Each prime p_n occupies:
      r_n = cumulative product of previous primes (mod NONCE_MAX+1)
      θ_n = 2π × (cumulative / p_n) mod 2π
    Plus POLAR_LATTICE_HARMONICS conjugate angles per prime:
      θ_{n,k,m} = k × 2π × (p_m / p_n) mod 2π
    """
    global _POLAR_LATTICE_CACHE
    if _POLAR_LATTICE_CACHE is not None:
        return _POLAR_LATTICE_CACHE

    lattice: list[dict] = []
    cumulative = 1
    primes_so_far: list[int] = []

    for p in POLAR_LATTICE_PRIMES:
        r = cumulative % (NONCE_MAX + 1)
        theta = (TWO_PI * (cumulative / p)) % TWO_PI

        conjugates: list[float] = []
        for k in range(1, POLAR_LATTICE_HARMONICS + 1):
            for pm in primes_so_far:
                conj = (k * TWO_PI * (pm / p)) % TWO_PI
                conjugates.append(conj)

        lattice.append({
            "prime": p,
            "radius": r,
            "theta": theta,
            "conjugates": conjugates,
        })
        primes_so_far.append(p)
        cumulative *= p

    _POLAR_LATTICE_CACHE = lattice
    return lattice


def _polar_lattice_candidates(base_nonce: int, block_height: int) -> list[int]:
    """
    Generate nonce candidates from the polar prime lattice.

    For each lattice point (r, θ):
      candidate = int(r × |sin(θ)| % (NONCE_MAX+1))
    shifted by base_nonce and block_height for per-block variation.

    Conjugate angles produce additional candidates.
    The back-reaction prime (167) and Q-product (231) create cascade
    offsets that amplify coverage at resonant positions.
    """
    lattice = _compute_polar_lattice()
    out: list[int] = []
    nonce_space = NONCE_MAX + 1

    height_phase = (block_height * math.pi * PHI) % TWO_PI

    for point in lattice:
        r = point["radius"]
        theta = point["theta"]

        raw = int(r * abs(math.sin(theta + height_phase))) % nonce_space
        out.append((base_nonce + raw) & NONCE_MAX)
        out.append((base_nonce - raw) & NONCE_MAX)

        q_offset = int(r * abs(math.sin(theta * PRIME_HARMONIC_Q / point["prime"]))) % nonce_space
        out.append((base_nonce + q_offset) & NONCE_MAX)

        br_offset = int(abs(math.sin(theta + height_phase)) * BACK_REACTION_PRIME * point["prime"]) % nonce_space
        out.append((base_nonce + br_offset) & NONCE_MAX)
        out.append((base_nonce - br_offset) & NONCE_MAX)

        for conj_theta in point["conjugates"]:
            conj_raw = int(r * abs(math.sin(conj_theta + height_phase))) % nonce_space
            out.append((base_nonce + conj_raw) & NONCE_MAX)

    return out


def build_candidate_list(
    base_nonce: int,
    recovery_nonce: int,
    start_nonce: int,
    end_nonce: int,
    quadrant_id: Optional[int] = None,
    block_height: Optional[int] = None,
) -> list[int]:
    """
    Build candidate nonces using sphere hopping, duality ordering, golden-ratio spiral.

    Implements the thesis sphere-hopping candidate ordering aligned with the C miner
    and the memory-hopping architecture (compact vector / sphere hierarchy in
    c. math/math/src/compact/sphere_hopping.c). The C miner uses create_sphere_hierarchy(2)
    to drive the same 12-sphere, duality, golden-ratio formula.

    When quadrant_id is not None (0-3), only nonces in that 500D lattice quadrant are
    included; used by 4-worker thesis partition to avoid building the full list per worker.
    When quadrant_id is set, C path is skipped (Python-only) so each worker builds only
    its quadrant's candidates.
    When BTC_USE_C_CANDIDATES=1 and libalgorithms is loaded, uses C build_candidate_list_sphere.
    block_height: chain height for polar lattice phase (Layer E); omit or None uses 0.
    """
    if quadrant_id is None and use_c_candidates() and _load_libnonce() and _libnonce is not False:
        fn = getattr(_libnonce, "build_candidate_list_sphere", None)
        if fn is not None:
            buf = (c_uint32 * 1024)()
            count = c_size_t(0)
            if fn(
                c_uint32(base_nonce & NONCE_MAX),
                c_uint32(recovery_nonce & NONCE_MAX),
                c_uint32(start_nonce & NONCE_MAX),
                c_uint32(end_nonce & NONCE_MAX),
                buf,
                c_size_t(1024),
                byref(count),
            ) == 0:
                return [int(buf[i]) for i in range(count.value)]
    nonce_range = end_nonce - start_nonce
    if nonce_range <= 0:
        return []
    sphere_size = max(1, nonce_range // 12)
    seen: set[int] = set()
    candidates: list[int] = []

    def add(n: int) -> None:
        if quadrant_id is not None and quadrant_from_nonce(n) != quadrant_id:
            return
        if start_nonce <= n < end_nonce and n not in seen:
            seen.add(n)
            candidates.append(n)

    add(base_nonce)
    add(recovery_nonce)

    for s in range(12):
        sphere_base = start_nonce + (s * sphere_size) % nonce_range
        if sphere_base >= end_nonce:
            sphere_base = start_nonce
        prime_pos = is_prime_position(s)
        steps = 40 if prime_pos else 35
        for i in range(steps):
            offset = int(i * PHI) % PLATONIC_RADIUS
            if sphere_base + offset < end_nonce:
                add(sphere_base + offset)
            if offset > 0 and sphere_base >= offset:
                add(sphere_base - offset)

    for off in range(-200, 201):
        add(base_nonce + off)
        add(recovery_nonce + off)

    # --- Crystalline layers (Grok "Lunar Cycle Stability" thesis) ---

    # Layer A: 432-family normalization.
    # 144 (12²) and 432 (144×3) are fundamental set boundaries; twin primes
    # 431/433 flank the normalizer.  Sweep multiples up to ±10.
    for k in range(1, 11):
        for stride in (QUADRATIC_BOUNDARY, NORMALIZER_432):
            add(base_nonce + k * stride)
            add(base_nonce - k * stride)
        add(base_nonce + k * 431)
        add(base_nonce - k * 431)
        add(base_nonce + k * 433)
        add(base_nonce - k * 433)

    # Layer B: twin-prime boundary sweep.
    # Each twin-prime pair marks a modular boundary; offset base and recovery
    # by the pair values and by pair × sphere index for cross-layer coverage.
    for lo, hi in TWIN_PRIME_PAIRS:
        add(base_nonce + lo)
        add(base_nonce - lo)
        add(base_nonce + hi)
        add(base_nonce - hi)
        add(recovery_nonce + lo)
        add(recovery_nonce - lo)
        add(recovery_nonce + hi)
        add(recovery_nonce - hi)
        for s in range(12):
            add(base_nonce + lo * (s + 1))
            add(base_nonce + hi * (s + 1))

    # Layer C: fractal ring expansion.
    # Platonic layers at distances 7, 12, 20, 24, 30, 42 from each sphere
    # center — self-similar copies of the prime-boundary structure.
    for s in range(12):
        sphere_base = start_nonce + (s * sphere_size) % nonce_range
        if sphere_base >= end_nonce:
            sphere_base = start_nonce
        for ring in FRACTAL_RINGS:
            add(sphere_base + ring)
            add(sphere_base - ring)

    # Layer D: 29-prime lunar / 762 combined-cycle modular.
    # 29 is the lunar prime (level 3 recursive zero-paired); 762 = 61×12 + 29.
    for k in range(1, 21):
        add(base_nonce + k * LUNAR_PRIME)
        add(base_nonce - k * LUNAR_PRIME)
    for k in range(1, 11):
        add(base_nonce + k * COMBINED_CYCLE)
        add(base_nonce - k * COMBINED_CYCLE)

    # Layer E: polar prime lattice (E-S-F fabric model).
    # Nonce candidates from the lattice positions (r, θ) of the first 10
    # primes, including conjugate harmonics and cascade amplification at
    # the back-reaction prime (167) and Q-product (231 = 3×7×11).
    # block_height modulates the phase (per-block); base_nonce is the seed.
    _bh = 0 if block_height is None else int(block_height) & 0xFFFFFFFF
    polar_cands = _polar_lattice_candidates(base_nonce, _bh)
    for pc in polar_cands:
        add(pc)

    return candidates


def get_base_nonce_source() -> str:
    """Return the actual implementation source (currently 'python')."""
    return _base_nonce_source


def get_base_nonce_version() -> str:
    """Identify the corrected deterministic seed mapping for replay records."""
    return TOWER_VERSION


def get_last_seed_prime_path() -> Optional[str]:
    """Return the historical path label: clock_o1, crystalline, sft, or None."""
    return _last_seed_prime_path


def is_recovery_loaded() -> Optional[bool]:
    """Return True if recovery lib is available, False if not, None if not yet tried."""
    return _recovery_loaded
