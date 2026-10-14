"""Exact executable counterparts of EllipseSearch and DynamicRods.

The Python implementations are tested against the statements, not Lean-extracted
or themselves formally verified. Integer/rational geometry avoids floating point.
Prime rods certify a finite window; growing that window requires more rods.
None of these statements predicts SHA256 hashes or authorizes excluding nonces.
"""
from dataclasses import dataclass
from fractions import Fraction
from math import gcd, isqrt, prod
from threading import RLock
from .product_tree_crt import ProductTreeCRT


def _integer(value, name, minimum=None):
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(name + " must be an integer")
    if minimum is not None and value < minimum:
        raise ValueError(name + " must be at least " + str(minimum))
    return value


def _rational(value, name):
    if isinstance(value, bool) or not isinstance(value, (int, Fraction, str)):
        raise TypeError(name + " must be an integer, Fraction, or exact numeric string")
    return Fraction(value)


def floor_sqrt(value):
    value = _rational(value, "radicand")
    if value < 0:
        raise ValueError("Square-root bounds require a nonnegative radicand")
    return isqrt(value.numerator // value.denominator)


def ceil_sqrt(value):
    value = _rational(value, "radicand")
    root = floor_sqrt(value)
    return root if root * root == value else root + 1


def pass_count(rods, value):
    """Evaluate every rod once, including after a failed divisibility check."""
    _integer(value, "value")
    passed, checks = True, 0
    for rod in rods:
        _integer(rod, "rod", 2)
        nonzero = value % rod != 0
        passed = passed and nonzero
        checks += 1
    return passed, checks


def least_coprime_prime(modulus):
    """Least m > 1 coprime to positive M; primality follows from minimality.

    M=0 is rejected: no m>1 is coprime to zero. This is a search, not a
    constant-cost prime generator as M varies.
    """
    _integer(modulus, "modulus", 1)
    candidate = 2
    while gcd(candidate, modulus) != 1:
        candidate += 1
    return candidate


@dataclass(frozen=True)
class RodAbacus:
    """Pairwise coprime rods and their exact Chinese-remainder arithmetic."""
    rods: tuple = ()

    def __post_init__(self):
        rods = tuple(self.rods)
        plan = ProductTreeCRT(rods)
        object.__setattr__(self, "rods", rods)
        object.__setattr__(self, "_capacity", plan.capacity)
        object.__setattr__(self, "_crt_plan", plan)

    @property
    def capacity(self):
        return self._capacity

    def reading(self, value):
        _integer(value, "value")
        return tuple(value % rod for rod in self.rods)

    def reconstruct(self, residues):
        return self._crt_plan.decode(residues)

    def extend(self, rod):
        return RodAbacus(self.rods + (_integer(rod, "rod", 2),))

    def extend_residue(self, old_residue, rod, new_residue):
        """Inverse CRT for Z/(M*rod) -> Z/M x Z/rod."""
        _integer(old_residue, "old residue")
        _integer(new_residue, "new residue")
        self.extend(rod)  # Validate coprimality before taking an inverse.
        capacity = self.capacity
        old = old_residue % capacity
        return old + capacity * ((new_residue - old) * pow(capacity, -1, rod) % rod)


class DynamicRods:
    """All primes below the frontier r, with certified window 1 < x < r*r.

    The frontier is the least missing prime. Each extension appends precisely
    that prime and finds the next by coprimality. Read-only queries never grow
    the window; ensure_volume explicitly does. Instances are mutable; the
    shared runtime instance below is protected by a lock.
    """
    def __init__(self, frontier=19):
        _integer(frontier, "prime frontier", 2)
        self._rods = ()
        self._capacity = 1
        self._frontier = 2
        while self._frontier < frontier:
            self.extend()
        if self._frontier != frontier:
            raise ValueError("The frontier must be prime")

    @property
    def rods(self):
        return self._rods

    @property
    def frontier(self):
        return self._frontier

    @property
    def capacity(self):
        return self._capacity

    @property
    def volume(self):
        """Exclusive primality bound; distinct from the CRT capacity."""
        return self.frontier * self.frontier

    def pass_count(self, value):
        return pass_count(self.rods, value)

    def is_prime_in_window(self, value):
        _integer(value, "value", 2)
        if value >= self.volume:
            raise ValueError("Value is outside the certified window; add rods first")
        # A prime already loaded as a rod has a zero reading on itself.
        return value in self.rods or self.pass_count(value)[0]

    def primes_in_window(self, start=None, stop=None):
        start = self.frontier if start is None else _integer(start, "start", 2)
        stop = self.volume if stop is None else _integer(stop, "exclusive stop", 2)
        if not 2 <= start <= stop <= self.volume:
            raise ValueError("Requested interval is outside the loaded volume")
        return tuple(x for x in range(start, stop) if self.is_prime_in_window(x))

    def extend(self):
        rod = self.frontier
        self._rods += (rod,)
        self._capacity *= rod
        candidate = rod + 1
        # All numbers 2..rod already fail after rod is appended, so scanning
        # upwards still finds the least integer >1 coprime to the new capacity.
        while gcd(candidate, self.capacity) != 1:
            candidate += 1
        self._frontier = candidate
        return rod

    def ensure_volume(self, value):
        _integer(value, "value", 0)
        while value >= self.volume:
            self.extend()
        return self

    def factor_on_rods(self, n, eccentricity_band=None):
        """Find a proper factor within the loaded window and supplied band.

        For pq < r*r with p<=q, the smaller prime is necessarily a loaded rod.
        An optional eccentricity band is external information, not inferred
        from n. This method does not silently construct an unbounded abacus.
        """
        _integer(n, "n", 2)
        if n >= self.volume:
            raise ValueError("n is outside the loaded window; add rods first")
        lo, hi = (2, isqrt(n)) if eccentricity_band is None else eccentricity_bounds(n, *eccentricity_band)
        for rod in self.rods:
            if lo <= rod <= hi and n % rod == 0 and rod < n:
                return rod, n // rod
        return None


_PRIMES = DynamicRods()
_PRIME_LOCK = RLock()


def is_prime(value):
    """Runtime prime decision using explicitly grown, certified rod windows."""
    _integer(value, "value")
    if value < 2:
        return False
    with _PRIME_LOCK:
        _PRIMES.ensure_volume(value)
        return _PRIMES.is_prime_in_window(value)


def runtime_rod_state():
    with _PRIME_LOCK:
        return {"rods": list(_PRIMES.rods), "frontier": _PRIMES.frontier,
                "exclusive_volume": _PRIMES.volume, "rod_checks_per_full_query": len(_PRIMES.rods)}


def eccentricity_bounds(n, lower, upper):
    """Exact inclusive integer interval ceil(sqrt(n*lo)) .. floor(sqrt(n*hi))."""
    _integer(n, "n", 1)
    lower, upper = _rational(lower, "lower eccentricity"), _rational(upper, "upper eccentricity")
    if not 0 <= lower <= upper <= 1:
        raise ValueError("Require 0 <= lower <= upper <= 1 for the smaller-factor chart")
    return ceil_sqrt(n * lower), floor_sqrt(n * upper)


@dataclass(frozen=True)
class PQEllipse:
    """The p/q chart for positive integer p<q; identities do not assume primes."""
    p: int
    q: int

    def __post_init__(self):
        _integer(self.p, "p", 1)
        _integer(self.q, "q", 1)
        if self.p >= self.q:
            raise ValueError("A nondegenerate pq ellipse requires p < q")

    @property
    def n(self):
        return self.p * self.q

    @property
    def r_min(self):
        return Fraction(self.q - self.p, 2)

    @property
    def r_max(self):
        return Fraction(self.q + self.p, 2)

    @property
    def eccentricity(self):
        return Fraction(self.p, self.q)

    @property
    def semi_minor_squared(self):
        return Fraction(self.q * self.q - self.p * self.p, 4)

    @property
    def area_over_pi_squared(self):
        """(A/pi)^2: exact rational area information, without rounding pi."""
        return Fraction(self.q * self.q, 4) * self.semi_minor_squared

    def focal_radius(self, cosine):
        """Exact polar radius for a supplied exact cos(theta) in [-1,1]."""
        cosine = _rational(cosine, "cosine")
        if not -1 <= cosine <= 1:
            raise ValueError("cos(theta) must lie in [-1, 1]")
        return (self.semi_minor_squared / Fraction(self.q, 2)) / (1 + self.eccentricity * cosine)

    @classmethod
    def from_bounds(cls, r_min, r_max):
        r_min, r_max = _rational(r_min, "rMin"), _rational(r_max, "rMax")
        p, q = r_max - r_min, r_max + r_min
        if p.denominator != 1 or q.denominator != 1:
            raise ValueError("These bounds do not describe integer factors")
        return cls(int(p), int(q))

    @classmethod
    def from_area_squared(cls, n, area_over_pi_squared):
        _integer(n, "n", 1)
        area_sq = _rational(area_over_pi_squared, "(area/pi)^2")
        if area_sq <= 0:
            raise ValueError("A nondegenerate ellipse requires positive area")
        q4 = n * n + 16 * area_sq
        q = isqrt(floor_sqrt(q4))
        if q ** 4 != q4 or n % q:
            raise ValueError("Area information does not describe integer factors of n")
        return cls(n // q, q)

    @classmethod
    def from_eccentricity(cls, n, eccentricity):
        _integer(n, "n", 1)
        e = _rational(eccentricity, "eccentricity")
        if not 0 < e < 1:
            raise ValueError("Require 0 < eccentricity < 1")
        p, q = floor_sqrt(n * e), floor_sqrt(n / e)
        if p * p != n * e or q * q != n / e:
            raise ValueError("Eccentricity does not describe integer factors of n")
        return cls(p, q)

    def integer_bounds(self):
        if self.r_min.denominator != 1 or self.r_max.denominator != 1:
            raise ValueError("Integer difference-of-squares bounds require matching factor parity")
        return int(self.r_min), int(self.r_max)

    def fermat_steps(self):
        _, x = self.integer_bounds()
        return x - ceil_sqrt(self.n)

    def fermat_step_bound(self):
        """Floor(rMin^2/(2*sqrt(n))), computed entirely with integer roots."""
        self.integer_bounds()
        square = self.r_min * self.r_min
        return isqrt(square.numerator ** 2 // (4 * self.n * square.denominator ** 2))


def difference_of_squares_pair(n, divisor):
    """Map a divisor d<=sqrt(n) of odd n to X,Y with X^2-Y^2=n."""
    _integer(n, "n", 1)
    _integer(divisor, "divisor", 1)
    if n % 2 == 0 or n % divisor or divisor > isqrt(n):
        raise ValueError("Require odd n and a divisor no larger than sqrt(n)")
    other = n // divisor
    return (other + divisor) // 2, (other - divisor) // 2


@dataclass(frozen=True)
class FermatResult:
    factors: tuple
    increments: int
    square_tests: int


def fermat_factor(n, max_steps=10000):
    """Budgeted exact search from ceil(sqrt(n)); None means no proper factor found.

    max_steps bounds increments, so at most max_steps+1 squares are tested.
    No claim of fast general factoring follows from the gap theorem.
    """
    _integer(n, "n", 2)
    _integer(max_steps, "max_steps", 0)
    if n % 2 == 0:
        return FermatResult((2, n // 2), 0, 0) if n > 2 else None
    x = ceil_sqrt(n)
    for step in range(max_steps + 1):
        y2 = x * x - n
        y = isqrt(y2)
        if y * y == y2:
            p, q = x - y, x + y
            return FermatResult((p, q), step, step + 1) if p > 1 else None
        x += 1
    return None


def report():
    """JSON-friendly exact examples for the miner's existing /math interface."""
    ellipse = PQEllipse(19, 181)
    rods = DynamicRods(19)
    before = {"rods": list(rods.rods), "exclusive_volume": rods.volume,
              "primes_in_19_to_361": len(rods.primes_in_window()),
              "checks_per_query": len(rods.rods), "boundary_361_passes": rods.pass_count(361)[0]}
    rods.extend()
    factored = DynamicRods(61).factor_on_rods(3439, (Fraction(1, 10), Fraction(1, 8)))
    return {"source": "EllipseSearch.lean + DynamicRods.lean (2026-09-29)",
            "arithmetic": "exact integers and rational numbers",
            "runtime_use": "dynamic rods decide the primes used by qualifying_primes and Traversal",
            "ellipse": {"p": 19, "q": 181, "n": ellipse.n,
                        "r_min": str(ellipse.r_min), "r_max": str(ellipse.r_max),
                        "eccentricity": str(ellipse.eccentricity),
                        "area_over_pi_squared": str(ellipse.area_over_pi_squared),
                        "band_1_10_to_1_8_factor_interval": eccentricity_bounds(3439, "1/10", "1/8"),
                        "factor_from_loaded_rods_and_band": factored,
                        "fermat_increments": ellipse.fermat_steps(),
                        "fermat_increment_upper_bound": ellipse.fermat_step_bound()},
            "rods_before_extension": before,
            "rods_after_extension": {"rods": list(rods.rods), "exclusive_volume": rods.volume,
                                      "361_is_prime": rods.is_prime_in_window(361)},
            "scope": "Ellipse bounds constrain integer-factor searches when bounds are supplied. No nonce exclusion or SHA256 prediction is implied.",
            "shape_note": "With e=p/q, close factors have eccentricity near 1; small eccentricity is rounder but does not give a short Fermat search."}
