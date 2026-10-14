# Ellipse and dynamic rods implementation — 1.2.3

The supplied mathematics is implemented in `btcminer/pqmath.py`. Dynamic rods now
decide primality in `thesis2.qualifying_primes()`, which supplies and validates
the prime used by the real THESIS2 traversal. This is exercised by both integration
tests and a Bitcoin Core regtest block acceptance run.

The ellipse routines are available for integer factor searches and `/math`
inspection. The supplied proofs do not connect an ellipse's factors to a successful
Bitcoin nonce, so they provide no basis for removing nonces from the search.
The existing complete-tile ordering and native SHA256d acceptance checks are preserved.

## Source and executable counterparts

Unmodified source copies are in `reference/aristotle-ellipse-rods/`; their hashes and
the Desktop export location are recorded in `validation/ellipse-rods/source-provenance.json`.
The Python routines are ports tested against the mathematical statements. They are
not Lean-extracted code or formally verified Python. A subsequent independent
check compiled the completed task's EllipseSearch, DynamicRods and CorePrimes
sources plus all 10 local dependencies. The 83 theorem roots in those three
modules use only Lean's standard axioms. Exact source hashes, scope and logs are
recorded in `validation/aristotle-current/latest-validation.json`; see
`ARISTOTLE-MONITOR.md` for the added core-prime diagnostics and monitoring.

| Source result | Executable counterpart and scope |
| --- | --- |
| `focalRadius_bounds`, recovery from bounds | `PQEllipse.r_min`, `r_max`, `focal_radius(cosine)`, `from_bounds`; exact rational radii and reconstruction. |
| `area_determines` | `area_over_pi_squared`, `from_area_squared`; stores `(A/pi)^2` exactly, with `q^4 = n^2 + 16(A/pi)^2`. |
| `ecc_band` | `eccentricity_bounds`; inclusive integer interval `[ceil(sqrt(n*lo)), floor(sqrt(n*hi))]`. The band must be supplied. |
| `fermat_gap` | `fermat_steps`, `fermat_step_bound`, `fermat_factor`; exact integer roots, explicit increment budget, at most budget+1 square tests. |
| `fermat_pairs_pq` and coprime bounds | `difference_of_squares_pair` and `integer_bounds`; tests enumerate all divisor pairs for distinct odd prime pairs below 100, finding exactly the trivial and nontrivial pair. The two-pair claim requires those prime assumptions. |
| `least_coprime_prime`, `next_rod` | `least_coprime_prime(M)` and `DynamicRods.extend`; next rod obtained by coprimality. Positive modulus required, since zero has no coprime integer greater than one. |
| `window`, sharp boundary, `add_rod` | `DynamicRods.is_prime_in_window`, `ensure_volume`, `extend`; all prime rods below prime frontier r, classification only for `1 < x < r^2`. Loaded prime rods are handled separately from the all-nonzero test. |
| CRT extension | `RodAbacus.reading`, `reconstruct`, `extend`, `extend_residue`; pairwise-coprime validation and exact reconstruction preserve old readings. |
| `passCount_snd`, `rods_needed` | `pass_count` performs one remainder check per rod, including after a failure. Rod-count and volume are exposed; growing volumes add rods. The lower-bound theorem is a complexity constraint, not a shortcut algorithm. |
| `factor_on_rods` | `DynamicRods.factor_on_rods(n, band)` searches loaded prime rods within an optional exact eccentricity interval; requires `n < r^2`. |

All geometry uses integers and `fractions.Fraction`; floating-point inputs are rejected.
Algebraic identities work for positive integer `p < q` without assuming primality.
Integer Fermat bounds require matching parity; distinct odd prime assumptions are
needed for uniqueness and coprimality. General factoring is still search.

The shared runtime abacus grows under a lock before out-of-window primality queries.
The qualifying-prime list is cached; these checks do not run for every nonce. An
abacus's CRT capacity (the product of its rods) differs from its primality window
(the square of its least missing prime).

## Using the math

The existing dashboard `/math` command now includes `ellipse_and_rods` examples and
the runtime rod state. The command-line equivalent is:

```sh
./bin/btc-miner math inspect --strategy thesis2
```

For a supplied eccentricity band and a loaded abacus:

```python
from btcminer.pqmath import DynamicRods, PQEllipse, eccentricity_bounds, fermat_factor

ellipse = PQEllipse(19, 181)
assert (ellipse.r_min, ellipse.r_max) == (81, 100)
assert eccentricity_bounds(3439, "1/10", "1/8") == (19, 20)
assert DynamicRods(61).factor_on_rods(3439, ("1/10", "1/8")) == (19, 181)
assert fermat_factor(3439, max_steps=41).factors == (19, 181)

rods = DynamicRods(19)
assert len(rods.primes_in_window()) == 65  # [19,361)
assert rods.pass_count(361) == (True, 7)   # Outside its valid window!
rods.extend()                            # Add 19; next frontier 23, volume 529
assert not rods.is_prime_in_window(361)
```

## Correction to the informal explanation

With this definition `e = p/q`, close factors have eccentricity near **1**.
They give small `rMin = (q-p)/2` and a short Fermat search. Small eccentricity
describes a rounder ellipse with more unequal factors; roundness alone does not
make Fermat search short. The source's informal “nearly round” explanation reverses
this relationship. Its displayed gap formula is correct. Original source copies
are retained unchanged, and a test covers this distinction.

## Validation and limits

All **74 regression tests** pass, including 18 new tests for the statements above.
They cover the seven-rod/65-prime example, the `r^2` boundary, dynamic growth against
an independent sieve, CRT extension, exact inverse geometry and an algebraic
example above 8192 product bits. The latter's factors are not asserted prime.

Bitcoin Core 31.1.0 accepted a THESIS2-generated witness-containing block on an
isolated regtest chain using this version's sources. The report records their
SHA-256 digests. This validates the tested miner workflow on regtest; it does not
establish a public-network result or a hashing advantage from these identities.

Fixed rods give a fixed count of remainder checks. The cost is not uniformly
constant as the window grows, and arbitrary-precision remainders also have bit cost.
Area, eccentricity or focal bounds are additional factor information, not values
this code can infer cheaply from `n` alone.

## October 10 source integration and recheck

The current source incorporates the reviewed unit basis `(11,19,73,109)` into
THESIS2 step validation and describes its unique coordinates with periods
`(6,2,4,2)`. All 96 steps retain the existing full board traversal. These periods
are group coordinates, not pairwise coprime CRT moduli. Diagnostics distinguish
integer-unit clocks, square norm-one circles, hex norm-one circles and petal spokes.

Resident residue columns now require consistent expression lineage before merge,
derive recurrence bounds independently, invalidate certificates on partial native
failure, and preserve lineage during capacity growth. Unit powers no longer trigger
unnecessary frame growth. The native Eisenstein distance has an arbitrary-precision
adapter and defined behavior across the full signed 64-bit input range.

The legacy seed now uses exact modular towers through height three, with prime-power
valuation handling for noncoprime bases. The previous exponent reduction was wrong:
`3^(3^3) mod 7` is 6. The corrected legacy mapping is `exact-tower-v2`, exposed in
engine state and nonce logs. It changes legacy seed order; the THESIS2 mapping remains
unchanged. The optional historical native seed cannot override this calculation.

`python3 -B -m btcminer abacus formulas` exposes the hash-bound 1,302-record formula
snapshot and typed consumer map. Add `--query TEXT` to search literal records. Provider
status labels and name matches do not grant proof acceptance. Detailed source cards,
fresh Lean contracts and integration evidence are in
`validation/aristotle-card-distillation-20261010T184744Z/`.

These are source and offline validation changes. Historical test and regtest counts
above describe earlier snapshots; current receipts bind their own source hashes.
The changes do not qualify a live pool connection or reload an active miner.

## Product-tree CRT and capacity-derived intervals

`btcminer.product_tree_crt.ProductTreeCRT` builds a reusable balanced tree of
coprime products and modular inverses. `RodAbacus.reconstruct` uses it for exact
arbitrary-precision reconstruction. `shared_abacus.Column.value` uses the tree
for frames with at least 64 rods, while retaining the native decoder for small
frames. Signed reads preserve the column's sealed interval and lineage checks.
Reconstruction into an inclusive interval requires `high - low < capacity`;
residues that contradict the interval are rejected.

`btcminer.capacity_reals` provides a fixed-frame algebraic interval library for
rational constants, negation, addition, subtraction, multiplication, rational
scaling and nonnegative square roots. It holds endpoints as residue columns and
uses exact integer arithmetic for bounds, readback and outward rounding. For a
working scale `P = base**G`, the planner reserves the largest intermediate bound
`B = max(linear*P, quadratic*P*P)` and requires `2*B < capacity`. Multiplication
reserves the product before rescaling, and square roots reserve the scaled
radicand. There is no fixed 192-place mathematical limit.

```python
from btcminer.capacity_reals import CapacityReals, Expr

service = CapacityReals((1000000007, 1000000009))
expression = Expr.rational(2).sqrt()
plan = service.plan(expression)
reading = service.read(expression, places=3)
assert reading.certified
assert reading.lower == 305470  # floor(sqrt(2) * 60**3)
```

Certification uses `lo % F + (hi-lo) < F`, equivalent to agreement of the two
floor readings for positive `F`. Exhausting capacity returns
`uncertified_at_capacity`; it does not prove that the value lies exactly on an
integer boundary. Optional stage budgets are computational limits, separately
reported. Transcendental functions and general interval division are outside
this module. This does not replace the unavailable provider C real evaluator.

Run `python3 -B scripts/capacity_real_report.py --sqrt 19 --places 0` for an
offline report using rods `(11,19,73,109)`. The command reports the expression's
maximum working scale, certificate and explicit capacity/budget outcomes.

Literal Lean contracts, counterexamples, source-bound implementation cards and
tests for this increment are under
`validation/api-library-completion-20261010T205820Z/`. The contracts prove the
stated mathematical algorithms and conditions. They are not a formal refinement
of the Python interpreter, C ABI, memory management or the whole miner, and do
not enlarge the separate 299-root portable proof capsule. Source changes do not
reload the running process.
