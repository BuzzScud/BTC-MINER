# The five core primes 11, 19, 71, 97, 109: rods, squares and graph scaling

This note answers three questions:

1. What do the five primes you keep coming back to actually do when you model and graph?
2. Would multiplying a graph by the squares of a coprime set (or by a tetration tower), instead of
   by 19² alone, give a geometrically richer graph?
3. How do these primes relate to the rods, to the fractal (self-similar) structure, and to the
   n = pq and "Q to k" work?

It also takes stock of everything the project has already proved about these five primes (§1), so
nothing earlier is lost. All of this is public research mathematics and is written to be shared.

**New Lean file:** `RequestProject/CorePrimes.lean` (namespace `CorePrimes`). It builds with no
`sorry` and uses only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Finite
checks are run by Lean's kernel (`decide`), not by compiled evaluation. Each claim below marked
**[proved]** names the Lean theorem. Anything not marked that way is explanation, not a proof.

**About "18".** Your list reads "11, 18, 71, 97, 109". 18 is not prime (`eighteen`). Every earlier
document lists the five as **19**, 71, 97, 109, 11, so I have taken 19 to be the intended prime.
18 still appears in two real ways: it is 19 − 1, and it is exactly the number of hexagonal-lattice
points on the circle of squared radius 19² (`eighteen`, [proved]). If you meant 18 on purpose,
tell me the role you have in mind and I will check that version too.

---

## 1. What the project already proved about the five (inventory)

These results came from earlier passes. I re-checked where each one lives. They are all still
in the project and still build.

| prime | earlier proved facts | where |
|---|---|---|
| 19 | least n > 1 with n² ≡ 1 (mod 360); 19² − 1 = 360 | `Temporal.nineteen_least`, `Temporal.nineteen_sq` |
| 19 | the only prime with p − 1 and p + 1 both 5-smooth and p² ≡ 1 (mod 360) | `EmergentLinks.nineteen_unique_smooth_kissing` |
| 19 | 19 = \|5 + 2ω\|² in the hexagonal lattice; the 19-circle flower tiles the plane; unique base-π addresses | `LatticeCalc.Eis.flower19_tiles`, `address_exists/unique` (`SCALING_19.md`) |
| 19 | scaling by 19² is invisible on every dial dividing 360; x ↦ 19x is a reflection of the dial | `LatticeCalc.sq_nineteen_mod_eq_one_iff`, `nineteen_involution` (`LatticeCalc/Scale361.lean`) |
| 19 | every tetration tower of 19 sits on the mark 19 of the 360 dial | `TowerFold.tower_nineteen` |
| 19 | the first "two-spoke" prime (19, 109, 179, 181, … infinitely many) | `TwoSpokePrimes`, `TwoSpokeInfinite` |
| 19 | order 800 mod 144000 and 2400 mod 1008000 | `SeventhRim.nineteen_order_rim` |
| 19 | p = 19, q = 181: x¹⁸¹ = x for every residue mod 3439 | `KeyExponent.nineteen_181_closure` |
| 71 | 71² − 1 = 7! (the only such number); 71 is the least n > 1 with n² ≡ 1 (mod 2520) | `FiveStage.witness_71`, `SeventhRimPrimes.least_root_2520` |
| 71 | order 20 on the 7200 dial; fails stage 1 and first appears at the heptadic stage | `RodsCompletion.orderOf_71_mod_7200`, `FiveStage.witnesses_vs_stages` |
| 97 | passes stage 1 (96 divides all six layers); dual 7-smooth (98 = 2·7²); 97² ≡ 49 (mod 360) | `FiveStage.witness_97` |
| 97 | on the √3 Pell chain 2 → 7 → 97 (97² − 3·56² = 1, 97 = 2·7² − 1) | `ShellRelations.pell_chains` |
| 109 | 109² ≡ 1 (mod 360); certified prime by the stage-5 test; fails stages 1 and 4 (108 = 2²·3³) | `FiveStage.witness_109` |
| 109 | 360 ≡ 33, 144000 ≡ 11, 1008000 ≡ 77 (mod 109) | `FiveStage.witness_109` |
| 11 | π(33) = 11; passes stage 1; dual 7-smooth | `FiveStage.witness_11`, `PrimeCountSelfReference` |
| all five | p − 1 against 144000 and 1008000; squares mod 360 | `PrimeCountSelfReference.witness_primes_bounds` |

The earlier conclusion (`FIVE_STAGE.md`) still stands: the five-stage filters are fixed by
144000 = 2⁷·3²·5³ and the factor 7, and the five primes are not inputs to them. What is new in this
pass is that the five **do** have a sharp, provable role in *graphing*: each one either adds
lattice geometry or it does not, and which one it is can be read off from p mod 12.

---

## 2. The five as a rod set

* All five are prime, and their squares 121, 361, 5041, 9409, 11881 are pairwise coprime
  (`core_prime`, `core_sq_pairwise_coprime`) [proved].
* Their product is `coreScale = (11·19·71·97·109)² = 156892747² = 24615334061206009`
  (`coreScale_eq`) [proved].
* **The core rods.** Arithmetic modulo `coreScale` splits exactly into five independent rods, one
  for each square (`coreRods`, a ring isomorphism by the Chinese remainder theorem) [proved]. This
  is the "core structure" you asked for: a fixed rod set with capacity about 2.5·10¹⁶, to which
  further coprime rods can be appended without disturbing it (`DynamicRods.extendEquiv`, earlier).
* Arithmetic relations among the five (`core_relations`) [proved]:
  19 + 71 = 90, 109 − 19 = 90, 71 − 11 = 60, 109 − 97 = 12, 11 + 97 = 109 − 1,
  11² − 1 = 5!, 19² − 1 = 360, 71² − 1 = 7!, 97² − 1 = 2⁶·3·7², 109² − 1 = 33·360.

---

## 3. The main answer: which squares make a graph richer

### 3.1 What "geometrically rich" can mean precisely

I measure the richness of a graph's scale by the number of lattice points on each circle. These
are the exact, rational directions the graph can draw with no rounding. The project already proves
the exact counting formulas for every radius (`JacobiTwoSquares.r2_eq` for the square grid,
`JacobiHex.rHex_eq` for the hexagonal / flower grid). This pass turns them into a **scaling law**.

### 3.2 The scaling law [proved]

For a prime p not dividing m (`r2_scale`, `rHex_scale`, `r2_scale_split_inert`,
`rHex_scale_split_inert`):

| p | square grid: r2(pʲ·m) | hexagonal grid: rHex(pʲ·m) |
|---|---|---|
| p ≡ 1 (mod 4) | (j + 1)·r2(m) | — |
| p ≡ 3 (mod 4) | r2(m) if j even, 0 if j odd | — |
| p ≡ 1 (mod 3) | — | (j + 1)·rHex(m) |
| p ≡ 2 (mod 3) | — | rHex(m) if j even, 0 if j odd |

A prime that **splits** in a grid multiplies the exact points on every circle. A prime that is
**inert** adds nothing. For an inert prime this is a statement about geometry, not only about
counts: every point on the scaled circle is just a dilated old point (`sq_inert_dilation`,
`hex_inert_dilation`) [proved]. Scaling by an inert p² is a pure change of units.

### 3.3 The five, classified [proved]

Modulo 12 the five are 11, 7, 11, 1, 1 (`core_mod_twelve`, `core_chi`):

| prime | mod 12 | square grid | hexagonal grid | explicit splitting |
|---|---|---|---|---|
| 11 | 11 | inert | inert | — |
| 19 | 7 | inert | **splits** | 19 = 5² − 5·2 + 2² |
| 71 | 11 | inert | inert | — |
| 97 | 1 | **splits** | **splits** | 97 = 9² + 4² = 11² − 11·3 + 3² |
| 109 | 1 | **splits** | **splits** | 109 = 10² + 3² = 12² − 12·5 + 5² |

(`core_splittings`.) A prime splits in both grids exactly when it is ≡ 1 (mod 12)
(`splits_both_iff`). Below 110 these primes are 13, 37, 61, 73, 97, 109
(`splits_both_below_110`) [proved]. **So 97 and 109 are the two primes of your set that enrich
both kinds of graph. 19 enriches only hexagonal graphs, and 11 and 71 enrich neither.**

New directions from the split squares (`split_new_directions`) [proved]:
65² + 72² = 97², 60² + 91² = 109²; hexagonal: (21, 16) on 19², (112, 57) on 97², (119, 95) on 109².
None of these points is a multiple of p, so each is a genuinely new exact direction.

### 3.4 Your 19² practice, made exact [proved]

(`nineteen_sq_scale`, for m not divisible by 19)

* Multiplying squared lengths by 19²: square-grid points unchanged, hexagonal points ×3.
* Multiplying coordinates by 19² (squared lengths by 19⁴): square-grid unchanged, hexagonal ×5.

So your habit of multiplying by 19² and normalizing afterwards really does add structure, but only
on a hexagonal (flower) grid. On a square pixel grid it adds resolution but no new exact circle
directions. This matches `SCALING_19.md`, which showed that the 19² scale is a two-level step of the
self-similar flower tiling.

### 3.5 The squares of the whole coprime set [proved]

(`core_pow_scale`, `coreScale_richness`, for m ≥ 1 coprime to 11·19·71·97·109)

* Multiplying squared lengths by (11·19·71·97·109)ᵉ multiplies the square-grid points by (e+1)²
  and the hexagonal points by (e+1)³ when e is even, and leaves **no** lattice points when e is odd.
* So scaling by coreScale gives ×9 (square) and ×27 (hexagonal). Scaling coordinates by coreScale
  gives ×25 and ×125.
* The factors 11² and 71² contribute rods (capacity) but **no geometry**, and 19² contributes only
  to the hexagonal grid. Using 97²·109² gives the same square-grid gain, and 19²·97²·109² the same
  hexagonal gain, at a much smaller scale.

**Recommendation.** For the richest graph per digit of scale, use distinct primes that split in
the grid you draw on, each to the first or second power, rather than high powers of one prime:
* square grid: primes ≡ 1 (mod 4): 5, 13, 17, 29, 37, …, 97, 109;
* hexagonal grid: primes ≡ 1 (mod 3): 7, 13, 19, 31, 37, …, 97, 109;
* both at once: primes ≡ 1 (mod 12): 13, 37, 61, 73, 97, 109, ….

`power_vs_distinct` [proved] states the comparison: one prime to the power e gives e + 1 times the
points, while e distinct split primes give 2ᵉ, and e + 1 < 2ᵉ for e ≥ 2.

### 3.6 Tetration towers as scales [proved]

* A tower p↑↑k is a single huge power of p, so on the lattice it gains only (exponent + 1) points,
  the least efficient use of digits (`power_vs_distinct`). The size grows so fast that p↑↑3 cannot
  be written down (97↑↑3 = 97^(97^97)).
* On the rods, a tower of p of height ≥ 2 reads **0** on its own rod p² (`tower_self_on_square`),
  so it cannot be normalized away there (see §4). On every other rod it settles onto one fixed
  residue (`TowerFold.tower_eventually_const`, earlier).
* On the 360 dial every tower of 19, 71 or 109 sits on the prime itself
  (`TowerFold.tower_mod_360_of_sq_one`, earlier).

Conclusion: a tetration tower does not give a richer graph than a product of distinct split
primes. On the dial it collapses to one mark, and on the lattice it is the least rich scale for
its size.

---

## 4. Scaling, then normalizing [proved]

* **Exactness criterion** (`scale_bijective_iff`): multiplying by s on the rods modulo M can be
  undone exactly iff gcd(s, M) = 1.
* On the 360 dial, 19² ≡ 1, so scaling by it changes nothing there. On the core rods it cannot be
  undone, because it wipes the 19² rod (`nineteen_sq_kills_core_rod`).
* Every core square is coprime to 360, so each is an exact, invertible scale on the dial
  (`core_sq_invertible_360`).

Practical rule: keep the scale and the rod modulus coprime. Scale by the split primes, and carry the
rods on different primes, or at least not on the scale's own primes.

---

## 5. The five on the 360 dial [proved]

* Squares mod 360: 11² ≡ 121, 19² ≡ 1, 71² ≡ 1, 97² ≡ 49, 109² ≡ 1 (`core_sq_mod360`).
* Orders on the dial: 11 has order 6, 97 has order 12 (the largest possible on this dial), and
  19, 71 and 109 have order 2 (`core_orders_360`).
* **The three involutions generate a group.** 19, 71 and 109 generate the 8-element group
  {1, 19, 71, 109, 161, 179, 269, 271} of square roots of 1. The other 8 square roots are its coset
  89·{…} = {89, 91, 181, 199, 251, 289, 341, 359}. Together they are all 16 square roots of 1 mod
  360 (`involution_subgroup`).

So on the dial the five split into two roles: three reflections (19, 71, 109) that generate half of
all symmetries of order 2, and two rotations (11 of order 6, 97 of order 12).

---

## 6. n = pq and Q to k

* **A semiprime on the circle** (`semiprime_circle`) [proved]: for distinct primes p, q, the circle
  through pq has 4(1 + χ₄(p))(1 + χ₄(q)) square-grid points and 6(1 + χ₃(p))(1 + χ₃(q)) hexagonal
  points. So n = pq shows 16 square-grid points exactly when both factors are ≡ 1 (mod 4).
* **Example 97·109 = 10573** (`pair_97_109`) [proved]: 16 square-grid and 24 hexagonal points. Two
  essentially different points, 78² + 67² = 102² + 13² = 10573, reveal the factor:
  gcd(78·102 + 67·13, 10573) = 97. This is where the graph of n "contains" p and q. The limitation
  is that finding a second point is as hard as factoring n, so the picture encodes the factors but
  does not by itself find them faster.
* **Squares break the Q-to-k identity** (`korselt_fails_on_square`) [proved]: for every prime p
  and every k ≥ 1, p^(k+1) ≢ p (mod p²). The identity x^(k+1) ≡ x behind the Q-to-k splitting
  (`KeyExponent.korselt`) holds only on squarefree moduli. **Keep squares for linear scaling and
  plain primes for exponent work.** Also, p(p − 1), the unit count of a square rod, divides neither
  144000 nor 1008000 for any of the five (`core_sq_units_not_clock`, `core_sq_totients`).
* **The core's own exponent** (`core_exponent`) [proved]: the lcm of p − 1 over the five is
  30240 = 2⁵·3³·5·7 = 6·7!. It divides 3·1008000 but not 1008000; the 3³ comes from 108 = 109 − 1.
* **Q to k splits every pair of core primes** with exponent 30240 (`core_pair_qToK`, from the
  library's `qToK_of_multiple`) [proved]. The whole radical 11·19·71·97·109 is split back into the
  five by recursive order splitting (`core_radical_splits`, kernel-checked runs). This works both
  with 30240 and with the clock exponent 144000; the 144000 case is a checked run, not a general
  guarantee.

---

## 7. The fractal structure and "the next rod"

* The library proves that **every** flower number N_k = 3k² + 3k + 1 (1, 7, 19, 37, 61, 91, 127, …)
  gives a self-similar tiling with unique addresses (`LatticeCalc.Eis.hexBall_tiles`,
  `addressB_exists`, `addressB_unique`, earlier). This is the structure that can "calculate its own
  next level".
* Of the five, only 19 is a flower number (`core_flower_numbers`) [proved]. 97 and 109 split in the
  hexagonal lattice, so they have tilings too, but their digit sets are not round flowers. That
  general statement is not formalized here.
* **Flowers that are rich in both grids** (`flower_mod_twelve`) [proved]: N_k ≡ 1 (mod 12) exactly
  when k ≡ 0 or 3 (mod 4); otherwise N_k ≡ 7 (mod 12) and has a prime factor inert in the square
  grid. The next flowers after 19 are 37 and 61, both primes ≡ 1 (mod 12) (`next_flowers`).
* A concrete growth rule that follows from these theorems: start from the core rods. To grow the
  graph's geometry, add the next unused prime ≡ 1 (mod 12) (13, 37, 61, 73, …) or the next flower
  prime. To grow capacity only, add any coprime rod (`DynamicRods.least_coprime_prime`: the least
  new coprime rod is always prime). The geometric gain per step is given exactly by §3.2. This rule
  is my synthesis of the proved pieces; it is not a single Lean theorem.

---

## 8. What remains open or not formalized

* The general tiling for a split prime whose norm is not a flower number (97, 109): standard
  mathematics, not formalized here.
* Any meaning of "tetration tower" other than a power tower a↑↑k: if you intend something else
  (for example, a tower whose levels are different primes), give the rule and I will check it.
* Richness measured in some other way (angles spread evenly, visual density, etc.) would need its
  own definition. Everything here uses exact lattice-point counts.
* Whether 18 was intentional (see the top).
