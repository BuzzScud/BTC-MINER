# Rods, flowers, shells and towers: where 11 and 71 put their geometry, and Q to k

Lean files: `RequestProject/RodCircles.lean`, `RequestProject/RodScaling.lean`,
`RequestProject/ShellEnrichment.lean`, `RequestProject/TowerCollapse.lean`,
`RequestProject/BaseDensity.lean`.
Every item marked **[proved]** builds with no `sorry` and uses only Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). **[checked]** marks a finite computation run by
the Lean kernel (`decide +kernel`): it is exact, but it covers only the listed cases.

---

## 0. The pattern in one paragraph

There is a **duality** between the integer lattice and the rods. On the integer lattice (circles
x² + y² = n and x² + xy + y² = n drawn with integer points), a prime that *splits* (97, 109, and 19 on
the flower grid) adds new points, and an *inert* prime (11, 71, and 19 on the square grid) adds none.
On a **rod**, meaning the same circle drawn with residues mod p, it goes the other way: an inert
prime gives the **largest possible circle, p + 1 points**, and a split prime gives p − 1.
So 11 and 71 are not geometrically empty. Their geometry is on the rods, in the rod circles of
12 and 72 points, and in 3D and 4D shells. It is not in the planar lattice.

---

## 1. Circles on the rods (`RodCircles.lean`)

* **Counting law** (`conic_card_add`) [proved]. Take any finite field with q elements and odd
  characteristic, and any c ≠ 0. Then
  #{x² + c y² = 1} + #{t : c t² = −1} = q + 1.
  The proof is stereographic projection from the point (−1, 0). So a rod circle always has
  q − 1 or q + 1 points.
* **Square circle on the rod p** (`sqCircle_card_of_mod_four_eq_one` / `_three`) [proved]: p − 1
  points if p ≡ 1 (mod 4), p + 1 if p ≡ 3 (mod 4).
* **Flower (hexagonal) circle on the rod p**, p > 3 (`hexCircle_card_of_mod_three_eq_one` /
  `_two`) [proved]: p − 1 points if p ≡ 1 (mod 3), p + 1 if p ≡ 2 (mod 3). This holds for every
  prime. The p ≡ 1 case uses an element of order 3; no table lookup is involved.
* **The five core rods** (`core_rod_circles`) [proved]:

  | rod p | p mod 12 | square circle | flower circle | lattice role |
  |-------|----------|---------------|---------------|--------------|
  | 11    | 11       | **12**        | **12**        | inert in both |
  | 19    | 7        | 20            | **18**        | flower only |
  | 71    | 11       | **72**        | **72**        | inert in both |
  | 97    | 1        | 96            | 96            | split in both |
  | 109   | 1        | 108           | 108           | split in both |

  11 and 71 have the *largest* rod circles relative to their size, in both grids at once.
* **Twelve-fold agreement** (`twelve_fold`) [proved]. When p ≡ ±1 (mod 12), both rod circles have
  the same size and that size is a multiple of 12. Four of the five core primes (11, 71, 97, 109)
  are of this kind. Only 19 is mixed, with 20 square points and 18 flower points.
* **Geometry across rods multiplies** (`formPts_card_mul`) [proved]. By the Chinese remainder
  theorem, for coprime rods m, n and *any* binary quadratic form a x² + b xy + c y² = 1, the number
  of points mod mn is the product of the numbers mod m and mod n. On the whole core
  (`core_modulus_circle_counts`) [proved]:
  * the square circle mod 11·19·71·97·109 has 12·20·72·96·108 points;
  * the flower circle has 12·18·72·96·108 points.

  Here 11 and 71 contribute factors 12 and 72, just as 97 and 109 contribute 96 and 108.
* **Scaling a rod to its square** (`RodScaling.lean`) [checked]. The rod 11² = 121 has 132 = 11·12
  points on both circles, and the rod 19² = 361 has 342 = 19·18 flower points. Squaring a rod
  multiplied the count by p in these cases. A general theorem for every p^k (Hensel lifting) is not
  formalized here.
* **On the 360 dial** (`rod_circles_on_dial`) [proved]: the rod circles 12, 20, 72, 18 divide 360;
  96 and 108 do not.

## 2. The flower geometry (`RodCircles.lean`)

* **Flower divisors** (`flower_prime_divisor`) [proved]. Every prime factor of a flower number
  N_k = 3k² + 3k + 1 is ≡ 1 (mod 3). The reason is that N_k = (k+1)² + (k+1)k + k², so
  (k+1)/k is a cube root of unity mod p.
* **Hence 11 and 71 never divide any flower number** (`eleven_seventyone_never_flower`) [proved].
  They cannot enrich the flower tiling in the lattice, at any scale. This answers "do they improve
  the flower geometry?" for the lattice: **no, provably never.**
* **The flower on its own rod** (`flower_prime_hexCircle`) [proved]. If N = 3k² + 3k + 1 is prime,
  the flower circle on the rod N has exactly N − 1 = 3k(k+1) points. That is one point for every
  non-central cell of the flower, since 6·(1 + 2 + ⋯ + k) = 3k(k+1). For k = 2 the flower is 19
  and its rod circle has **18** points (`nineteen_flower`). This gives a third proved role for 18,
  after 19 − 1 and the 18 lattice points on the circle of squared radius 19².

## 3. Larger shells: 3D and 4D (`ShellEnrichment.lean`)

`shellCount d n` counts integer vectors in ℤ^d with x₁² + ⋯ + x_d² = n. It is defined by
peeling off one coordinate at a time. The table below is [checked]:

| n    | 2D | 3D  | 4D   |
|------|----|-----|------|
| 1    | 4  | 6   | 8    |
| 11   | 0  | 24  | 96   |
| 19   | 0  | 24  | 160  |
| 71   | 0  | **0** | 576 |
| 97   | 8  | 48  | 784  |
| 109  | 8  | 72  | 880  |
| 121  | 4  | 78  | 1064 |
| 209  | 0  | 240 | 1920 |
| 5041 | 4  | 438 | —    |

* **71 is invisible in 3D** (`seventyone_empty_3d`) [proved]. No integer ≡ 7 (mod 8) is a sum of
  three squares (`mod_eight_no_three_squares`), and 71 ≡ 7 (mod 8). But 71² = 5041 ≡ 1 (mod 8), and
  the 3D shell of 71² has 438 = 6·73 points [checked].
* **11 is visible in 3D** (24 points). Its square gives 78 = 6·13.
* **3D scaling.** In these checked cases, squaring an inert prime multiplied the 6 axis points by
  p + 2 (13 for 11, 73 for 71), and squaring a split prime would multiply them by p. So in 3D the
  inert primes enrich *more* than the split ones. The general formula behind this (Gauss's
  three-square count) is not formalized. Only the checked values are claimed.
* **In 4D every core prime enriches** (`four_d_core`) [checked]: each core prime p carries
  8(p + 1) points, e.g. 96 = 8·12 for 11 and 576 = 8·72 for 71. That is the same p + 1 as the rod
  circle of an inert prime. Jacobi's four-square theorem (8σ(n) for odd n) explains this in general
  but is not formalized here. Also r₄(11·19) = 1920 = 8·12·20 [checked]: in 4D the counts
  multiply across coprime factors.

**Answer to "do they enrich larger shells or the geometry across rods?"** Yes, on both counts:
* across rods they carry the maximal circles, 12 and 72, in both grids;
* in 4D they add 8(p + 1) points like every prime;
* in 3D, 11 enriches and 71 is absent at first power but enriches strongly when squared.

## 4. Towers of three coprimes (`TowerCollapse.lean`)

A tower here is a^(b^c) with a, b, c coprime.

* **Collapse law** (`tower_collapse`) [proved]. Suppose a^E ≡ 1 (mod m) and b^F ≡ 1 (mod E). Then
  a^(b^c) ≡ a^(b^(c mod F)) (mod m). One level up (`tower4_collapse`) [proved]: if also
  c^G ≡ 1 (mod F), then a^(b^(c^d)) ≡ a^(b^(c^(d mod G))). The tower is governed by a
  **descending chain of moduli**. This chain is the fractal structure: each level of the tower
  sees only the residue that the level below allows.
* **On the 360 dial** the chain is 360 → 12 → 2 (`dial_tower`, `dial_tower_two_values`) [proved].
  For a coprime to 360 and b coprime to 12, a^(b^c) ≡ a when c is even and ≡ a^b when c is odd.
  Every three-coprime tower on the dial takes **only two values**.
* **On the core dial M = 11·19·71·97·109** the chain is M → 30240 → 72 → 6 → 2
  (`core_units`, `units_30240`, `units_72`) [proved].
  * A three-level tower depends on its top only mod 72 (`core_tower3`) [proved].
  * A four-level tower depends on its top only mod 6 (`core_tower4`) [proved].
  * The 72 is attained (`core_tower_sharp`) [checked]: 7^(11^c) mod M for c = 0, …, 71 are 72
    distinct values.
  * The number 72 that caps the core's towers is the same as the size of 71's rod circle. The two
    have different sources: λ(30240) = 72 on one side, 71 + 1 on the other. The coincidence is
    recorded, not explained.
* **What this means for information content.** A three-coprime tower on a dial of size m carries
  at most (units mod m) × (residues of b mod E) × F distinct values. That count is finite and
  usually small, however large the tower is numerically. This is the proved statement. Any
  application to black-hole information density would need its own model and is not claimed.

## 5. n = pq and Q to k (`BaseDensity.lean`)

What was already proved (earlier files):
* `splitWith_isSome_iff`: order splitting with base a and any multiple E of
  k = lcm(p − 1, q − 1) succeeds **exactly** when ord_p(a) ≠ ord_q(a).
* `qToK_pq`: it then returns p, q and k.
* `PQRecovery`: finding k from n and factoring n are equivalent; each is computed from the other by
  a deterministic procedure.

New:
* **At least half of all bases work** (`half_bases_split`) [proved]. Take distinct primes p, q, any
  nonzero multiple E of k, and rs containing the primes of E. Then at least (p − 1)(q − 1)/2 bases
  a ∈ [0, pq) split pq. The key count (`bad_units_card`): unit pairs with equal orders number at
  most g², where g = gcd(p − 1, q − 1), and 2g² ≤ (p − 1)(q − 1). A random base therefore succeeds
  with probability at least (p − 1)(q − 1)/(2pq), close to 1/2, so on average about two bases are
  needed.
* **The clock family is completely solved** (`clock_half_bases_split`) [proved]. This covers every
  pair of distinct primes with p − 1, q − 1 ∣ 144000, and so every pair from the qualifying set Q
  (`Q_half_bases_split`) [proved]. The fixed exponent 144000 with rs = [2, 3, 5] splits pq for at
  least half of all unit bases. Each attempt costs at most 8 + 3 + 4 = 15 gcd tests. The routine is
  never told p or q.

**Where the problem really stands.** Two steps are now completely solved:
* turning a multiple of k into p, q and k, with at least half of bases working, proved;
* the whole Q/clock family, where the multiple 144000 is known in advance.

The remaining step is producing a multiple of k = λ(pq) **from n alone** for arbitrary p, q. By
the proved equivalence with factoring, that step *is* factoring. No fast general method is known,
and nothing here provides one. Methods that work are exactly those that know a multiple of k in
advance:
* the clock family (p − 1 5-smooth);
* smooth p − 1 in general (Pollard's p − 1 idea);
* the core family (exponent 30240, `core_pair_qToK`).

"Any Q and any pq" cannot be solved *completely* without solving factoring in general. What can be
done, and is done here, is to solve it completely on every family whose exponent is known, with a
proved success rate.

**More complex coprime sets.** Two things are available now:
* a squarefree n with more primes is split by recursive order splitting, as in the kernel-checked
  run `core_radical_splits`;
* across rods, the geometry multiplies by `formPts_card_mul`.

A general success-rate theorem for three or more primes (the analogue of `half_bases_split`) is not
yet formalized. It would need a many-prime version of the library's completeness theorem.

## 6. Open / next

* Hensel lifting in general (rod p^k circle = p^(k−1)(p ∓ 1)): only instances are checked.
* Proving `shellCount` equals the cardinality of the integer point set; it is currently the
  defining recursion. Jacobi's four-square and Gauss's three-square formulas are also unproved
  here.
* A many-prime version of `half_bases_split`.
* Tetration towers with more than three distinct coprimes: `tower4_collapse` already covers four
  levels. Longer chains follow the same pattern but are not stated.
