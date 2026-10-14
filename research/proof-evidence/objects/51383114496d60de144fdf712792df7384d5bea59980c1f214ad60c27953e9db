module

public import Mathlib
public import RequestProject.JacobiTwoSquares
public import RequestProject.JacobiHex
public import RequestProject.TowerFold
public import LatticeCalc.Verified.OrderSplit

/-!
# The five core primes `11, 19, 71, 97, 109`, their squares, and graph scaling

The research names five primes, `19, 71, 97, 109, 11`, as special when modelling and graphing.
This file studies them as a **core rod set** and as **scale factors for graphs**.

* **Rods.**  The five squares `121, 361, 5041, 9409, 11881` are pairwise coprime, so the
  arithmetic modulo their product `coreScale = (11·19·71·97·109)²` splits exactly into five
  independent rods (`coreRods`, Chinese remainder theorem).
* **The scaling law (general).**  Graph richness is measured by the number of lattice points on
  a circle: `r2 n` for the square grid, `rHex n` for the hexagonal (flower) grid.  For a prime
  `p` not dividing `m` (`r2_scale`, `rHex_scale`):
  `r2 (p^j · m) = (1 + χ₄(p) + … + χ₄(p)^j) · r2 m`, and the same for `rHex` with `χ₃`.
  So a prime `p ≡ 1 (mod 4)` (resp. `≡ 1 (mod 3)`) multiplies the points by `j + 1`, while any
  other prime `p ≠ 2, 3` adds **nothing** (even `j`) or empties the circle (odd `j`).
* **Which of the five enrich which grid** (`core_mod_twelve`, `core_chi`): modulo 12 the five are
  `11, 7, 11, 1, 1`.  `97` and `109` split in both grids, `19` only in the hexagonal grid,
  `11` and `71` in neither.  A prime splits in both grids iff it is `≡ 1 (mod 12)`
  (`splits_both_iff`), and the first six such primes are `13, 37, 61, 73, 97, 109`.
* **The whole core as a scale** (`core_pow_scale`): multiplying all squared lengths by
  `(11·19·71·97·109)^e` multiplies the square-grid points by `(e+1)²` and the hexagonal points by
  `(e+1)³` when `e` is even, and leaves no points at all when `e` is odd.
  `sq_inert_dilation`, `hex_inert_dilation`: for an inert prime every point on the scaled
  circle is just a dilated old point, so `11²` and `71²` add rods but no geometry.
* **Scaling then normalizing** (`scale_bijective_iff`): multiplying by `s` on the rods modulo `M`
  can be undone exactly iff `gcd(s, M) = 1`.  So `19²` is harmless on the 360 dial (where it is
  the identity) but destroys the `19²` rod of the core (`nineteen_sq_kills_core_rod`).
* **The dial** (`core_sq_mod360`, `involution_subgroup`): `19, 71, 109` square to `1` modulo 360
  and generate an 8-element subgroup of the 16 square roots of 1; `11` and `97` have orders
  6 and 12 on the dial.
* **Q to k and squares** (`korselt_fails_on_square`): the exponent identity `x^(k+1) ≡ x` that
  the Q-to-k splitting relies on fails on every square rod; `p(p − 1)`, the unit count of a
  square rod, never divides `144000` or `1008000` for the five (`core_sq_units_not_clock`).
* **Tetration** (`tower_self_on_square`): a tower of `p` of height `≥ 2` reads `0` on the rod
  `p²`, so as a scale factor it cannot be normalized away on its own rod.  `power_vs_distinct`:
  one prime to the power `e` gives `e + 1` times the points, `e` distinct split primes give `2^e`.
* **`n = p q`** (`semiprime_circle`, `pair_97_109`): the circle through `p q` has
  `4(1 + χ₄(p))(1 + χ₄(q))` square-grid and `6(1 + χ₃(p))(1 + χ₃(q))` hexagonal points.
* **Flowers** (`core_flower_numbers`, `flower_mod_twelve`, `next_flowers`): of the five only `19`
  is a flower number `3k² + 3k + 1`; the next flowers `37, 61` are primes `≡ 1 (mod 12)`.
* **Q to k on the core** (`core_exponent`, `core_pair_qToK`, `core_radical_splits`): the lcm of
  the `p − 1` is `30240 = 6·7!`; with it every pair of core primes splits, and the radical
  `11·19·71·97·109` splits back into the five.
-/

@[expose] public section

namespace CorePrimes

open DivisorRecursion JacobiTwoSquares JacobiHex

/-! ## The core set -/

/-- The five core primes of the research. -/
def core : List ℕ := [11, 19, 71, 97, 109]

theorem core_prime : ∀ p ∈ core, p.Prime := by
  intro p hp
  simp only [core, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- The squares of the core primes are pairwise coprime. -/
theorem core_sq_pairwise_coprime : (core.map (· ^ 2)).Pairwise Nat.Coprime := by
  decide

/-- The product of the core primes. -/
def coreRadical : ℕ := 11 * 19 * 71 * 97 * 109

/-- The product of the squares of the core primes. -/
def coreScale : ℕ := coreRadical ^ 2

theorem coreScale_eq :
    coreRadical = 156892747 ∧ coreScale = 11 ^ 2 * 19 ^ 2 * 71 ^ 2 * 97 ^ 2 * 109 ^ 2 ∧
      coreScale = 24615334061206009 := by
  refine ⟨by norm_num [coreRadical], by norm_num [coreScale, coreRadical], by
    norm_num [coreScale, coreRadical]⟩

/-- The five square rods. -/
def coreSq : Fin 5 → ℕ := ![121, 361, 5041, 9409, 11881]

theorem coreSq_prod : ∏ i, coreSq i = coreScale := by
  rw [Fin.prod_univ_five]
  show 121 * 361 * 5041 * 9409 * 11881 = coreScale
  norm_num [coreScale, coreRadical]

/-- **The core rods.** Arithmetic modulo `coreScale` splits exactly into the five square rods. -/
noncomputable def coreRods : ZMod coreScale ≃+* ((i : Fin 5) → ZMod (coreSq i)) :=
  (ZMod.ringEquivCongr coreSq_prod.symm).trans
    (ZMod.prodEquivPi coreSq (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide))

/-- `18` is not prime; it is `19 − 1`, and it is the number of hexagonal lattice points on the
circle of squared radius `19²`. -/
theorem eighteen : ¬ (18 : ℕ).Prime ∧ 18 = 19 - 1 ∧ rHex (19 ^ 2) = 18 := by
  refine ⟨by norm_num, rfl, ?_⟩
  have h := rHex_rec 19 19 (by norm_num) (by norm_num)
  have h19 := rHex_prime_one_mod_three (p := 19) (by norm_num) (by norm_num)
  have hc : chi3 19 = 1 := by decide
  rw [if_pos (dvd_refl 19), Nat.div_self (by norm_num), rHex_one, h19, hc] at h
  rw [pow_two]; omega

/-- Arithmetic relations among the five (and `p² − 1`). -/
theorem core_relations :
    19 + 71 = 90 ∧ 109 - 19 = 90 ∧ 71 - 11 = 60 ∧ 109 - 97 = 12 ∧ 11 + 97 = 109 - 1 ∧
    11 ^ 2 - 1 = Nat.factorial 5 ∧ 19 ^ 2 - 1 = 360 ∧ 71 ^ 2 - 1 = Nat.factorial 7 ∧
    97 ^ 2 - 1 = 2 ^ 6 * 3 * 7 ^ 2 ∧ 109 ^ 2 - 1 = 33 * 360 := by
  decide

/-! ## The two lattices: which core primes split -/

/-- The five core primes modulo 12, 4 and 3. -/
theorem core_mod_twelve :
    core.map (· % 12) = [11, 7, 11, 1, 1] ∧ core.map (· % 4) = [3, 3, 3, 1, 1] ∧
      core.map (· % 3) = [2, 1, 2, 1, 1] := by
  decide

/-- The characters `χ₄`, `χ₃` on the core primes (`1` = splits, `−1` = inert). -/
theorem core_chi :
    core.map chi4 = [-1, -1, -1, 1, 1] ∧ core.map chi3 = [-1, 1, -1, 1, 1] := by
  decide

/-- Explicit splittings: `97 = 9² + 4²`, `109 = 10² + 3²`, and in the hexagonal grid
`19 = 5² − 5·2 + 2²`, `97 = 11² − 11·3 + 3²`, `109 = 12² − 12·5 + 5²`. -/
theorem core_splittings :
    9 ^ 2 + 4 ^ 2 = 97 ∧ 10 ^ 2 + 3 ^ 2 = 109 ∧
    5 ^ 2 - 5 * 2 + 2 ^ 2 = 19 ∧ 11 ^ 2 - 11 * 3 + 3 ^ 2 = 97 ∧ 12 ^ 2 - 12 * 5 + 5 ^ 2 = 109 := by
  decide

/-- A prime splits in both grids iff it is `≡ 1 (mod 12)`. -/
theorem splits_both_iff (p : ℕ) : chi4 p = 1 ∧ chi3 p = 1 ↔ p % 12 = 1 := by
  unfold chi4 chi3
  constructor
  · rintro ⟨h4, h3⟩
    split_ifs at h4 h3 <;> omega
  · intro h
    have h4 : p % 4 = 1 := by omega
    have h3 : p % 3 = 1 := by omega
    simp [h4, h3]

/-- The primes below 110 that split in both grids. -/
theorem splits_both_below_110 :
    (List.range 110).filter (fun p => p.Prime ∧ p % 12 = 1) = [13, 37, 61, 73, 97, 109] := by
  decide

/-! ## The scaling law -/

/-- The one-prime recursion shared by `r2` and `rHex` gives the effect of `p^j`. -/
theorem rec_pow (R : ℕ → ℤ) (c : ℤ) (p m : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hrec : ∀ k, k ≠ 0 → R (p * k) = R k + c * (R k - if p ∣ k then R (k / p) else 0))
    (hm : m ≠ 0) (j : ℕ) :
    R (p ^ j * m) = (∑ i ∈ Finset.range (j + 1), c ^ i) * R m := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have key : ∀ j, R (p ^ j * m) = (∑ i ∈ Finset.range (j + 1), c ^ i) * R m ∧
      R (p ^ (j + 1) * m) = (∑ i ∈ Finset.range (j + 2), c ^ i) * R m := by
    intro j
    induction j with
    | zero =>
      refine ⟨by simp, ?_⟩
      rw [pow_one, hrec m hm, if_neg hpm]
      simp [Finset.sum_range_succ]; ring
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      have hne : p ^ (j + 1) * m ≠ 0 := mul_ne_zero (pow_ne_zero _ hp0) hm
      have hdiv : p ∣ p ^ (j + 1) * m := Dvd.dvd.mul_right (dvd_pow_self p (by omega)) m
      have hq : p ^ (j + 1) * m / p = p ^ j * m := by
        rw [pow_succ, mul_comm (p ^ j) p, mul_assoc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp0)]
      rw [show p ^ (j + 1 + 1) * m = p * (p ^ (j + 1) * m) by ring, hrec _ hne, if_pos hdiv, hq,
        ih.1, ih.2]
      rw [Finset.sum_range_succ _ (j + 2), Finset.sum_range_succ _ (j + 1)]
      ring
  exact (key j).1

/-- **Scaling law, square grid.** -/
theorem r2_scale (p m j : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0) :
    (r2 (p ^ j * m) : ℤ) = (∑ i ∈ Finset.range (j + 1), chi4 p ^ i) * r2 m :=
  rec_pow (fun n => (r2 n : ℤ)) (chi4 p) p m hp hpm (fun k hk => r2_rec p k hp hk) hm j

/-- **Scaling law, hexagonal grid.** -/
theorem rHex_scale (p m j : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0) :
    (rHex (p ^ j * m) : ℤ) = (∑ i ∈ Finset.range (j + 1), chi3 p ^ i) * rHex m :=
  rec_pow (fun n => (rHex n : ℤ)) (chi3 p) p m hp hpm (fun k hk => rHex_rec p k hp hk) hm j

lemma geom_one (j : ℕ) : (∑ i ∈ Finset.range (j + 1), (1 : ℤ) ^ i) = j + 1 := by
  simp

lemma geom_neg_one (j : ℕ) :
    (∑ i ∈ Finset.range (j + 1), (-1 : ℤ) ^ i) = if Even j then 1 else 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd j with h | h
    · have h' : ¬ Even (j + 1) := by rw [Nat.even_add_one]; exact not_not.2 h
      rw [if_pos h, if_neg h', pow_succ, h.neg_one_pow]; ring
    · have h' : Even (j + 1) := by rw [Nat.even_add_one]; exact Nat.not_even_iff_odd.2 h
      rw [if_neg (Nat.not_even_iff_odd.2 h), if_pos h', pow_succ, h.neg_one_pow]; ring

/-- **Split primes enrich, inert primes do not (square grid).**  For `p ≡ 1 (mod 4)` the factor
is `j + 1`; for `p ≡ 3 (mod 4)` it is `1` for even `j` and `0` for odd `j`. -/
theorem r2_scale_split_inert (p m j : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0) :
    (p % 4 = 1 → r2 (p ^ j * m) = (j + 1) * r2 m) ∧
    (p % 4 = 3 → r2 (p ^ j * m) = (if Even j then 1 else 0) * r2 m) := by
  have h := r2_scale p m j hp hpm hm
  refine ⟨fun h1 => ?_, fun h3 => ?_⟩
  · simp only [chi4, h1, if_true] at h
    rw [geom_one] at h; exact_mod_cast h
  · simp only [chi4, h3, show (3 : ℕ) ≠ 1 by norm_num, if_false, if_true] at h
    rw [geom_neg_one] at h
    split_ifs at h ⊢ <;> omega

/-- **Split primes enrich, inert primes do not (hexagonal grid).** -/
theorem rHex_scale_split_inert (p m j : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ m) (hm : m ≠ 0) :
    (p % 3 = 1 → rHex (p ^ j * m) = (j + 1) * rHex m) ∧
    (p % 3 = 2 → rHex (p ^ j * m) = (if Even j then 1 else 0) * rHex m) := by
  have h := rHex_scale p m j hp hpm hm
  refine ⟨fun h1 => ?_, fun h2 => ?_⟩
  · simp only [chi3, h1, if_true] at h
    rw [geom_one] at h; exact_mod_cast h
  · simp only [chi3, h2, show (2 : ℕ) ≠ 1 by norm_num, if_false, if_true] at h
    rw [geom_neg_one] at h
    split_ifs at h ⊢ <;> omega

/-- The `19²` convention.  Multiplying squared lengths by `19²` leaves the square-grid circle
counts unchanged and triples the hexagonal ones; scaling coordinates by `19²` (squared lengths by
`19⁴`) multiplies the hexagonal counts by `5`. -/
theorem nineteen_sq_scale (m : ℕ) (hm : m ≠ 0) (h19 : ¬ 19 ∣ m) :
    r2 (19 ^ 2 * m) = r2 m ∧ rHex (19 ^ 2 * m) = 3 * rHex m ∧
      r2 (19 ^ 4 * m) = r2 m ∧ rHex (19 ^ 4 * m) = 5 * rHex m := by
  have hp : (19 : ℕ).Prime := by norm_num
  have a := (r2_scale_split_inert 19 m 2 hp h19 hm).2 (by norm_num)
  have b := (rHex_scale_split_inert 19 m 2 hp h19 hm).1 (by norm_num)
  have c := (r2_scale_split_inert 19 m 4 hp h19 hm).2 (by norm_num)
  have d := (rHex_scale_split_inert 19 m 4 hp h19 hm).1 (by norm_num)
  simp only [show Even 2 by decide, show Even 4 by decide, if_true, one_mul] at a c
  exact ⟨a, b, c, d⟩

/-! ## Inert primes: every point on the scaled circle is a dilated old point -/

lemma card_eq_of_inj_subset {s t : Finset (ℤ × ℤ)} (f : ℤ × ℤ → ℤ × ℤ) (hf : Function.Injective f)
    (hmap : ∀ q ∈ s, f q ∈ t) (hcard : t.card = s.card) : ∀ q ∈ t, ∃ q' ∈ s, f q' = q := by
  have hsub : s.image f ⊆ t := by
    intro x hx; obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hx; exact hmap q hq
  have heq : s.image f = t :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injective _ hf, hcard])
  intro q hq; rw [← heq] at hq
  obtain ⟨q', hq', h⟩ := Finset.mem_image.1 hq; exact ⟨q', hq', h⟩

lemma dilate_injective (p : ℕ) (hp : p ≠ 0) :
    Function.Injective (fun q : ℤ × ℤ => ((p : ℤ) * q.1, (p : ℤ) * q.2)) := by
  intro a b h
  simp only [Prod.mk.injEq] at h
  have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  exact Prod.ext (mul_left_cancel₀ hp' h.1) (mul_left_cancel₀ hp' h.2)

/-- **Inert primes only dilate (square grid).**  For `p ≡ 3 (mod 4)` every point of the circle
`x² + y² = p² m` is `p` times a point of the circle `x² + y² = m`. -/
theorem sq_inert_dilation (p m : ℕ) (hp : p.Prime) (h3 : p % 4 = 3) (hpm : ¬ p ∣ m) (hm : m ≠ 0)
    (x y : ℤ) (hxy : x ^ 2 + y ^ 2 = ((p ^ 2 * m : ℕ) : ℤ)) :
    ∃ u v : ℤ, x = p * u ∧ y = p * v ∧ u ^ 2 + v ^ 2 = m := by
  have hc : r2 (p ^ 2 * m) = r2 m := by
    have := (r2_scale_split_inert p m 2 hp hpm hm).2 h3
    simpa using this
  obtain ⟨⟨u, v⟩, huv, he⟩ := card_eq_of_inj_subset (s := sqCircle m) (t := sqCircle (p ^ 2 * m))
    _ (dilate_injective p hp.ne_zero) (by
      intro q hq
      rw [mem_sqCircle] at hq ⊢
      push_cast; rw [← hq]; ring) hc (x, y) (mem_sqCircle.2 hxy)
  simp only [Prod.mk.injEq] at he
  exact ⟨u, v, he.1.symm, he.2.symm, mem_sqCircle.1 huv⟩

/-- **Inert primes only dilate (hexagonal grid).** -/
theorem hex_inert_dilation (p m : ℕ) (hp : p.Prime) (h2 : p % 3 = 2) (hpm : ¬ p ∣ m) (hm : m ≠ 0)
    (x y : ℤ) (hxy : x ^ 2 - x * y + y ^ 2 = ((p ^ 2 * m : ℕ) : ℤ)) :
    ∃ u v : ℤ, x = p * u ∧ y = p * v ∧ u ^ 2 - u * v + v ^ 2 = m := by
  have hc : rHex (p ^ 2 * m) = rHex m := by
    have := (rHex_scale_split_inert p m 2 hp hpm hm).2 h2
    simpa using this
  obtain ⟨⟨u, v⟩, huv, he⟩ := card_eq_of_inj_subset (s := hexCircle m)
    (t := hexCircle (p ^ 2 * m))
    _ (dilate_injective p hp.ne_zero) (by
      intro q hq
      rw [mem_hexCircle] at hq ⊢
      push_cast; rw [← hq]; ring) hc (x, y) (mem_hexCircle.2 hxy)
  simp only [Prod.mk.injEq] at he
  exact ⟨u, v, he.1.symm, he.2.symm, mem_hexCircle.1 huv⟩

/-- New directions from split primes: points on the circles of squared radius `p²` that are not
multiples of `p` (`65² + 72² = 97²`, `60² + 91² = 109²`; hexagonal: `(21, 16)` for `19²`,
`(112, 57)` for `97²`, `(119, 95)` for `109²`). -/
theorem split_new_directions :
    65 ^ 2 + 72 ^ 2 = 97 ^ 2 ∧ 60 ^ 2 + 91 ^ 2 = 109 ^ 2 ∧
    21 ^ 2 - 21 * 16 + 16 ^ 2 = 19 ^ 2 ∧ 112 ^ 2 - 112 * 57 + 57 ^ 2 = 97 ^ 2 ∧
    119 ^ 2 - 119 * 95 + 95 ^ 2 = 109 ^ 2 := by
  decide

/-! ## The whole core as a scale factor -/

lemma not_dvd_step {p q m e : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hpm : ¬ p ∣ m) :
    ¬ p ∣ q ^ e * m := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
  · exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow h1))
  · exact hpm h1

lemma not_dvd_of_coprime {p m : ℕ} (hp : p.Prime) (hpr : p ∣ coreRadical)
    (hcop : Nat.Coprime m coreRadical) : ¬ p ∣ m := by
  intro h
  have := Nat.dvd_gcd h hpr
  rw [hcop] at this
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

/-- **The core as a scale.**  For `m ≥ 1` coprime to `11·19·71·97·109`, multiplying squared
lengths by `(11·19·71·97·109)^e` multiplies the square-grid circle points by `(e+1)²` and the
hexagonal ones by `(e+1)³` when `e` is even, and empties both circles when `e` is odd.  Only
`97, 109` (square grid) and `19, 97, 109` (hexagonal grid) contribute. -/
theorem core_pow_scale (e m : ℕ) (hm : m ≠ 0) (hcop : Nat.Coprime m coreRadical) :
    r2 (coreRadical ^ e * m) = (if Even e then (e + 1) ^ 2 else 0) * r2 m ∧
    rHex (coreRadical ^ e * m) = (if Even e then (e + 1) ^ 3 else 0) * rHex m := by
  have p11 : (11 : ℕ).Prime := by norm_num
  have p19 : (19 : ℕ).Prime := by norm_num
  have p71 : (71 : ℕ).Prime := by norm_num
  have p97 : (97 : ℕ).Prime := by norm_num
  have p109 : (109 : ℕ).Prime := by norm_num
  have d11 : ¬ 11 ∣ m := not_dvd_of_coprime p11 (by norm_num [coreRadical]) hcop
  have d19 : ¬ 19 ∣ m := not_dvd_of_coprime p19 (by norm_num [coreRadical]) hcop
  have d71 : ¬ 71 ∣ m := not_dvd_of_coprime p71 (by norm_num [coreRadical]) hcop
  have d97 : ¬ 97 ∣ m := not_dvd_of_coprime p97 (by norm_num [coreRadical]) hcop
  have d109 : ¬ 109 ∣ m := not_dvd_of_coprime p109 (by norm_num [coreRadical]) hcop
  have hsplit : coreRadical ^ e * m = 11 ^ e * (19 ^ e * (71 ^ e * (97 ^ e * (109 ^ e * m)))) := by
    simp only [coreRadical, mul_pow]; ring
  set m4 := 109 ^ e * m with hm4
  set m3 := 97 ^ e * m4 with hm3
  set m2 := 71 ^ e * m3 with hm2
  set m1 := 19 ^ e * m2 with hm1
  have n4 : m4 ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hm
  have n3 : m3 ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) n4
  have n2 : m2 ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) n3
  have n1 : m1 ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) n2
  have e4 : ¬ 97 ∣ m4 := not_dvd_step p97 p109 (by norm_num) d97
  have e3 : ¬ 71 ∣ m3 := not_dvd_step p71 p97 (by norm_num) (not_dvd_step p71 p109 (by norm_num) d71)
  have e2 : ¬ 19 ∣ m2 := not_dvd_step p19 p71 (by norm_num)
    (not_dvd_step p19 p97 (by norm_num) (not_dvd_step p19 p109 (by norm_num) d19))
  have e1 : ¬ 11 ∣ m1 := not_dvd_step p11 p19 (by norm_num) (not_dvd_step p11 p71 (by norm_num)
    (not_dvd_step p11 p97 (by norm_num) (not_dvd_step p11 p109 (by norm_num) d11)))
  rw [hsplit]
  -- square grid
  have s5 := (r2_scale_split_inert 109 m e p109 d109 hm).1 (by norm_num)
  have s4 := (r2_scale_split_inert 97 m4 e p97 e4 n4).1 (by norm_num)
  have s3 := (r2_scale_split_inert 71 m3 e p71 e3 n3).2 (by norm_num)
  have s2 := (r2_scale_split_inert 19 m2 e p19 e2 n2).2 (by norm_num)
  have s1 := (r2_scale_split_inert 11 m1 e p11 e1 n1).2 (by norm_num)
  -- hexagonal grid
  have h5 := (rHex_scale_split_inert 109 m e p109 d109 hm).1 (by norm_num)
  have h4 := (rHex_scale_split_inert 97 m4 e p97 e4 n4).1 (by norm_num)
  have h3 := (rHex_scale_split_inert 71 m3 e p71 e3 n3).2 (by norm_num)
  have h2 := (rHex_scale_split_inert 19 m2 e p19 e2 n2).1 (by norm_num)
  have h1 := (rHex_scale_split_inert 11 m1 e p11 e1 n1).2 (by norm_num)
  rw [← hm4] at s5 h5; rw [← hm3] at s4 h4; rw [← hm2] at s3 h3; rw [← hm1] at s2 h2
  refine ⟨?_, ?_⟩
  · rw [s1, s2, s3, s4, s5]; split_ifs <;> ring
  · rw [h1, h2, h3, h4, h5]; split_ifs <;> ring

/-- Special cases: scaling squared lengths by `coreScale` (coordinates by `√coreScale`) gives
`9×` square-grid and `27×` hexagonal points; scaling coordinates by `coreScale` gives `25×` and
`125×`. -/
theorem coreScale_richness (m : ℕ) (hm : m ≠ 0) (hcop : Nat.Coprime m coreRadical) :
    r2 (coreScale * m) = 9 * r2 m ∧ rHex (coreScale * m) = 27 * rHex m ∧
    r2 (coreScale ^ 2 * m) = 25 * r2 m ∧ rHex (coreScale ^ 2 * m) = 125 * rHex m := by
  have a := core_pow_scale 2 m hm hcop
  have b := core_pow_scale 4 m hm hcop
  rw [show coreScale = coreRadical ^ 2 from rfl, ← pow_mul]
  simp only [show Even 2 by decide, show Even 4 by decide, if_true] at a b
  norm_num at a b ⊢
  exact ⟨a.1, a.2, b.1, b.2⟩

/-! ## Scaling then normalizing on rods -/

/-- **Scale-then-normalize is exact iff the scale is coprime to the rods.**  Multiplication by
`s` on `ZMod M` is a bijection exactly when `gcd(s, M) = 1`. -/
theorem scale_bijective_iff (M s : ℕ) :
    Function.Bijective (fun x : ZMod M => (s : ZMod M) * x) ↔ Nat.Coprime s M := by
  rw [← ZMod.isUnit_iff_coprime]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h.2 1
    exact IsUnit.of_mul_eq_one x hx
  · intro h
    obtain ⟨u, hu⟩ := h
    rw [← hu]
    exact (Units.mulLeft u).bijective

/-- On the 360 dial scaling by `19²` is the identity; on the core rods it is not invertible,
since it kills the `19²` rod. -/
theorem nineteen_sq_kills_core_rod :
    ((19 ^ 2 : ℕ) : ZMod 360) = 1 ∧
    ¬ Function.Bijective (fun x : ZMod coreScale => ((19 ^ 2 : ℕ) : ZMod coreScale) * x) := by
  refine ⟨by decide, ?_⟩
  rw [scale_bijective_iff]
  norm_num [coreScale, coreRadical]

/-- Each core square is an invertible scale on the 360 dial. -/
theorem core_sq_invertible_360 : ∀ p ∈ core, Nat.Coprime (p ^ 2) 360 := by
  decide

/-! ## The core primes on the 360 dial -/

theorem core_sq_mod360 : core.map (fun p => p ^ 2 % 360) = [121, 1, 1, 49, 1] := by decide

/-- On the 360 dial `11` has order 6 and `97` has order 12 (the largest possible). -/
theorem core_orders_360 :
    orderOf (11 : ZMod 360) = 6 ∧ orderOf (97 : ZMod 360) = 12 ∧
    orderOf (19 : ZMod 360) = 2 ∧ orderOf (71 : ZMod 360) = 2 ∧ orderOf (109 : ZMod 360) = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [orderOf_eq_iff (by norm_num)]
    exact ⟨by decide, by decide⟩

/-- The involutions `19, 71, 109` generate the 8-element group
`{1, 19, 71, 109, 161, 179, 269, 271}` of square roots of 1 on the 360 dial; the other 8 square
roots of 1 are its coset `89 · {…} = {89, 91, 181, 199, 251, 289, 341, 359}`. -/
theorem involution_subgroup :
    19 * 71 % 360 = 269 ∧ 19 * 109 % 360 = 271 ∧ 71 * 109 % 360 = 179 ∧
    19 * 71 * 109 % 360 = 161 ∧
    (∀ a ∈ ([1, 19, 71, 109, 161, 179, 269, 271] : List ℕ),
      ∀ b ∈ ([1, 19, 71, 109, 161, 179, 269, 271] : List ℕ),
        a * b % 360 ∈ ([1, 19, 71, 109, 161, 179, 269, 271] : List ℕ)) ∧
    ([1, 19, 71, 109, 161, 179, 269, 271] : List ℕ).map (fun a => 89 * a % 360) =
      [89, 251, 199, 341, 289, 91, 181, 359] ∧
    (List.range 360).filter (fun n => n ^ 2 % 360 = 1) =
      [1, 19, 71, 89, 91, 109, 161, 179, 181, 199, 251, 269, 271, 289, 341, 359] := by
  decide

/-! ## Q to k: squares break the exponent identity -/

/-- **Korselt fails on every square rod.**  For a prime `p` and every `k ≥ 1`,
`p^(k+1) ≢ p (mod p²)`.  The identity `x^(k+1) ≡ x` used by the Q-to-k splitting holds only
on squarefree moduli. -/
theorem korselt_fails_on_square (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    ¬ p ^ (k + 1) ≡ p [MOD p ^ 2] := by
  intro h
  have h0 : p ^ (k + 1) % p ^ 2 = 0 := Nat.mod_eq_zero_of_dvd (pow_dvd_pow p (by omega))
  have h1 : p % p ^ 2 = p := Nat.mod_eq_of_lt (by nlinarith [hp.two_le])
  unfold Nat.ModEq at h
  rw [h0, h1] at h
  exact hp.ne_zero h.symm

/-- The unit count `p(p − 1)` of each square rod divides neither `144000` nor `1008000`. -/
theorem core_sq_units_not_clock :
    ∀ p ∈ core, ¬ (p * (p - 1)) ∣ 144000 ∧ ¬ (p * (p - 1)) ∣ 1008000 := by
  decide

theorem core_sq_totients :
    core.map (fun p => Nat.totient (p ^ 2)) = [110, 342, 4970, 9312, 11772] := by
  simp only [core, List.map_cons, List.map_nil]
  rw [Nat.totient_prime_pow (by norm_num) (by norm_num),
    Nat.totient_prime_pow (by norm_num) (by norm_num),
    Nat.totient_prime_pow (by norm_num) (by norm_num),
    Nat.totient_prime_pow (by norm_num) (by norm_num),
    Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num

/-! ## Tetration towers on the core rods -/

lemma tower_ge_base (p : ℕ) (hp : 1 ≤ p) (j : ℕ) (hj : 1 ≤ j) : p ≤ TowerFold.tower p j := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [TowerFold.tower_succ]
  have : 1 ≤ TowerFold.tower p i := by
    induction i with
    | zero => simp
    | succ i _ => rw [TowerFold.tower_succ]; exact Nat.one_le_pow _ _ hp
  calc p = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ TowerFold.tower p i := Nat.pow_le_pow_right hp this

/-- **A tower annihilates its own square rod.**  For `p ≥ 2` and height `k ≥ 2`,
`p ↑↑ k ≡ 0 (mod p²)`. -/
theorem tower_self_on_square (p k : ℕ) (hp : 2 ≤ p) (hk : 2 ≤ k) :
    TowerFold.tower p k % p ^ 2 = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [TowerFold.tower_succ]
  apply Nat.mod_eq_zero_of_dvd
  exact pow_dvd_pow p (le_trans hp (tower_ge_base p (by omega) j (by omega)))

/-! ## `n = p q` on the circle -/

/-- **A semiprime on the circle.**  For distinct primes `p, q`, the circle `x² + y² = p q` has
`4 (1 + χ₄(p)) (1 + χ₄(q))` square-grid points and the circle `a² − ab + b² = p q` has
`6 (1 + χ₃(p)) (1 + χ₃(q))` hexagonal points.  So `n = p q` shows 16 square-grid points exactly
when both factors are `≡ 1 (mod 4)`, and 24 hexagonal points exactly when both are
`≡ 1 (mod 3)`. -/
theorem semiprime_circle (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (r2 (p * q) : ℤ) = 4 * (1 + chi4 p) * (1 + chi4 q) ∧
    (rHex (p * q) : ℤ) = 6 * (1 + chi3 p) * (1 + chi3 q) := by
  have hpq' : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 h)
  have hq1 : ¬ q ∣ 1 := fun h => hq.one_lt.ne' (Nat.dvd_one.1 h)
  have a := r2_scale q 1 1 hq hq1 one_ne_zero
  have b := r2_scale p q 1 hp hpq' hq.ne_zero
  have c := rHex_scale q 1 1 hq hq1 one_ne_zero
  have d := rHex_scale p q 1 hp hpq' hq.ne_zero
  simp only [pow_one, mul_one, Finset.sum_range_succ, Finset.sum_range_zero, pow_zero,
    zero_add] at a b c d
  have r1 : (r2 1 : ℤ) = 4 := by exact_mod_cast r2_one
  have h1 : (rHex 1 : ℤ) = 6 := by exact_mod_cast rHex_one
  rw [r1] at a; rw [h1] at c
  refine ⟨?_, ?_⟩
  · rw [b, a]; ring
  · rw [d, c]; ring

/-- The pair `97 · 109 = 10573`: 16 square-grid and 24 hexagonal points.  Two essentially
different representations `78² + 67² = 102² + 13² = 10573` (from `(9+4i)(10±3i)`) reveal the
factor: `gcd(78·102 + 67·13, 10573) = 97`. -/
theorem pair_97_109 :
    r2 (97 * 109) = 16 ∧ rHex (97 * 109) = 24 ∧
    78 ^ 2 + 67 ^ 2 = 97 * 109 ∧ 102 ^ 2 + 13 ^ 2 = 97 * 109 ∧
    Nat.gcd (78 * 102 + 67 * 13) (97 * 109) = 97 := by
  have h := semiprime_circle 97 109 (by norm_num) (by norm_num) (by norm_num)
  have c4a : chi4 97 = 1 := by decide
  have c4b : chi4 109 = 1 := by decide
  have c3a : chi3 97 = 1 := by decide
  have c3b : chi3 109 = 1 := by decide
  rw [c4a, c4b, c3a, c3b] at h
  refine ⟨by exact_mod_cast (by linarith [h.1] : (r2 (97 * 109) : ℤ) = 16),
    by exact_mod_cast (by linarith [h.2] : (rHex (97 * 109) : ℤ) = 24), by norm_num, by norm_num,
    by norm_num⟩

/-- Richness per digit: a single prime to the power `e` multiplies the points by `e + 1`, while
`e` distinct split primes multiply them by `2^e`; `e + 1 ≤ 2^e`, with equality only for
`e ≤ 1`.  So tall powers (and tetration towers) are the least rich use of digits. -/
theorem power_vs_distinct (e : ℕ) : e + 1 ≤ 2 ^ e ∧ (2 ≤ e → e + 1 < 2 ^ e) := by
  refine ⟨?_, fun he => ?_⟩
  · induction e with
    | zero => simp
    | succ e ih => rw [pow_succ]; omega
  · induction e with
    | zero => omega
    | succ e ih =>
      rcases Nat.lt_or_ge e 2 with h | h
      · interval_cases e <;> simp_all
      · have := ih h; rw [pow_succ]; omega

/-! ## Flowers: the self-similar tilings -/

/-- Among the five, only `19` is a flower number `3k² + 3k + 1` (the `k = 2` flower of life);
`11, 71, 97, 109` are not.  (The library's `hexBall_tiles` gives a self-similar flower tiling
for every flower number.) -/
theorem core_flower_numbers :
    3 * 2 ^ 2 + 3 * 2 + 1 = 19 ∧
    ∀ k : ℕ, 3 * k ^ 2 + 3 * k + 1 ≠ 11 ∧ 3 * k ^ 2 + 3 * k + 1 ≠ 71 ∧
      3 * k ^ 2 + 3 * k + 1 ≠ 97 ∧ 3 * k ^ 2 + 3 * k + 1 ≠ 109 := by
  refine ⟨by norm_num, fun k => ?_⟩
  rcases Nat.lt_or_ge k 7 with h | h
  · interval_cases k <;> decide
  · have : 147 ≤ 3 * k ^ 2 := by nlinarith
    omega

/-- **Which flowers are rich in both grids.**  The flower number `3k² + 3k + 1` is `≡ 1 (mod 12)`
exactly when `k ≡ 0` or `3 (mod 4)`; otherwise it is `≡ 7 (mod 12)`.  Every flower number is
`≡ 1 (mod 3)`.  The flowers `k = 1, 2, 5, 6, …` (`7, 19, 91, 127, …`) are `≡ 3 (mod 4)`, so each
has a prime factor `≡ 3 (mod 4)` that is inert in the square grid; only the flowers
`k = 3, 4, 7, 8, …` (`37, 61, 169, 217, …`) can be built entirely from primes that split in both
grids (`37`, `61`, `169 = 13²` are; `217 = 7·31` is not). -/
theorem flower_mod_twelve (k : ℕ) :
    (3 * k ^ 2 + 3 * k + 1) % 12 = if k % 4 = 0 ∨ k % 4 = 3 then 1 else 7 := by
  have h : (3 * k ^ 2 + 3 * k + 1) % 12 = (3 * (k % 12) ^ 2 + 3 * (k % 12) + 1) % 12 := by
    simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  have h4 : k % 4 = (k % 12) % 4 := by omega
  rw [h, h4]
  have : k % 12 < 12 := Nat.mod_lt _ (by norm_num)
  interval_cases (k % 12) <;> simp

/-- The next flower after `19` is `37 = N₃`, a prime `≡ 1 (mod 12)` that splits in both grids,
followed by `61 = N₄`, also prime and `≡ 1 (mod 12)`. -/
theorem next_flowers :
    3 * 3 ^ 2 + 3 * 3 + 1 = 37 ∧ (37 : ℕ).Prime ∧ 37 % 12 = 1 ∧
    3 * 4 ^ 2 + 3 * 4 + 1 = 61 ∧ (61 : ℕ).Prime ∧ 61 % 12 = 1 := by
  norm_num

/-! ## Q to k on the core -/

/-- **The core's own exponent.**  `p − 1` for the five is `10, 18, 70, 96, 108`; their lcm is
`30240 = 2⁵·3³·5·7 = 6·7!`.  It divides `3·1008000` but not `1008000` (the factor `3³` comes
from `108`). -/
theorem core_exponent :
    (∀ p ∈ core, (p - 1) ∣ 30240) ∧ List.foldl Nat.lcm 1 (core.map (· - 1)) = 30240 ∧
    30240 = 2 ^ 5 * 3 ^ 3 * 5 * 7 ∧ 30240 = 6 * Nat.factorial 7 ∧
    ¬ 30240 ∣ 1008000 ∧ 30240 ∣ 3 * 1008000 := by
  decide

/-- **Q to k splits every pair of core primes** with the core exponent `30240` (from the
library's `qToK_of_multiple`). -/
theorem core_pair_qToK (p q : ℕ) (hp : p ∈ core) (hq : q ∈ core) (hpq : p ≠ q) :
    ∃ a g h, LatticeCalc.Verified.OrderSplit.qToK (p * q) a 30240 [2, 3, 5, 7] =
        some (g, h, Nat.lcm (p - 1) (q - 1)) ∧ ((g = p ∧ h = q) ∨ (g = q ∧ h = p)) := by
  refine LatticeCalc.Verified.OrderSplit.qToK_of_multiple _ (core_prime p hp) (core_prime q hq)
    hpq (core_exponent.1 p hp) (core_exponent.1 q hq) (by norm_num) ?_
  intro r hr hdvd
  have h30 : (30240 : ℕ) = 2 ^ 5 * 3 ^ 3 * 5 * 7 := by norm_num
  rw [h30] at hdvd
  have hr2 := hr.two_le
  have : r ∣ 2 ∨ r ∣ 3 ∨ r ∣ 5 ∨ r ∣ 7 := by
    rcases (Nat.Prime.dvd_mul hr).1 hdvd with h | h
    · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
        · exact Or.inl (hr.dvd_of_dvd_pow h)
        · exact Or.inr (Or.inl (hr.dvd_of_dvd_pow h))
      · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have h2 : r ≤ 7 := by
    rcases this with h | h | h | h <;> exact le_trans (Nat.le_of_dvd (by norm_num) h) (by norm_num)
  interval_cases r <;> simp_all

/-- **The whole core radical splits into the five primes** by recursive order splitting, both
with the core exponent `30240` and with the clock exponent `144000` (kernel-checked runs). -/
theorem core_radical_splits :
    (LatticeCalc.Verified.OrderSplit.splitTree 30240 [2, 3, 5, 7] [2, 3] 10 coreRadical).isPerm
        core = true ∧
    (LatticeCalc.Verified.OrderSplit.splitTree 144000 [2, 3, 5] [2, 3] 10 coreRadical).isPerm
        core = true := by
  refine ⟨by decide +kernel, by decide +kernel⟩

end CorePrimes
