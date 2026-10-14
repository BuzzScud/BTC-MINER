module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Push

/-!
# Circles on the rods: the geometry that inert primes carry

The earlier scaling law (`CorePrimes`) counts exact points of the *integer* lattice on a circle.
There an inert prime (for the square grid: `p ≡ 3 (mod 4)`; for the hexagonal / flower grid:
`p ≡ 2 (mod 3)`) adds nothing.  Here the same two circles are drawn *on a rod*, i.e. over the
residues modulo `p`, and the roles reverse.

* `conic_card_add` — over any finite field of odd characteristic and any `c ≠ 0`,
  `#{x² + c y² = 1} + #{t : c t² = −1} = q + 1`.  So such a circle has `q − 1` or `q + 1` points.
* `sqCircle_card_of_mod_four_eq_one`, `sqCircle_card_of_mod_four_eq_three` — the square circle
  `x² + y² = 1` modulo an odd prime `p` has `p − 1` points when `p` splits and `p + 1` when `p` is
  inert.
* `hexCircle_card_of_mod_three_eq_one`, `hexCircle_card_of_mod_three_eq_two` — the hexagonal
  (flower) circle `x² + x y + y² = 1` modulo a prime `p > 3` has `p − 1` points when `p` splits and
  `p + 1` when `p` is inert.  (Fully general; the `p ≡ 1` case uses an element of order 3.)
* `formPts_card_mul` — across coprime rods the counts multiply (Chinese remainder theorem), for
  every binary quadratic form.
* `flower_prime_divisor` — every prime factor of a flower number `3k² + 3k + 1` is `≡ 1 (mod 3)`;
  so `11` and `71` (indeed every prime `≡ 2 mod 3`) never divide a flower number.
* `flower_prime_hexCircle` — if the flower number `N = 3k² + 3k + 1` is prime, the hexagonal circle
  modulo `N` has exactly `N − 1 = 6·(1 + 2 + ⋯ + k)` points: one for each non-central cell of the
  flower.  For `k = 2` this is `19` and `18`.
* `core_rod_circles`, `core_modulus_circles` — the table for `11, 19, 71, 97, 109` and for their
  product.
-/

@[expose] public section

namespace RodCircles

open Finset

/-! ## A conic over a finite field -/

section Field

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The points of `x² + c y² = 1`. -/
def conic (c : F) : Finset (F × F) := univ.filter (fun p => p.1 ^ 2 + c * p.2 ^ 2 = 1)

/-- The parameters at which the stereographic projection of `x² + c y² = 1` breaks down. -/
def isoRoots (c : F) : Finset F := univ.filter (fun t => c * t ^ 2 = -1)

/-- Stereographic projection from `(−1, 0)`: the points of `x² + c y² = 1` other than `(−1, 0)`
correspond to the slopes `t` with `c t² ≠ −1`. -/
theorem conic_card_add (c : F) (hc : c ≠ 0) (h2 : (2 : F) ≠ 0) :
    (conic c).card + (isoRoots c).card = Fintype.card F + 1 := by
  have hmem : ((-1 : F), (0 : F)) ∈ conic c := by simp [conic]
  have hsplit := Finset.card_erase_add_one hmem
  have hx_of : ∀ x y : F, ¬(x = -1 ∧ y = 0) → x ^ 2 + c * y ^ 2 = 1 → 1 + x ≠ 0 := by
    intro x y hne hxy hx
    have : x = -1 := by linear_combination hx
    subst this
    have : c * y ^ 2 = 0 := by linear_combination hxy
    have hy : y = 0 := by simpa [hc] using this
    exact hne ⟨rfl, hy⟩
  have hD : ∀ t : F, ¬ c * t ^ 2 = -1 → 1 + c * t ^ 2 ≠ 0 := by
    intro t ht h; exact ht (by linear_combination h)
  have hbij : ((conic c).erase (-1, 0)).card =
      (univ.filter (fun t : F => ¬ c * t ^ 2 = -1)).card := by
    apply Finset.card_nbij' (fun p => p.2 / (1 + p.1))
      (fun t => ((1 - c * t ^ 2) / (1 + c * t ^ 2), 2 * t / (1 + c * t ^ 2)))
    · rintro ⟨x, y⟩ h
      simp only [conic, Finset.mem_coe, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
        true_and, ne_eq, Prod.mk.injEq] at h ⊢
      obtain ⟨hne, hxy⟩ := h
      have hx := hx_of x y hne hxy
      intro h
      field_simp at h
      have : 2 * (1 + x) = 0 := by linear_combination h - hxy
      rcases mul_eq_zero.1 this with h' | h'
      · exact h2 h'
      · exact hx h'
    · intro t ht
      simp only [conic, Finset.mem_coe, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
        true_and, ne_eq, Prod.mk.injEq] at ht ⊢
      have hd := hD t ht
      refine ⟨?_, ?_⟩
      · rintro ⟨h, -⟩
        field_simp at h
        apply h2; linear_combination h
      · field_simp; ring
    · rintro ⟨x, y⟩ h
      simp only [conic, Finset.mem_coe, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
        true_and, ne_eq, Prod.mk.injEq] at h ⊢
      obtain ⟨hne, hxy⟩ := h
      have hx := hx_of x y hne hxy
      have hcy : c * y ^ 2 = (1 - x) * (1 + x) := by linear_combination hxy
      have hden : 1 + c * (y / (1 + x)) ^ 2 = 2 / (1 + x) := by
        field_simp; linear_combination hcy
      rw [hden]
      constructor
      · field_simp; linear_combination (-1) * hxy
      · field_simp
    · intro t ht
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      have hd := hD t ht
      have hsum : 1 + (1 - c * t ^ 2) / (1 + c * t ^ 2) = 2 / (1 + c * t ^ 2) := by
        field_simp; ring
      simp only
      rw [hsum, div_div_div_cancel_right₀ hd, mul_div_cancel_left₀ _ h2]
  have hfilt := Finset.card_filter_add_card_filter_not (s := (univ : Finset F))
    (fun t : F => c * t ^ 2 = -1)
  simp only [Finset.card_univ] at hfilt
  unfold isoRoots
  omega

/-- If `c t₀² = −1` has a solution, it has exactly the two solutions `± t₀`. -/
theorem isoRoots_eq_pair (c t₀ : F) (h2 : (2 : F) ≠ 0) (ht : c * t₀ ^ 2 = -1) :
    (isoRoots c).card = 2 := by
  have hc : c ≠ 0 := by rintro rfl; simp at ht
  have ht0 : t₀ ≠ 0 := by rintro rfl; simp at ht
  have hne : t₀ ≠ -t₀ := by
    intro h; apply ht0
    have : 2 * t₀ = 0 := by linear_combination h
    simpa [h2] using this
  have : isoRoots c = {t₀, -t₀} := by
    ext t
    simp only [isoRoots, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      have : t ^ 2 = t₀ ^ 2 := by
        apply mul_left_cancel₀ hc; rw [h, ht]
      exact sq_eq_sq_iff_eq_or_eq_neg.1 this
    · rintro (rfl | rfl)
      · exact ht
      · simpa using ht
  rw [this, Finset.card_pair hne]

theorem isoRoots_eq_zero (c : F) (h : ∀ t : F, c * t ^ 2 ≠ -1) : (isoRoots c).card = 0 := by
  simp [isoRoots, h]

/-- The points of `x² + x y + y² = 1` over a field. -/
def hexConic : Finset (F × F) := univ.filter (fun p => p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = 1)

/-- Completing the square: `x² + x y + y² = (x + y/2)² + 3 (y/2)²`. -/
theorem hexConic_card (h2 : (2 : F) ≠ 0) : (hexConic : Finset (F × F)).card = (conic (3 : F)).card := by
  apply Finset.card_nbij' (fun p => (p.1 + p.2 / 2, p.2 / 2)) (fun q => (q.1 - q.2, 2 * q.2))
  · rintro ⟨x, y⟩ h
    simp only [hexConic, conic, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
    field_simp; linear_combination 4 * h
  · rintro ⟨u, v⟩ h
    simp only [hexConic, conic, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
    linear_combination h
  · rintro ⟨x, y⟩ _
    simp only [Prod.mk.injEq]
    constructor
    · ring
    · field_simp
  · rintro ⟨u, v⟩ _
    simp only [Prod.mk.injEq]
    constructor
    · field_simp; ring
    · field_simp

end Field

/-! ## Binary quadratic forms over any finite ring, and the Chinese remainder theorem -/

/-- The points of `a x² + b x y + c y² = 1` over a finite ring `R`. -/
def formPts (R : Type*) [CommRing R] [Fintype R] [DecidableEq R] (a b c : ℤ) : Finset (R × R) :=
  univ.filter (fun p => (a : R) * p.1 ^ 2 + (b : R) * p.1 * p.2 + (c : R) * p.2 ^ 2 = 1)

/-- The square circle `x² + y² = 1` on the rod `R`. -/
abbrev sqCircle (R : Type*) [CommRing R] [Fintype R] [DecidableEq R] : Finset (R × R) :=
  formPts R 1 0 1

/-- The hexagonal (flower) circle `x² + x y + y² = 1` on the rod `R`. -/
abbrev hexCircle (R : Type*) [CommRing R] [Fintype R] [DecidableEq R] : Finset (R × R) :=
  formPts R 1 1 1

lemma form_map {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] (e : R ≃+* A × B)
    (a b c : ℤ) (x y : R) :
    (a : R) * x ^ 2 + (b : R) * x * y + (c : R) * y ^ 2 = 1 ↔
    ((a : A) * (e x).1 ^ 2 + (b : A) * (e x).1 * (e y).1 + (c : A) * (e y).1 ^ 2 = 1 ∧
     (a : B) * (e x).2 ^ 2 + (b : B) * (e x).2 * (e y).2 + (c : B) * (e y).2 ^ 2 = 1) := by
  rw [← e.injective.eq_iff]
  simp [Prod.ext_iff, map_add, map_mul, map_pow, map_intCast]

/-- **Geometry across rods multiplies.**  For coprime rods `m, n`, the points of any binary
quadratic form modulo `m n` are exactly the pairs (point mod `m`, point mod `n`). -/
theorem formPts_card_mul (m n : ℕ) [NeZero m] [NeZero n] (hmn : m.Coprime n) (a b c : ℤ) :
    haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
    (formPts (ZMod (m * n)) a b c).card =
      (formPts (ZMod m) a b c).card * (formPts (ZMod n) a b c).card := by
  haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  set e := ZMod.chineseRemainder hmn
  rw [← Finset.card_product]
  apply Finset.card_nbij' (fun p => (((e p.1).1, (e p.2).1), ((e p.1).2, (e p.2).2)))
    (fun q => (e.symm (q.1.1, q.2.1), e.symm (q.1.2, q.2.2)))
  · rintro ⟨x, y⟩ h
    simp only [formPts, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product] at h ⊢
    exact (form_map e a b c x y).1 h
  · rintro ⟨⟨x1, y1⟩, ⟨x2, y2⟩⟩ h
    simp only [formPts, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product] at h ⊢
    rw [form_map e]
    simpa using h
  · rintro ⟨x, y⟩ _
    simp
  · rintro ⟨⟨x1, y1⟩, ⟨x2, y2⟩⟩ _
    simp

/-! ## Prime rods -/

section Prime

variable (p : ℕ) [hp : Fact p.Prime]

lemma two_ne_zero_of_odd (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : (p : ℕ) ∣ 2 := by
    rw [← ZMod.natCast_eq_zero_iff]; exact_mod_cast h
  have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this
  exact hp2 this

lemma three_ne_zero_of_ne (hp3 : p ≠ 3) : (3 : ZMod p) ≠ 0 := by
  intro h
  have : (p : ℕ) ∣ 3 := by
    rw [← ZMod.natCast_eq_zero_iff]; exact_mod_cast h
  have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).1 this
  exact hp3 this

lemma sqCircle_eq_conic : sqCircle (ZMod p) = conic (1 : ZMod p) := by
  ext ⟨x, y⟩; simp [formPts, conic]

lemma hexCircle_eq_hexConic : hexCircle (ZMod p) = (hexConic : Finset (ZMod p × ZMod p)) := by
  ext ⟨x, y⟩; simp [formPts, hexConic]

/-- A root of `z² + z + 1` modulo a prime `p ≠ 3` forces `p ≡ 1 (mod 3)`. -/
theorem mod_three_of_cube_root (hp3 : p ≠ 3) (z : ZMod p) (hz : z ^ 2 + z + 1 = 0) :
    p % 3 = 1 := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hz3 : z ^ 3 = 1 := by linear_combination (z - 1) * hz
  have hz1 : z ≠ 1 := by
    rintro rfl
    apply three_ne_zero_of_ne p hp3
    linear_combination hz
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hdvd : 3 ∣ p - 1 := by
    rw [← hord]; exact orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hz0)
  have := hp.out.two_le
  omega

/-- Conversely, `p ≡ 1 (mod 3)` gives an element of order 3, hence a root of `3 t² = −1`. -/
theorem exists_iso_three (hp1 : p % 3 = 1) : ∃ t : ZMod p, 3 * t ^ 2 = -1 := by
  have hp3 : p ≠ 3 := by rintro rfl; norm_num at hp1
  have hdvd : 3 ∣ Fintype.card (ZMod p)ˣ := by
    rw [ZMod.card_units]; have := hp.out.two_le; omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 3 hdvd
  set z : ZMod p := (u : ZMod p)
  have hz3 : z ^ 3 = 1 := by
    have := pow_orderOf_eq_one u; rw [hu] at this
    simp [z, ← Units.val_pow_eq_pow_val, this]
  have hz1 : z ≠ 1 := by
    intro h
    have : u = 1 := Units.val_eq_one.1 h
    rw [this, orderOf_one] at hu; norm_num at hu
  have hq : z ^ 2 + z + 1 = 0 := by
    have : (z - 1) * (z ^ 2 + z + 1) = 0 := by linear_combination hz3
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (by linear_combination h) hz1
    · exact h
  have h3 := three_ne_zero_of_ne p hp3
  refine ⟨(2 * z + 1) / 3, ?_⟩
  field_simp
  linear_combination 4 * hq

/-- The square circle on an odd prime rod `p ≡ 1 (mod 4)` has `p − 1` points. -/
theorem sqCircle_card_of_mod_four_eq_one (hp1 : p % 4 = 1) :
    (sqCircle (ZMod p)).card = p - 1 := by
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hp1
  have h2 := two_ne_zero_of_odd p hp2
  obtain ⟨t, ht⟩ := ZMod.exists_sq_eq_neg_one_iff.2 (by omega : p % 4 ≠ 3)
  have hroots := isoRoots_eq_pair (1 : ZMod p) t h2 (by rw [ht]; ring)
  have := conic_card_add (1 : ZMod p) one_ne_zero h2
  rw [sqCircle_eq_conic]; rw [ZMod.card] at this; omega

/-- The square circle on a prime rod `p ≡ 3 (mod 4)` (inert in the square grid) has `p + 1`
points: the maximum. -/
theorem sqCircle_card_of_mod_four_eq_three (hp3 : p % 4 = 3) :
    (sqCircle (ZMod p)).card = p + 1 := by
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hp3
  have h2 := two_ne_zero_of_odd p hp2
  have hnone : ∀ t : ZMod p, (1 : ZMod p) * t ^ 2 ≠ -1 := by
    intro t ht
    have : IsSquare (-1 : ZMod p) := ⟨t, by rw [← ht]; ring⟩
    exact ZMod.exists_sq_eq_neg_one_iff.1 this hp3
  have hroots := isoRoots_eq_zero (1 : ZMod p) hnone
  have := conic_card_add (1 : ZMod p) one_ne_zero h2
  rw [sqCircle_eq_conic]; rw [ZMod.card] at this; omega

/-- The hexagonal circle on a prime rod `p ≡ 1 (mod 3)` has `p − 1` points. -/
theorem hexCircle_card_of_mod_three_eq_one (hp1 : p % 3 = 1) :
    (hexCircle (ZMod p)).card = p - 1 := by
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hp1
  have hp3 : p ≠ 3 := by rintro rfl; norm_num at hp1
  have h2 := two_ne_zero_of_odd p hp2
  obtain ⟨t, ht⟩ := exists_iso_three p hp1
  have hroots := isoRoots_eq_pair (3 : ZMod p) t h2 ht
  have := conic_card_add (3 : ZMod p) (three_ne_zero_of_ne p hp3) h2
  rw [hexCircle_eq_hexConic, hexConic_card h2]; rw [ZMod.card] at this; omega

/-- The hexagonal circle on a prime rod `p ≡ 2 (mod 3)`, `p ≠ 2` (inert in the flower grid) has
`p + 1` points: the maximum. -/
theorem hexCircle_card_of_mod_three_eq_two (hp2' : p % 3 = 2) (hp2 : p ≠ 2) :
    (hexCircle (ZMod p)).card = p + 1 := by
  have hp3 : p ≠ 3 := by rintro rfl; norm_num at hp2'
  have h2 := two_ne_zero_of_odd p hp2
  have h3 := three_ne_zero_of_ne p hp3
  have hnone : ∀ t : ZMod p, (3 : ZMod p) * t ^ 2 ≠ -1 := by
    intro t ht
    have hz : ((3 * t - 1) / 2) ^ 2 + (3 * t - 1) / 2 + 1 = 0 := by
      field_simp; linear_combination 3 * ht
    have := mod_three_of_cube_root p hp3 _ hz
    omega
  have hroots := isoRoots_eq_zero (3 : ZMod p) hnone
  have := conic_card_add (3 : ZMod p) h3 h2
  rw [hexCircle_eq_hexConic, hexConic_card h2]; rw [ZMod.card] at this; omega

end Prime

/-! ## The flower numbers -/

/-- The `k`-th flower (centred hexagonal) number. -/
def flower (k : ℕ) : ℕ := 3 * k ^ 2 + 3 * k + 1

theorem flower_mod_three (k : ℕ) : flower k % 3 = 1 := by
  unfold flower
  rw [show 3 * k ^ 2 + 3 * k + 1 = 1 + 3 * (k ^ 2 + k) by ring, Nat.add_mul_mod_self_left]

/-- **Flower divisors.**  Every prime factor of a flower number is `≡ 1 (mod 3)`.  In particular no
prime `≡ 2 (mod 3)` (such as `11` or `71`) ever divides a flower number. -/
theorem flower_prime_divisor (k p : ℕ) (hp : p.Prime) (hdvd : p ∣ flower k) : p % 3 = 1 := by
  haveI := Fact.mk hp
  have hp3 : p ≠ 3 := by
    rintro rfl
    have := (Nat.dvd_iff_mod_eq_zero).1 hdvd
    rw [flower_mod_three] at this
    exact absurd this one_ne_zero
  have hN : ((flower k : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hdvd
  have hk : (k : ZMod p) ≠ 0 := by
    intro hk
    have : ((flower k : ℕ) : ZMod p) = 1 := by
      unfold flower; push_cast; rw [hk]; ring
    rw [hN] at this; exact zero_ne_one this
  apply mod_three_of_cube_root p hp3 (((k : ZMod p) + 1) / k)
  have : (3 * (k : ZMod p) ^ 2 + 3 * k + 1) = 0 := by
    have := hN; unfold flower at this; push_cast at this; exact this
  field_simp
  linear_combination this

theorem eleven_seventyone_never_flower (k : ℕ) : ¬ 11 ∣ flower k ∧ ¬ 71 ∣ flower k := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := flower_prime_divisor k 11 (by norm_num) h; norm_num at this
  · have := flower_prime_divisor k 71 (by norm_num) h; norm_num at this

/-- **The flower on its own rod.**  If the flower number `N = 3k² + 3k + 1` is prime, its hexagonal
circle has exactly `N − 1 = 3k(k + 1)` points: as many as the flower has non-central cells. -/
theorem flower_prime_hexCircle (k : ℕ) (hN : (flower k).Prime) :
    haveI := Fact.mk hN
    (hexCircle (ZMod (flower k))).card = flower k - 1 ∧ flower k - 1 = 3 * k * (k + 1) := by
  haveI := Fact.mk hN
  refine ⟨hexCircle_card_of_mod_three_eq_one _ (flower_mod_three k), ?_⟩
  · unfold flower; rw [Nat.add_sub_cancel]; ring

theorem nineteen_flower : flower 2 = 19 ∧ flower 2 - 1 = 18 := by decide

/-! ## The five core primes and their product -/

theorem core_rod_circles :
    haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    haveI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    haveI : Fact (Nat.Prime 71) := ⟨by norm_num⟩
    haveI : Fact (Nat.Prime 97) := ⟨by norm_num⟩
    haveI : Fact (Nat.Prime 109) := ⟨by norm_num⟩
    ((sqCircle (ZMod 11)).card, (hexCircle (ZMod 11)).card) = (12, 12) ∧
    ((sqCircle (ZMod 19)).card, (hexCircle (ZMod 19)).card) = (20, 18) ∧
    ((sqCircle (ZMod 71)).card, (hexCircle (ZMod 71)).card) = (72, 72) ∧
    ((sqCircle (ZMod 97)).card, (hexCircle (ZMod 97)).card) = (96, 96) ∧
    ((sqCircle (ZMod 109)).card, (hexCircle (ZMod 109)).card) = (108, 108) := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 71) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 97) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 109) := ⟨by norm_num⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Prod.mk.injEq]
  · exact ⟨sqCircle_card_of_mod_four_eq_three 11 (by norm_num),
      hexCircle_card_of_mod_three_eq_two 11 (by norm_num) (by norm_num)⟩
  · exact ⟨sqCircle_card_of_mod_four_eq_three 19 (by norm_num),
      hexCircle_card_of_mod_three_eq_one 19 (by norm_num)⟩
  · exact ⟨sqCircle_card_of_mod_four_eq_three 71 (by norm_num),
      hexCircle_card_of_mod_three_eq_two 71 (by norm_num) (by norm_num)⟩
  · exact ⟨sqCircle_card_of_mod_four_eq_one 97 (by norm_num),
      hexCircle_card_of_mod_three_eq_one 97 (by norm_num)⟩
  · exact ⟨sqCircle_card_of_mod_four_eq_one 109 (by norm_num),
      hexCircle_card_of_mod_three_eq_one 109 (by norm_num)⟩

/-- **Twelve-fold agreement.**  For a prime `p ≡ ±1 (mod 12)` both circles on the rod have the same
number of points, and that number is a multiple of `12`.  (For `p ≡ 1` both are `p − 1`, for
`p ≡ 11` both are `p + 1`.)  Among the core primes this covers `11, 71, 97, 109`. -/
theorem twelve_fold (p : ℕ) [Fact p.Prime] (h : p % 12 = 1 ∨ p % 12 = 11) :
    (sqCircle (ZMod p)).card = (hexCircle (ZMod p)).card ∧ 12 ∣ (sqCircle (ZMod p)).card := by
  rcases h with h | h
  · rw [sqCircle_card_of_mod_four_eq_one p (by omega),
      hexCircle_card_of_mod_three_eq_one p (by omega)]
    exact ⟨rfl, by omega⟩
  · have hp2 : p ≠ 2 := by rintro rfl; norm_num at h
    rw [sqCircle_card_of_mod_four_eq_three p (by omega),
      hexCircle_card_of_mod_three_eq_two p (by omega) hp2]
    exact ⟨rfl, by omega⟩

/-- The product of the five core rods. -/
def coreModulus : ℕ := 11 * 19 * 71 * 97 * 109

instance : NeZero coreModulus := ⟨by decide⟩

-- REPAIR CONTRACT: MUST keep the historical theorem statements and their hypotheses.
-- MUST compose the CRT cardinality theorem with the existing prime count proofs.
-- The multiplication congruences below deliberately use the same overloaded `x * y`
-- syntax as the theorem statements. Replacing these lambdas with raw `Nat.mul`
-- causes kernel definitional equality to reduce closed finite-set counts eagerly
-- (the core modulus has 156892747 residues). The local irreducibility annotation
-- alone only guides elaboration; it does not prevent that kernel reduction.
-- SHALL pass the source-bound axiom gate in ../../run_retry.py; see ../../MASTER_PLAN.md.
attribute [local irreducible] formPts

/-- Across all five rods at once: the square circle modulo `11·19·71·97·109` has
`12·20·72·96·108` points and the hexagonal circle `12·18·72·96·108`. -/
theorem core_modulus_circles (a b c : ℤ) :
    (formPts (ZMod coreModulus) a b c).card =
      (formPts (ZMod 11) a b c).card * (formPts (ZMod 19) a b c).card *
      (formPts (ZMod 71) a b c).card * (formPts (ZMod 97) a b c).card *
      (formPts (ZMod 109) a b c).card := by
  unfold coreModulus
  rw [formPts_card_mul (11 * 19 * 71 * 97) 109 (by norm_num),
    formPts_card_mul (11 * 19 * 71) 97 (by norm_num),
    formPts_card_mul (11 * 19) 71 (by norm_num),
    formPts_card_mul 11 19 (by norm_num)]

theorem core_modulus_circle_counts :
    (sqCircle (ZMod coreModulus)).card = 12 * 20 * 72 * 96 * 108 ∧
    (hexCircle (ZMod coreModulus)).card = 12 * 18 * 72 * 96 * 108 := by
  rcases core_rod_circles with ⟨h11, h19, h71, h97, h109⟩
  constructor
  · exact (core_modulus_circles 1 0 1).trans
      (congrArg₂ (fun x y : ℕ => x * y)
        (congrArg₂ (fun x y : ℕ => x * y)
          (congrArg₂ (fun x y : ℕ => x * y)
            (congrArg₂ (fun x y : ℕ => x * y) (congrArg Prod.fst h11) (congrArg Prod.fst h19))
            (congrArg Prod.fst h71))
          (congrArg Prod.fst h97))
        (congrArg Prod.fst h109))
  · exact (core_modulus_circles 1 1 1).trans
      (congrArg₂ (fun x y : ℕ => x * y)
        (congrArg₂ (fun x y : ℕ => x * y)
          (congrArg₂ (fun x y : ℕ => x * y)
            (congrArg₂ (fun x y : ℕ => x * y) (congrArg Prod.snd h11) (congrArg Prod.snd h19))
            (congrArg Prod.snd h71))
          (congrArg Prod.snd h97))
        (congrArg Prod.snd h109))

/-- Which rod circles fit the `360` dial: `12, 20, 72, 18` divide `360`; `96, 108` do not. -/
theorem rod_circles_on_dial :
    12 ∣ 360 ∧ 20 ∣ 360 ∧ 72 ∣ 360 ∧ 18 ∣ 360 ∧ ¬ 96 ∣ 360 ∧ ¬ 108 ∣ 360 := by decide

end RodCircles
