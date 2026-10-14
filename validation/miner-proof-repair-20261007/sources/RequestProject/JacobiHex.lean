module

public import Mathlib
public import RequestProject.DivisorRecursion
public import RequestProject.EisensteinInt

/-!
# The flower-lattice circle count for every `n`, and twelve-point circles for every prime

`LatticePatterns.rHex_formula` checked `#{(a, b) : a² − ab + b² = n} = 6 · Σ_{d ∣ n} χ₃(d)` for
`1 ≤ n ≤ 100` only, and `FlowerOfLife.twelve_points` checked the twelve-point circles for the five
primes `7, 19, 37, 61, 127` only.  Here both are proved in general:

* **`rHex_eq`**: for every `n ≥ 1` the flower lattice has exactly `6 · Σ_{d ∣ n} χ₃(d)` points on
  the circle `a² − ab + b² = n`;
* **`rHex_prime_one_mod_three`**: for every prime `p ≡ 1 (mod 3)` the circle `a² − ab + b² = p`
  passes through exactly **12** lattice points;
* `rHex_prime_two_mod_three`: for a prime `p ≡ 2 (mod 3)` it passes through none;
* `rHex_three`: the circle of squared radius 3 passes through 6.

**Proof.**  The same one-prime recursion as for the square grid (`JacobiTwoSquares`), now in the
Euclidean domain `ℤ[ω]` (`EisensteinInt`): for `p = 3`, `3 = −ω²(1 − ω)²` and every point of norm
divisible by 3 is a multiple of `1 − ω`; a prime `p ≡ 2 (mod 3)` stays prime (a norm
`a² − ab + b²` is never `≡ 2 (mod 3)`); a prime `p ≡ 1 (mod 3)` splits as `π π̄` with `π, π̄`
non-associate primes (an element of order 3 mod `p` gives `r` with `p ∣ r² − r + 1`).
-/

@[expose] public section

namespace JacobiHex

open DivisorRecursion EisInt
open scoped Classical

/-- Lattice points of the flower lattice on the circle `a² − ab + b² = n`. -/
def hexCircle (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
    (fun q => q.1 ^ 2 - q.1 * q.2 + q.2 ^ 2 = n)

/-- The number of flower-lattice points on the circle `a² − ab + b² = n`. -/
def rHex (n : ℕ) : ℕ := (hexCircle n).card

lemma mem_hexCircle {n : ℕ} {q : ℤ × ℤ} :
    q ∈ hexCircle n ↔ q.1 ^ 2 - q.1 * q.2 + q.2 ^ 2 = n := by
  unfold hexCircle
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    have hn : (0 : ℤ) ≤ n := by positivity
    have ha : 3 * q.1 ^ 2 ≤ 4 * n := by nlinarith [sq_nonneg (2 * q.2 - q.1)]
    have hb : 3 * q.2 ^ 2 ≤ 4 * n := by nlinarith [sq_nonneg (2 * q.1 - q.2)]
    have h1 : |q.1| ≤ n := by
      by_contra hc; push_neg at hc
      nlinarith [sq_abs q.1, abs_nonneg q.1]
    have h2 : |q.2| ≤ n := by
      by_contra hc; push_neg at hc
      nlinarith [sq_abs q.2, abs_nonneg q.2]
    exact ⟨⟨abs_le.1 h1, abs_le.1 h2⟩, h⟩

/-- Pairs as Eisenstein integers. -/
def toE : ℤ × ℤ ↪ EisInt := ⟨fun q => ⟨q.1, q.2⟩, fun a b h => by
  simp only [EisInt.mk.injEq] at h; exact Prod.ext h.1 h.2⟩

/-- Eisenstein integers of norm `n`. -/
def eset (n : ℕ) : Finset EisInt := (hexCircle n).map toE

lemma mem_eset {n : ℕ} {z : EisInt} : z ∈ eset n ↔ z.norm = n := by
  unfold eset
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [mem_hexCircle] at hq
    simpa [toE, EisInt.norm] using hq
  · intro h
    refine ⟨(z.re, z.im), ?_, by simp [toE]⟩
    rw [mem_hexCircle]; exact h

lemma card_eset (n : ℕ) : (eset n).card = rHex n := Finset.card_map _

lemma card_filter_dvd (π : EisInt) {k : ℕ} (hk : π.norm = k) (hk0 : k ≠ 0) (m : ℕ) :
    ((eset (k * m)).filter (fun z => π ∣ z)).card = (eset m).card := by
  have hπ : π ≠ 0 := by
    rintro rfl; simp [EisInt.norm] at hk; exact hk0 (by exact_mod_cast hk.symm)
  have hset : (eset (k * m)).filter (fun z => π ∣ z) = (eset m).image (fun w => π * w) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_image, mem_eset]
    constructor
    · rintro ⟨hz, w, rfl⟩
      refine ⟨w, ?_, rfl⟩
      rw [EisInt.norm_mul, hk] at hz
      have hk' : (k : ℤ) ≠ 0 := by exact_mod_cast hk0
      push_cast at hz
      exact mul_left_cancel₀ hk' hz
    · rintro ⟨w, hw, rfl⟩
      exact ⟨by rw [EisInt.norm_mul, hk, hw]; push_cast; ring, dvd_mul_right _ _⟩
  rw [hset, Finset.card_image_of_injective _ (mul_right_injective₀ hπ)]

lemma natCast_eq (n : ℕ) : (n : EisInt) = ⟨n, 0⟩ := by ext <;> simp

lemma norm_natCast (p : ℕ) : ((p : EisInt)).norm = ((p * p : ℕ) : ℤ) := by
  rw [natCast_eq]; simp [EisInt.norm]; ring

lemma natCast_norm (z : EisInt) {n : ℕ} (h : z.norm = n) : ((n : EisInt)) = z * star z := by
  rw [mul_star, h, natCast_eq]

lemma dvd_star_iff {a z : EisInt} : a ∣ star z ↔ star a ∣ z := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨star c, ?_⟩
    have := congrArg star hc
    rw [star_star', star_mul'] at this
    exact this
  · rintro ⟨c, rfl⟩; exact ⟨star c, by rw [star_mul', star_star']⟩

/-- A norm `a² − ab + b²` is never `≡ 2 (mod 3)`. -/
lemma norm_mod_three (z : EisInt) : z.norm % 3 ≠ 2 := by
  unfold EisInt.norm
  have h1 := Int.emod_emod_of_dvd z.re (show (3 : ℤ) ∣ 3 from dvd_refl _)
  rcases (show z.re % 3 = 0 ∨ z.re % 3 = 1 ∨ z.re % 3 = 2 by omega) with h | h | h <;>
  rcases (show z.im % 3 = 0 ∨ z.im % 3 = 1 ∨ z.im % 3 = 2 by omega) with h' | h' | h' <;>
  simp [pow_two, Int.sub_emod, Int.add_emod, Int.mul_emod, h, h']

lemma exists_dvd_of_multiple {p : ℕ} (hp : p.Prime) (z : EisInt) (w : EisInt)
    (hz : z.norm = ((p * p : ℕ) : ℤ) * w.norm) (m : ℕ) (hm : z.norm = ((p * m : ℕ) : ℤ)) :
    p ∣ m := by
  have hw0 := norm_nonneg w
  have : (p : ℤ) * (p * w.norm) = p * m := by push_cast at hz hm; linarith
  have h2 : (p : ℤ) * w.norm = m := mul_left_cancel₀ (by exact_mod_cast hp.ne_zero) this
  refine ⟨w.norm.toNat, ?_⟩
  have e : ((w.norm.toNat : ℕ) : ℤ) = w.norm := Int.toNat_of_nonneg hw0
  have : (m : ℤ) = ((p * w.norm.toNat : ℕ) : ℤ) := by push_cast; rw [e]; exact h2.symm
  exact_mod_cast this

/-! ## The prime cases -/

lemma rec_three (m : ℕ) : rHex (3 * m) = rHex m := by
  set l : EisInt := ⟨1, -1⟩
  have hl : l.norm = (3 : ℕ) := by simp [l, EisInt.norm]
  have hall : (eset (3 * m)).filter (fun z => l ∣ z) = eset (3 * m) := by
    apply Finset.filter_true_of_mem
    intro z hz
    rw [mem_eset] at hz
    unfold EisInt.norm at hz
    have h3 : (z.re + z.im) % 3 = 0 := by
      have : (z.re ^ 2 - z.re * z.im + z.im ^ 2) % 3 = 0 := by rw [hz]; push_cast; omega
      rcases (show z.re % 3 = 0 ∨ z.re % 3 = 1 ∨ z.re % 3 = 2 by omega) with h | h | h <;>
      rcases (show z.im % 3 = 0 ∨ z.im % 3 = 1 ∨ z.im % 3 = 2 by omega) with h' | h' | h' <;>
      simp [pow_two, Int.sub_emod, Int.add_emod, Int.mul_emod, h, h'] at this ⊢
    refine ⟨⟨(2 * z.re - z.im) / 3, (z.re + z.im) / 3⟩, ?_⟩
    ext <;> simp [l] <;> omega
  rw [← card_eset, ← card_eset, ← hall, card_filter_dvd l hl (by norm_num) m]

lemma prime_of_two_mod_three {p : ℕ} (hp : p.Prime) (h2 : p % 3 = 2) : Prime (p : EisInt) := by
  apply Irreducible.prime
  refine ⟨?_, ?_⟩
  · rw [isUnit_iff_norm_one, norm_natCast]
    have := hp.two_le
    intro h; have : p * p = 1 := by exact_mod_cast h
    nlinarith
  · intro x y hxy
    have hn := congrArg EisInt.norm hxy
    rw [EisInt.norm_mul, norm_natCast] at hn
    have hx0 := norm_nonneg x
    have hy0 := norm_nonneg y
    have hn' : x.norm.natAbs * y.norm.natAbs = p * p := by
      have := congrArg Int.natAbs hn
      rw [Int.natAbs_mul] at this; simpa using this.symm
    rw [isUnit_iff_norm_one, isUnit_iff_norm_one]
    have hdvd : x.norm.natAbs ∣ p * p := Dvd.intro _ hn'
    rcases (Nat.dvd_prime_pow hp).1 (show x.norm.natAbs ∣ p ^ 2 by simpa [pow_two] using hdvd) with
      ⟨i, hi, hxi⟩
    interval_cases i
    · left; simp at hxi; omega
    · exfalso
      simp at hxi
      have : x.norm = p := by omega
      exact norm_mod_three x (by rw [this]; omega)
    · right
      have : x.norm.natAbs = p * p := by rw [hxi]; ring
      have hp0 : 0 < p * p := Nat.mul_pos hp.pos hp.pos
      have : y.norm.natAbs = 1 := by
        rw [this] at hn'
        exact (Nat.mul_eq_left hp0.ne').1 hn'
      omega

lemma rec_two_mod_three {p : ℕ} (hp : p.Prime) (h2 : p % 3 = 2) (m : ℕ) :
    (rHex (p * m) : ℤ) = if p ∣ m then (rHex (m / p) : ℤ) else 0 := by
  have hpr := prime_of_two_mod_three hp h2
  have hall : ∀ z ∈ eset (p * m), (p : EisInt) ∣ z := by
    intro z hz
    rw [mem_eset] at hz
    have hd : (p : EisInt) ∣ z * star z := by
      rw [← natCast_norm z hz]; push_cast; exact dvd_mul_right _ _
    rcases hpr.dvd_or_dvd hd with h | h
    · exact h
    · rw [dvd_star_iff] at h
      have : star (p : EisInt) = p := by rw [natCast_eq]; ext <;> simp
      rwa [this] at h
  split_ifs with hpm
  · obtain ⟨k, rfl⟩ := hpm
    rw [Nat.mul_div_cancel_left k hp.pos, ← card_eset, ← card_eset, ← mul_assoc]
    have hfil : (eset (p * p * k)).filter (fun z => (p : EisInt) ∣ z) = eset (p * p * k) :=
      Finset.filter_true_of_mem (fun z hz => hall z (by rwa [mul_assoc] at hz))
    rw [← hfil, card_filter_dvd (p : EisInt) (norm_natCast p)
      (mul_ne_zero hp.ne_zero hp.ne_zero) k]
  · have : eset (p * m) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro z hz
      obtain ⟨w, rfl⟩ := hall z hz
      rw [mem_eset] at hz
      exact hpm (exists_dvd_of_multiple hp ((p : EisInt) * w) w (by rw [EisInt.norm_mul, norm_natCast]) m hz)
    rw [← card_eset, this]; rfl

/-- For `p ≡ 1 (mod 3)` there is an `r` with `p ∣ r² − r + 1`. -/
lemma exists_root {p : ℕ} (hp : p.Prime) (h1 : p % 3 = 1) :
    ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - r + 1 := by
  haveI := Fact.mk hp
  have hcard : 3 ∣ Fintype.card (ZMod p)ˣ := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hp]; omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 3 hcard
  have hg3 : (g : ZMod p) ^ 3 = 1 := by
    have := pow_orderOf_eq_one g; rw [hg] at this
    have := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) this
    simpa using this
  have hg1 : (g : ZMod p) ≠ 1 := by
    intro h
    have : g = 1 := Units.ext h
    rw [this, orderOf_one] at hg; norm_num at hg
  have hq : (g : ZMod p) ^ 2 + g + 1 = 0 := by
    have : ((g : ZMod p) - 1) * ((g : ZMod p) ^ 2 + g + 1) = 0 := by
      linear_combination hg3
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hg1
    · exact h
  refine ⟨((-(g : ZMod p)).val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val]
  linear_combination hq

lemma rec_one_mod_three {p : ℕ} (hp : p.Prime) (h1 : p % 3 = 1) (m : ℕ) :
    (rHex (p * m) : ℤ) = 2 * rHex m - if p ∣ m then (rHex (m / p) : ℤ) else 0 := by
  -- a prime `π` of norm `p`
  obtain ⟨π, hπ⟩ : ∃ π : EisInt, π.norm = p := by
    obtain ⟨r, hr⟩ := exists_root hp h1
    set z : EisInt := ⟨r, 1⟩
    have hz : z.norm = r ^ 2 - r + 1 := by simp [z, EisInt.norm]
    have hnp : ¬ Prime (p : EisInt) := by
      intro hpr
      have hd : (p : EisInt) ∣ z * star z := by
        rw [mul_star, hz]; obtain ⟨c, hc⟩ := hr
        exact ⟨⟨c, 0⟩, by rw [hc, natCast_eq]; ext <;> simp⟩
      rcases hpr.dvd_or_dvd hd with ⟨c, hc⟩ | ⟨c, hc⟩
      · have := congrArg EisInt.im hc
        simp [z, natCast_eq] at this
        have h1' : (p : ℤ) ∣ 1 := ⟨c.im, this⟩
        have := Int.eq_one_of_dvd_one (by positivity) h1'
        exact hp.one_lt.ne' (by exact_mod_cast this)
      · have := congrArg EisInt.im hc
        simp [z, natCast_eq] at this
        have h1' : (p : ℤ) ∣ 1 := ⟨-c.im, by linarith⟩
        have := Int.eq_one_of_dvd_one (by positivity) h1'
        exact hp.one_lt.ne' (by exact_mod_cast this)
    have hni : ¬ Irreducible (p : EisInt) := fun h => hnp h.prime
    have hnu : ¬ IsUnit (p : EisInt) := by
      rw [isUnit_iff_norm_one, norm_natCast]
      have := hp.two_le
      intro h; have : p * p = 1 := by exact_mod_cast h
      nlinarith
    rw [irreducible_iff] at hni
    push_neg at hni
    obtain ⟨x, y, hxy, hx, hy⟩ := hni hnu
    rw [isUnit_iff_norm_one] at hx hy
    have hn := congrArg EisInt.norm hxy
    rw [EisInt.norm_mul, norm_natCast] at hn
    have hx0 := norm_nonneg x
    have hy0 := norm_nonneg y
    have hn' : x.norm.natAbs * y.norm.natAbs = p * p := by
      have := congrArg Int.natAbs hn
      rw [Int.natAbs_mul] at this; simpa using this.symm
    have hdvd : x.norm.natAbs ∣ p * p := Dvd.intro _ hn'
    rcases (Nat.dvd_prime_pow hp).1 (show x.norm.natAbs ∣ p ^ 2 by simpa [pow_two] using hdvd) with
      ⟨i, hi, hxi⟩
    interval_cases i
    · exfalso; simp at hxi; omega
    · exact ⟨x, by simp at hxi; omega⟩
    · exfalso
      have : x.norm.natAbs = p * p := by rw [hxi]; ring
      have hp0 : 0 < p * p := Nat.mul_pos hp.pos hp.pos
      have : y.norm.natAbs = 1 := by
        rw [this] at hn'
        exact (Nat.mul_eq_left hp0.ne').1 hn'
      omega
  have hπ' : (star π).norm = p := by rw [EisInt.norm_star, hπ]
  have hpπ : ((p : EisInt)) = π * star π := natCast_norm π hπ
  have prπ := prime_of_norm_prime hp hπ
  have prπ' := prime_of_norm_prime hp hπ'
  -- `π̄` does not divide `π`
  have hnd : ¬ star π ∣ π := by
    rintro ⟨c, hc⟩
    have hn := congrArg EisInt.norm hc
    rw [EisInt.norm_mul, hπ', hπ] at hn
    have hc1 : c.norm = 1 := by
      have : (p : ℤ) * 1 = p * c.norm := by rw [mul_one]; exact hn
      exact (mul_left_cancel₀ (by exact_mod_cast hp.ne_zero) this).symm
    unfold EisInt.norm at hc1
    have hre := congrArg EisInt.re hc
    have him := congrArg EisInt.im hc
    simp only [EisInt.mul_re, EisInt.mul_im, EisInt.star_re, EisInt.star_im] at hre him
    have hp' : π.re ^ 2 - π.re * π.im + π.im ^ 2 = p := hπ
    have hcre : c.re ^ 2 ≤ 1 := by nlinarith [sq_nonneg (2 * c.im - c.re)]
    have hcim : c.im ^ 2 ≤ 1 := by nlinarith [sq_nonneg (2 * c.re - c.im)]
    have hr1 : -1 ≤ c.re := by nlinarith
    have hr2 : c.re ≤ 1 := by nlinarith
    have hi1 : -1 ≤ c.im := by nlinarith
    have hi2 : c.im ≤ 1 := by nlinarith
    have key : π.re = 0 ∨ π.im = 0 ∨ π.re = π.im ∨ π.re = -π.im ∨ π.im = 2 * π.re ∨
        π.re = 2 * π.im := by
      interval_cases hcr : c.re <;> interval_cases hci : c.im <;> simp at hc1 <;>
        simp at hre him <;> omega
    have hsq : ∀ x : ℤ, x ^ 2 ≠ p := fun x hx => by
      have hx' : x.natAbs ^ 2 = p := by
        have : ((x.natAbs ^ 2 : ℕ) : ℤ) = p := by rw [Nat.cast_pow, Int.natCast_natAbs, sq_abs]; exact hx
        exact_mod_cast this
      have := hp.eq_one_or_self_of_dvd x.natAbs ⟨x.natAbs, by rw [← hx']; ring⟩
      rcases this with h | h
      · rw [h] at hx'; simp at hx'; exact hp.one_lt.ne hx'
      · rw [h] at hx'; nlinarith [hp.two_le]
    have h3sq : ∀ x : ℤ, 3 * x ^ 2 ≠ p := fun x hx => by
      have h3 : (3 : ℤ) ∣ p := ⟨x ^ 2, hx.symm⟩
      have h3' : 3 ∣ p := by exact_mod_cast h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3'
      omega
    rcases key with h | h | h | h | h | h <;> rw [h] at hp'
    · exact hsq π.im (by linarith)
    · exact hsq π.re (by linarith)
    · exact hsq π.im (by linarith)
    · exact h3sq π.im (by linarith)
    · exact h3sq π.re (by linarith)
    · exact h3sq π.im (by linarith)
  set S := eset (p * m)
  set A := S.filter (fun z => π ∣ z)
  set B := S.filter (fun z => star π ∣ z)
  have hunion : A ∪ B = S := by
    ext z
    simp only [A, B, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hz
      have hz' := hz
      rw [mem_eset] at hz'
      have hd : π ∣ z * star z := by
        rw [← natCast_norm z hz']; push_cast; rw [hpπ, mul_assoc]; exact dvd_mul_right _ _
      rcases prπ.dvd_or_dvd hd with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, dvd_star_iff.1 h⟩
  have hinter : A ∩ B = S.filter (fun z => (p : EisInt) ∣ z) := by
    ext z
    simp only [A, B, Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hz, ⟨w, rfl⟩⟩, _, h2⟩
      refine ⟨hz, ?_⟩
      rcases prπ'.dvd_or_dvd h2 with h | ⟨v, rfl⟩
      · exact absurd h hnd
      · exact ⟨v, by rw [hpπ]; ring⟩
    · rintro ⟨hz, ⟨w, rfl⟩⟩
      exact ⟨⟨hz, ⟨star π * w, by rw [hpπ]; ring⟩⟩, hz, ⟨π * w, by rw [hpπ]; ring⟩⟩
  have hA : A.card = rHex m := by rw [← card_eset]; exact card_filter_dvd π hπ hp.ne_zero m
  have hB : B.card = rHex m := by rw [← card_eset]; exact card_filter_dvd _ hπ' hp.ne_zero m
  have hU := Finset.card_union_add_card_inter A B
  rw [hunion, hinter, hA, hB] at hU
  have hI : ((S.filter (fun z => (p : EisInt) ∣ z)).card : ℤ) =
      if p ∣ m then (rHex (m / p) : ℤ) else 0 := by
    split_ifs with hpm
    · obtain ⟨k, rfl⟩ := hpm
      rw [Nat.mul_div_cancel_left k hp.pos, ← card_eset]
      simp only [S]
      rw [← mul_assoc, card_filter_dvd (p : EisInt) (norm_natCast p)
        (mul_ne_zero hp.ne_zero hp.ne_zero) k]
    · have : S.filter (fun z => (p : EisInt) ∣ z) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro z hz
        simp only [S, Finset.mem_filter, mem_eset] at hz
        obtain ⟨hz, w, rfl⟩ := hz
        exact hpm (exists_dvd_of_multiple hp ((p : EisInt) * w) w (by rw [EisInt.norm_mul, norm_natCast]) m hz)
      rw [this]; rfl
  have hS : (S.card : ℤ) + (S.filter (fun z => (p : EisInt) ∣ z)).card = 2 * rHex m := by
    exact_mod_cast (show S.card + _ = rHex m + rHex m from hU).trans (by ring)
  rw [← card_eset]
  linarith

/-- The unit circle of the flower lattice has 6 points. -/
lemma rHex_one : rHex 1 = 6 := by decide

/-- The one-prime recursion for `r_hex`. -/
theorem rHex_rec (p m : ℕ) (hp : p.Prime) (_hm : m ≠ 0) :
    (rHex (p * m) : ℤ) = rHex m + chi3 p * (rHex m - if p ∣ m then (rHex (m / p) : ℤ) else 0) := by
  by_cases h3 : p = 3
  · subst h3; rw [rec_three]; simp [chi3]
  · have h12 : p % 3 = 1 ∨ p % 3 = 2 := by
      have : p % 3 ≠ 0 := by
        intro h0
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero h0)
        exact h3 this.symm
      omega
    rcases h12 with h | h
    · rw [rec_one_mod_three hp h m]; simp only [chi3, h]; simp; ring
    · rw [rec_two_mod_three hp h m]; simp only [chi3, h]; simp

/-- **The flower-lattice circle count**: for every `n ≥ 1` the circle `a² − ab + b² = n` passes
through exactly `6 · Σ_{d ∣ n} χ₃(d)` points of the flower lattice. -/
theorem rHex_eq (n : ℕ) (hn : n ≠ 0) : (rHex n : ℤ) = 6 * divisorSum chi3 n :=
  eq_of_recursion chi3 chi3_mul (fun n => (rHex n : ℤ)) 6 (by simp [rHex_one, chi3])
    rHex_rec n hn

lemma divisorSum_prime (f : ℕ → ℤ) {p : ℕ} (hp : p.Prime) : divisorSum f p = f 1 + f p := by
  unfold divisorSum
  rw [Nat.Prime.divisors hp, Finset.sum_pair hp.one_lt.ne]

/-- **Twelve-point circles for every prime `p ≡ 1 (mod 3)`**: the circle `a² − ab + b² = p` passes
through exactly 12 points of the flower lattice. -/
theorem rHex_prime_one_mod_three {p : ℕ} (hp : p.Prime) (h1 : p % 3 = 1) : rHex p = 12 := by
  have := rHex_eq p hp.ne_zero
  rw [divisorSum_prime chi3 hp] at this
  simp [chi3, h1] at this
  omega

/-- For a prime `p ≡ 2 (mod 3)` the circle `a² − ab + b² = p` misses the flower lattice. -/
theorem rHex_prime_two_mod_three {p : ℕ} (hp : p.Prime) (h2 : p % 3 = 2) : rHex p = 0 := by
  have := rHex_eq p hp.ne_zero
  rw [divisorSum_prime chi3 hp] at this
  simp [chi3, h2] at this
  omega

/-- The circle of squared radius 3 passes through 6 lattice points. -/
theorem rHex_three : rHex 3 = 6 := by
  have := rHex_eq 3 (by norm_num)
  rw [divisorSum_prime chi3 Nat.prime_three] at this
  simp [chi3] at this
  omega

/-- The five shell primes of `FlowerOfLife.twelve_points` are instances. -/
example : rHex 7 = 12 ∧ rHex 19 = 12 ∧ rHex 37 = 12 ∧ rHex 61 = 12 ∧ rHex 127 = 12 :=
  ⟨rHex_prime_one_mod_three (by norm_num) (by norm_num),
    rHex_prime_one_mod_three (by norm_num) (by norm_num),
    rHex_prime_one_mod_three (by norm_num) (by norm_num),
    rHex_prime_one_mod_three (by norm_num) (by norm_num),
    rHex_prime_one_mod_three (by norm_num) (by norm_num)⟩

end JacobiHex
