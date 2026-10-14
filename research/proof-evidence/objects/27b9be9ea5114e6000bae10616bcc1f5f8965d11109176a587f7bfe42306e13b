module

public import Mathlib
public import RequestProject.DivisorRecursion

/-!
# Jacobi's two-squares formula for every `n`

`LatticePatterns.r2_formula` checked `#{(x, y) : x² + y² = n} = 4 · Σ_{d ∣ n} χ₄(d)` for
`1 ≤ n ≤ 100` only.  Here it is proved for **every** `n ≥ 1` (`r2_eq`).

**Proof.**  Count lattice points as Gaussian integers of norm `n`.  For each prime `p` the count
`R(n)` satisfies the same one-prime recursion as the divisor sum
(`DivisorRecursion.divisorSum_prime_mul`):
* `p = 2`: every Gaussian integer of even norm is a multiple of `1 + i`, so `R(2m) = R(m)`;
* `p ≡ 3 (mod 4)`: `p` stays prime in `GaussianInt`, so `p ∣ x² + y²` forces `p ∣ x, y`, and
  `R(pm) = R(m/p)` (or `0` if `p ∤ m`);
* `p ≡ 1 (mod 4)`: `p = π·π̄` with `π = a + bi` prime; a point of norm `pm` is a multiple of `π`
  or of `π̄`, both happen exactly for the multiples of `p`, so `R(pm) = 2R(m) − R(m/p)`.
Since `R(1) = 4`, the recursion forces `R = 4 · Σ χ₄` (`DivisorRecursion.eq_of_recursion`).
-/

@[expose] public section

namespace JacobiTwoSquares

open DivisorRecursion
open scoped Classical


/-- Lattice points of the square grid on the circle `x² + y² = n`. -/
def sqCircle (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter (fun q => q.1 ^ 2 + q.2 ^ 2 = n)

/-- The number of square-grid points on the circle `x² + y² = n`. -/
def r2 (n : ℕ) : ℕ := (sqCircle n).card

lemma mem_sqCircle {n : ℕ} {q : ℤ × ℤ} : q ∈ sqCircle n ↔ q.1 ^ 2 + q.2 ^ 2 = n := by
  unfold sqCircle
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    have h1 : |q.1| ≤ n := by nlinarith [abs_nonneg q.1, sq_abs q.1, sq_nonneg q.2]
    have h2 : |q.2| ≤ n := by nlinarith [abs_nonneg q.2, sq_abs q.2, sq_nonneg q.1]
    exact ⟨⟨abs_le.1 h1, abs_le.1 h2⟩, h⟩

/-- Pairs as Gaussian integers. -/
def toG : ℤ × ℤ ↪ GaussianInt := ⟨fun q => ⟨q.1, q.2⟩, fun a b h => by
  simp only [Zsqrtd.mk.injEq] at h; exact Prod.ext h.1 h.2⟩

/-- Gaussian integers of norm `n`. -/
def gset (n : ℕ) : Finset GaussianInt := (sqCircle n).map toG

lemma norm_eq (z : GaussianInt) : z.norm = z.re ^ 2 + z.im ^ 2 := by
  rw [Zsqrtd.norm_def]; ring

lemma mem_gset {n : ℕ} {z : GaussianInt} : z ∈ gset n ↔ z.norm = n := by
  unfold gset
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [mem_sqCircle] at hq
    rw [norm_eq]; simpa [toG] using hq
  · intro h
    refine ⟨(z.re, z.im), ?_, by simp [toG]⟩
    rw [mem_sqCircle]; rw [norm_eq] at h; exact h

lemma card_gset (n : ℕ) : (gset n).card = r2 n := Finset.card_map _

/-- Multiplying by `π` matches the points of norm `m` with the multiples of `π` of norm
`N(π)·m`. -/
lemma card_filter_dvd (π : GaussianInt) {k : ℕ} (hk : π.norm = k) (hk0 : k ≠ 0) (m : ℕ) :
    ((gset (k * m)).filter (fun z => π ∣ z)).card = (gset m).card := by
  classical
  have hπ : π ≠ 0 := by
    rintro rfl; simp at hk; exact hk0 (by exact_mod_cast hk.symm)
  have hset : (gset (k * m)).filter (fun z => π ∣ z) = (gset m).image (fun w => π * w) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_image, mem_gset]
    constructor
    · rintro ⟨hz, w, rfl⟩
      refine ⟨w, ?_, rfl⟩
      rw [Zsqrtd.norm_mul, hk] at hz
      have hk' : (k : ℤ) ≠ 0 := by exact_mod_cast hk0
      push_cast at hz
      exact mul_left_cancel₀ hk' hz
    · rintro ⟨w, hw, rfl⟩
      exact ⟨by rw [Zsqrtd.norm_mul, hk, hw]; push_cast; ring, dvd_mul_right _ _⟩
  rw [hset, Finset.card_image_of_injective _ (mul_right_injective₀ hπ)]

lemma norm_natCast (p : ℕ) : ((p : GaussianInt)).norm = ((p * p : ℕ) : ℤ) := by
  rw [norm_eq]; simp; ring

lemma norm_star (z : GaussianInt) : (star z).norm = z.norm := Zsqrtd.norm_conj z

lemma dvd_star_iff {a z : GaussianInt} : a ∣ star z ↔ star a ∣ z := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨star c, ?_⟩
    have := congrArg star hc
    rw [star_star, star_mul] at this
    rw [this, mul_comm]
  · rintro ⟨c, rfl⟩; exact ⟨star c, by rw [star_mul, star_star, mul_comm]⟩

/-- An element whose norm is a prime number is a prime element. -/
lemma prime_of_norm_prime {π : GaussianInt} {p : ℕ} (hp : p.Prime) (hπ : π.norm = p) : Prime π := by
  apply Irreducible.prime
  refine ⟨?_, ?_⟩
  · rw [← Zsqrtd.norm_eq_one_iff, hπ]; simpa using hp.one_lt.ne'
  · intro x y hxy
    have hn := congrArg Zsqrtd.norm hxy
    rw [Zsqrtd.norm_mul, hπ] at hn
    have hx0 := Zsqrtd.norm_nonneg (by norm_num : (-1 : ℤ) ≤ 0) x
    have hy0 := Zsqrtd.norm_nonneg (by norm_num : (-1 : ℤ) ≤ 0) y
    have hn' : x.norm.natAbs * y.norm.natAbs = p := by
      have := congrArg Int.natAbs hn
      rw [Int.natAbs_mul] at this; simpa using this.symm
    rcases (Nat.prime_mul_iff.1 (hn' ▸ hp)) with ⟨_, h1⟩ | ⟨_, h1⟩
    · right; exact Zsqrtd.norm_eq_one_iff.1 h1
    · left; exact Zsqrtd.norm_eq_one_iff.1 h1

/-- Every point of norm `n` is a lattice point `z` with `z · z̄ = n`. -/
lemma natCast_norm (z : GaussianInt) {n : ℕ} (h : z.norm = n) : ((n : GaussianInt)) = z * star z := by
  rw [← Zsqrtd.norm_eq_mul_conj, h]; rfl

/-! ## The three prime cases -/

lemma rec_two (m : ℕ) : r2 (2 * m) = r2 m := by
  classical
  set π : GaussianInt := ⟨1, 1⟩
  have hπ : π.norm = (2 : ℕ) := by rw [norm_eq]; norm_num [π]
  have hall : (gset (2 * m)).filter (fun z => π ∣ z) = gset (2 * m) := by
    apply Finset.filter_true_of_mem
    intro z hz
    rw [mem_gset, norm_eq] at hz
    have hpar : (z.re + z.im) % 2 = 0 := by
      have : (z.re ^ 2 + z.im ^ 2) % 2 = 0 := by rw [hz]; push_cast; omega
      rcases Int.emod_two_eq_zero_or_one z.re with h | h <;>
        rcases Int.emod_two_eq_zero_or_one z.im with h' | h' <;>
        simp [pow_two, Int.add_emod, Int.mul_emod, h, h'] at this ⊢
    refine ⟨⟨(z.re + z.im) / 2, (z.im - z.re) / 2⟩, ?_⟩
    apply Zsqrtd.ext <;> simp [π] <;> omega
  rw [← card_gset, ← card_gset, ← hall, card_filter_dvd π hπ (by norm_num) m]

lemma rec_three_mod_four {p : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) (m : ℕ) :
    (r2 (p * m) : ℤ) = if p ∣ m then (r2 (m / p) : ℤ) else 0 := by
  classical
  haveI := Fact.mk hp
  have hpr : Prime (p : GaussianInt) := GaussianInt.prime_of_nat_prime_of_mod_four_eq_three p h3
  have hall : ∀ z ∈ gset (p * m), (p : GaussianInt) ∣ z := by
    intro z hz
    rw [mem_gset] at hz
    have hd : (p : GaussianInt) ∣ z * star z := by
      rw [← natCast_norm z hz]; push_cast; exact dvd_mul_right _ _
    rcases hpr.dvd_or_dvd hd with h | h
    · exact h
    · rw [dvd_star_iff] at h; simpa using h
  split_ifs with hpm
  · obtain ⟨k, rfl⟩ := hpm
    rw [Nat.mul_div_cancel_left k hp.pos, ← card_gset, ← card_gset, ← mul_assoc]
    have hfil : (gset (p * p * k)).filter (fun z => (p : GaussianInt) ∣ z) = gset (p * p * k) :=
      Finset.filter_true_of_mem (fun z hz => hall z (by rwa [mul_assoc] at hz))
    rw [← hfil, card_filter_dvd (p : GaussianInt) (norm_natCast p) (mul_ne_zero hp.ne_zero hp.ne_zero) k]
  · have : gset (p * m) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro z hz
      obtain ⟨w, rfl⟩ := hall z hz
      rw [mem_gset, Zsqrtd.norm_mul, norm_natCast] at hz
      have hw0 := Zsqrtd.norm_nonneg (by norm_num : (-1 : ℤ) ≤ 0) w
      apply hpm
      have : (p : ℤ) * (p * w.norm) = p * m := by push_cast at hz; linarith
      have h2 : (p : ℤ) * w.norm = m := mul_left_cancel₀ (by exact_mod_cast hp.ne_zero) this
      refine ⟨w.norm.toNat, ?_⟩
      have e : ((w.norm.toNat : ℕ) : ℤ) = w.norm := Int.toNat_of_nonneg hw0
      have : (m : ℤ) = ((p * w.norm.toNat : ℕ) : ℤ) := by push_cast; rw [e]; exact h2.symm
      exact_mod_cast this
    rw [← card_gset, this]; rfl

lemma rec_one_mod_four {p : ℕ} (hp : p.Prime) (h1 : p % 4 = 1) (m : ℕ) :
    (r2 (p * m) : ℤ) = 2 * r2 m - if p ∣ m then (r2 (m / p) : ℤ) else 0 := by
  classical
  haveI := Fact.mk hp
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  set π : GaussianInt := ⟨a, b⟩
  have hπ : π.norm = p := by rw [norm_eq]; simp [π]; exact_mod_cast hab
  have hπ' : (star π).norm = p := by rw [norm_star, hπ]
  have hpπ : ((p : GaussianInt)) = π * star π := natCast_norm π hπ
  have prπ := prime_of_norm_prime hp hπ
  have prπ' := prime_of_norm_prime hp hπ'
  -- `π̄` does not divide `π`
  have hnd : ¬ star π ∣ π := by
    rintro ⟨c, hc⟩
    have hn := congrArg Zsqrtd.norm hc
    rw [Zsqrtd.norm_mul, hπ', hπ] at hn
    have hc1 : c.norm = 1 := by
      have : (p : ℤ) * 1 = p * c.norm := by rw [mul_one]; exact hn
      exact (mul_left_cancel₀ (by exact_mod_cast hp.ne_zero) this).symm
    rw [norm_eq] at hc1
    have hre := congrArg Zsqrtd.re hc
    have him := congrArg Zsqrtd.im hc
    simp only [π, Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star] at hre him
    have hab' : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = p := by exact_mod_cast hab
    have hcre : c.re ^ 2 ≤ 1 := by nlinarith [sq_nonneg c.im]
    have hcim : c.im ^ 2 ≤ 1 := by nlinarith [sq_nonneg c.re]
    have hr1 : -1 ≤ c.re := by nlinarith
    have hr2 : c.re ≤ 1 := by nlinarith
    have hi1 : -1 ≤ c.im := by nlinarith
    have hi2 : c.im ≤ 1 := by nlinarith
    have key : (a : ℤ) = 0 ∨ (b : ℤ) = 0 ∨ (a : ℤ) = b ∨ (a : ℤ) = -b := by
      interval_cases hcr : c.re <;> interval_cases hci : c.im <;> simp at hc1 <;>
        simp at hre him <;> omega
    have hodd : ¬ (2 ∣ p) := by
      intro h2; have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2; omega
    have hsq : ∀ x : ℕ, x ^ 2 ≠ p := fun x hx => by
      have := hp.eq_one_or_self_of_dvd x ⟨x, by rw [← hx]; ring⟩
      rcases this with rfl | rfl
      · simp at hx; exact hp.one_lt.ne hx
      · nlinarith [hp.two_le]
    rcases key with h | h | h | h
    · have : a = 0 := by exact_mod_cast h
      subst this; exact hsq b (by simpa using hab)
    · have : b = 0 := by exact_mod_cast h
      subst this; exact hsq a (by simpa using hab)
    · have : a = b := by exact_mod_cast h
      subst this; exact hodd ⟨a ^ 2, by rw [← hab]; ring⟩
    · have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      subst ha0 hb0; simp at hab; exact hp.ne_zero hab.symm
  set S := gset (p * m)
  set A := S.filter (fun z => π ∣ z)
  set B := S.filter (fun z => star π ∣ z)
  have hunion : A ∪ B = S := by
    ext z
    simp only [A, B, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hz
      have hz' := hz
      rw [mem_gset] at hz'
      have hd : π ∣ z * star z := by
        rw [← natCast_norm z hz']; push_cast; rw [hpπ, mul_assoc]; exact dvd_mul_right _ _
      rcases prπ.dvd_or_dvd hd with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, dvd_star_iff.1 h⟩
  have hinter : A ∩ B = S.filter (fun z => (p : GaussianInt) ∣ z) := by
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
  have hA : A.card = r2 m := by rw [← card_gset]; exact card_filter_dvd π hπ hp.ne_zero m
  have hB : B.card = r2 m := by rw [← card_gset]; exact card_filter_dvd _ hπ' hp.ne_zero m
  have hU := Finset.card_union_add_card_inter A B
  rw [hunion, hinter, hA, hB] at hU
  have hI : ((S.filter (fun z => (p : GaussianInt) ∣ z)).card : ℤ) =
      if p ∣ m then (r2 (m / p) : ℤ) else 0 := by
    split_ifs with hpm
    · obtain ⟨k, rfl⟩ := hpm
      rw [Nat.mul_div_cancel_left k hp.pos, ← card_gset]
      simp only [S]
      rw [← mul_assoc, card_filter_dvd (p : GaussianInt) (norm_natCast p) (mul_ne_zero hp.ne_zero hp.ne_zero) k]
    · have : S.filter (fun z => (p : GaussianInt) ∣ z) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro z hz
        simp only [S, Finset.mem_filter, mem_gset] at hz
        obtain ⟨hz, w, rfl⟩ := hz
        rw [Zsqrtd.norm_mul, norm_natCast] at hz
        have hw0 := Zsqrtd.norm_nonneg (by norm_num : (-1 : ℤ) ≤ 0) w
        apply hpm
        have : (p : ℤ) * (p * w.norm) = p * m := by push_cast at hz; linarith
        have h2 : (p : ℤ) * w.norm = m := mul_left_cancel₀ (by exact_mod_cast hp.ne_zero) this
        refine ⟨w.norm.toNat, ?_⟩
        have e : ((w.norm.toNat : ℕ) : ℤ) = w.norm := Int.toNat_of_nonneg hw0
        have : (m : ℤ) = ((p * w.norm.toNat : ℕ) : ℤ) := by push_cast; rw [e]; exact h2.symm
        exact_mod_cast this
      rw [this]; rfl
  have hS : (S.card : ℤ) + (S.filter (fun z => (p : GaussianInt) ∣ z)).card = 2 * r2 m := by
    exact_mod_cast (show S.card + _ = r2 m + r2 m from hU).trans (by ring)
  rw [← card_gset]
  linarith

/-- The unit circle has 4 points. -/
lemma r2_one : r2 1 = 4 := by decide

/-- The one-prime recursion for `r₂`, in the form of `DivisorRecursion`. -/
theorem r2_rec (p m : ℕ) (hp : p.Prime) (_hm : m ≠ 0) :
    (r2 (p * m) : ℤ) = r2 m + chi4 p * (r2 m - if p ∣ m then (r2 (m / p) : ℤ) else 0) := by
  rcases hp.eq_two_or_odd' with rfl | hodd
  · rw [rec_two]; simp [chi4]
  · have h13 : p % 4 = 1 ∨ p % 4 = 3 := by
      obtain ⟨k, hk⟩ := hodd; omega
    rcases h13 with h | h
    · rw [rec_one_mod_four hp h m]; simp only [chi4, h]; simp; ring
    · rw [rec_three_mod_four hp h m]; simp only [chi4, h]; simp

/-- **Jacobi's two-squares theorem**: for every `n ≥ 1` the circle `x² + y² = n` passes through
exactly `4 · Σ_{d ∣ n} χ₄(d)` points of the square grid. -/
theorem r2_eq (n : ℕ) (hn : n ≠ 0) : (r2 n : ℤ) = 4 * divisorSum chi4 n :=
  eq_of_recursion chi4 chi4_mul (fun n => (r2 n : ℤ)) 4 (by simp [r2_one, chi4])
    r2_rec n hn

end JacobiTwoSquares
