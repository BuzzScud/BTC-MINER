module

public import Mathlib

/-!
# Which semi-major axis does the direct PQ ellipse chart intend? (XP-DT-016 / BG-014)

`CROSS_PROJECT_CLAIM_LEDGER.tsv` (XP-DT-016) and `THESIS.md` (formula ledger, Ch. 11) state the
direct PQ ellipse chart as

  `a = (q+1)/2`,  `b = √((q² − p²)/4)`,  `e = √(1 − b²/a²)`.

The earlier audit flagged `a = (q+1)/2` as a probable typo, with two candidate intended formulas:
reading **A** `a = q/2` and reading **B** `a = (p+q)/2`.  This file settles the question.

* **Reading A is the only consistent one.**
  - `readingA_focal`: `(q/2)² − b² = (p/2)²`, so the focal half-distance is exactly `p/2`:
    the chart is the "string" ellipse with major axis `q` and foci `p` apart, and
    `readingA_ecc`: the eccentricity is exactly `p/q`.
  - `focal_linear_iff`: among all semi-major axes `a = α·p + q/2` (all of which give a circle
    at `p = 0`, as A and B both do), the focal distance `√(a² − b²)` is a linear expression in
    `p, q` **only** for `α = 0`, i.e. reading A.
* **Reading B does not fit the given `b`.**  `readingB_focal`: its focal distance squared is
  `p(p+q)/2`, and `readingB_eccSq`: `e² = 2p/(p+q)`.  (Reading B would pair naturally with
  `b = √(pq)`, not with the stated `b`.)  `readingB_ecc_ne_ratio`: its eccentricity is never
  `p/q` for `0 < p < q`.
* **The literal formula is not a function of the ratio `p/q`.**  `literal_focal`: its focal
  distance squared is `(p/2)² + (2q+1)/4`, so it is *never* a circle (`literal_never_circle`), and
  `literal_not_scale_invariant`: the pairs `(1,3)` and `(2,6)` have the same ratio but different
  eccentricities.  This conflicts with the ratio-band classification of XP-DT-015.
  `literal_is_ceil`: for odd `q` (every odd prime), `(q+1)/2 = ⌈q/2⌉`, which is the most likely
  origin of the typo (integer rounding of `q/2`).
* **Emergent relationship with the geometric-mean chart (XP-DT-014).**  With
  `R_a = M p/√(pq)`, `R_b = M q/√(pq)` the axis ratio of the geometric-mean chart is `p/q`.
  `charts_complementary`: under reading A the direct chart's eccentricity equals the
  geometric-mean chart's axis ratio, and the direct chart's axis ratio squared equals the
  geometric-mean chart's eccentricity squared.  The two PQ charts are therefore the same data
  with the roles of "shape" and "eccentricity" swapped — but only under reading A.
* **Twin primes.**  `twin_semiMinorSq`: for `q = p + 2`, `b² = p + 1` (whatever the reading of `a`);
  `prime_succ_square`: if `p` is prime and `p + 1` is a perfect square then `p = 3`, so the
  semi-minor axis of a twin pair is an integer only for `(3, 5)`.
-/

@[expose] public section

namespace PQEllipse

open Real

/-- The stated semi-minor axis squared, `b² = (q² − p²)/4`. -/
noncomputable def semiMinorSq (p q : ℝ) : ℝ := (q ^ 2 - p ^ 2) / 4

/-- Squared eccentricity of an ellipse with semi-major `a` and semi-minor squared `bSq`. -/
noncomputable def eccSq (a bSq : ℝ) : ℝ := 1 - bSq / a ^ 2

/-! ### Reading A: `a = q/2` -/

theorem readingA_focal (p q : ℝ) : (q / 2) ^ 2 - semiMinorSq p q = (p / 2) ^ 2 := by
  unfold semiMinorSq; ring

theorem readingA_eccSq (p q : ℝ) (hq : q ≠ 0) :
    eccSq (q / 2) (semiMinorSq p q) = (p / q) ^ 2 := by
  unfold eccSq semiMinorSq; field_simp; ring

/-- Under reading A the eccentricity is exactly `p/q`. -/
theorem readingA_ecc (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) :
    √(eccSq (q / 2) (semiMinorSq p q)) = p / q := by
  rw [readingA_eccSq p q hq.ne', sqrt_sq (div_nonneg hp hq.le)]

/-- Among semi-major axes `α p + q/2`, the focal distance is a linear form in `p, q`
exactly when `α = 0` (reading A). -/
theorem focal_linear_iff (α : ℝ) :
    (∃ l m : ℝ, ∀ p q : ℝ, (α * p + q / 2) ^ 2 - semiMinorSq p q = (l * p + m * q) ^ 2) ↔
      α = 0 := by
  constructor
  · rintro ⟨l, m, h⟩
    have h01 := h 0 1
    have h10 := h 1 0
    have h11 := h 1 1
    unfold semiMinorSq at h01 h10 h11
    have hm : m = 0 := by nlinarith
    subst hm
    nlinarith
  · rintro rfl
    exact ⟨1 / 2, 0, fun p q => by unfold semiMinorSq; ring⟩

/-! ### Reading B: `a = (p+q)/2` -/

theorem readingB_focal (p q : ℝ) :
    ((p + q) / 2) ^ 2 - semiMinorSq p q = p * (p + q) / 2 := by
  unfold semiMinorSq; ring

theorem readingB_eccSq (p q : ℝ) (h : p + q ≠ 0) :
    eccSq ((p + q) / 2) (semiMinorSq p q) = 2 * p / (p + q) := by
  unfold eccSq semiMinorSq; field_simp; ring

/-- Reading B never has eccentricity `p/q` strictly between the degenerate cases. -/
theorem readingB_ecc_ne_ratio (p q : ℝ) (hp : 0 < p) (hpq : p < q) :
    eccSq ((p + q) / 2) (semiMinorSq p q) ≠ (p / q) ^ 2 := by
  rw [readingB_eccSq p q (by linarith)]
  intro h
  have hq : 0 < q := by linarith
  field_simp at h
  nlinarith [mul_pos hp hq, mul_pos hp (sub_pos.2 hpq), mul_pos (mul_pos hp hq) (sub_pos.2 hpq)]

/-! ### The literal formula `a = (q+1)/2` -/

theorem literal_focal (p q : ℝ) :
    ((q + 1) / 2) ^ 2 - semiMinorSq p q = (p / 2) ^ 2 + (2 * q + 1) / 4 := by
  unfold semiMinorSq; ring

/-- The literal chart is never a circle (for `q ≥ 0`), even when `p = 0`. -/
theorem literal_never_circle (p q : ℝ) (hq : 0 ≤ q) :
    0 < ((q + 1) / 2) ^ 2 - semiMinorSq p q := by
  rw [literal_focal]; positivity

/-- The literal eccentricity is not a function of the ratio `p/q`:
`(1,3)` and `(2,6)` have the same ratio but different eccentricities (`1/2` vs `17/49`). -/
theorem literal_not_scale_invariant :
    eccSq ((3 + 1) / 2) (semiMinorSq 1 3) = 1 / 2 ∧
    eccSq ((6 + 1) / 2) (semiMinorSq 2 6) = 17 / 49 := by
  unfold eccSq semiMinorSq; constructor <;> norm_num

/-- For odd `q`, `(q+1)/2 = ⌈q/2⌉`: the literal formula is `q/2` rounded up. -/
theorem literal_is_ceil (q : ℤ) (hq : Odd q) :
    (((q : ℝ) + 1) / 2) = (⌈(q : ℝ) / 2⌉ : ℝ) := by
  obtain ⟨k, rfl⟩ := hq
  have hc : ⌈((2 * k + 1 : ℤ) : ℝ) / 2⌉ = k + 1 := by
    rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
  rw [hc]; push_cast; ring

/-! ### Relationship with the geometric-mean chart (XP-DT-014) -/

/-- Under reading A, the direct chart and the geometric-mean chart
`R_a = M p/√(pq)`, `R_b = M q/√(pq)` swap roles: the direct eccentricity² is the
geometric-mean axis ratio², and the direct axis ratio² is the geometric-mean eccentricity². -/
theorem charts_complementary (M p q : ℝ) (hM : M ≠ 0) (hp : 0 < p) (hq : 0 < q) :
    let Ra := M * p / √(p * q)
    let Rb := M * q / √(p * q)
    eccSq (q / 2) (semiMinorSq p q) = (Ra / Rb) ^ 2 ∧
      semiMinorSq p q / (q / 2) ^ 2 = eccSq Rb (Ra ^ 2) := by
  intro Ra Rb
  have hs : 0 < √(p * q) := sqrt_pos.2 (mul_pos hp hq)
  have hratio : Ra / Rb = p / q := by
    simp only [Ra, Rb]; field_simp
  refine ⟨by rw [hratio, readingA_eccSq p q hq.ne'], ?_⟩
  have hRb : Rb ≠ 0 := by simp only [Rb]; positivity
  unfold eccSq semiMinorSq
  rw [show Ra ^ 2 / Rb ^ 2 = (Ra / Rb) ^ 2 by ring, hratio]
  field_simp; ring

/-! ### Twin primes -/

theorem twin_semiMinorSq (p : ℝ) : semiMinorSq p (p + 2) = p + 1 := by
  unfold semiMinorSq; ring

/-- If `p` is prime and `p + 1` is a perfect square, then `p = 3`. -/
theorem prime_succ_square (p m : ℕ) (hp : p.Prime) (hm : p + 1 = m ^ 2) : p = 3 := by
  have hm2 : 2 ≤ m := by
    by_contra h
    interval_cases m <;> simp_all [Nat.Prime]
  have hfac : p = (m - 1) * (m + 1) := by
    zify [hm2, show 1 ≤ m by omega] at hm ⊢
    nlinarith
  rw [hfac] at hp
  rcases Nat.prime_mul_iff.1 hp with ⟨_, h⟩ | ⟨_, h⟩
  · omega
  · have : m = 2 := by omega
    subst this; simpa using hfac

end PQEllipse
