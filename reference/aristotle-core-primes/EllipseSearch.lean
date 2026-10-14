module

public import Mathlib
public import RequestProject.PQEllipse

/-!
# The pq ellipse as a search-space reducer

Throughout, the pq ellipse is the corrected chart of `PQEllipse`: semi-major axis `a = q/2`,
focal half-distance `c = p/2`, `b² = (q² − p²)/4`, eccentricity `e = p/q`.

**The scalar oscillation.**  Measured from a focus, the distance to the ellipse is
`r(θ) = (b²/a) / (1 + e cos θ)`.  It oscillates between

  `rMin = a − c = (q − p)/2`  and  `rMax = a + c = (q + p)/2`

(`focalRadius_zero`, `focalRadius_pi`, `focalRadius_bounds`).  These two bounds alone carry the
whole pair: `rMax + rMin = q`, `rMax − rMin = p`, `rMin · rMax = b²` and
`rMax² − rMin² = p q = n` (`bounds_sum`, `bounds_diff`, `bounds_mul`, `bounds_sq_sub`).

**Scale and volume.**  Given `n = p q`:
* the area `A = π a b` fixes `q⁴ = n² + (4A/π)²` (`area_sq`), so `n` and the area determine the
  ellipse completely (`area_determines`);
* the eccentricity fixes `p² = n e` and `q² = n / e` (`ecc_scale`), so a band `e₁ ≤ e ≤ e₂`
  confines `p` to `[√(n e₁), √(n e₂)]` (`ecc_band`);
* Fermat's search for `rMax` starts at `√n`, and the number of steps it needs is at most
  `rMin² / (2√n)` (`fermat_gap`): the rounder the ellipse, the shorter the search.

**Which partition.**  For odd primes `p < q` the two bounds are coprime integers
(`intBounds_coprime`), and the only ways to write `n = p q` as a difference of two squares
`X² − Y²` are the trivial one and `(rMax, rMin)` (`fermat_pairs_pq`).  Every difference-of-squares
representation `X² − Y² = n` comes from the divisor `X − Y` of `n`, i.e. from a ring of the
`n`-dial (`fermat_pair_divisor`).  So the ellipse's two bounds pick out exactly the `p`-ring and
the `q`-ring of the fractal partition of the `n`-dial.

These are reparametrisations: the ellipse is built from `p` and `q`, so knowing its area, its
eccentricity or its bounds is the same information as knowing `p` and `q`.
-/

@[expose] public section

namespace EllipseSearch

open Real PQEllipse

/-- Smallest focal distance `a − c = (q − p)/2`. -/
noncomputable def rMin (p q : ℝ) : ℝ := (q - p) / 2

/-- Largest focal distance `a + c = (q + p)/2`. -/
noncomputable def rMax (p q : ℝ) : ℝ := (q + p) / 2

/-- Distance from a focus of the pq ellipse to its point at angle `θ` (polar form
`r = (b²/a) / (1 + e cos θ)` with `a = q/2`, `e = p/q`). -/
noncomputable def focalRadius (p q θ : ℝ) : ℝ :=
  (semiMinorSq p q / (q / 2)) / (1 + (p / q) * cos θ)

/-- Area `π a b` of the pq ellipse. -/
noncomputable def area (p q : ℝ) : ℝ := π * (q / 2) * √(semiMinorSq p q)

theorem focalRadius_zero {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    focalRadius p q 0 = rMin p q := by
  unfold focalRadius rMin semiMinorSq
  rw [cos_zero]
  have : q + p ≠ 0 := by linarith
  field_simp
  ring

theorem focalRadius_pi {p q : ℝ} (hq : 0 < q) (hpq : p < q) :
    focalRadius p q π = rMax p q := by
  unfold focalRadius rMax semiMinorSq
  rw [cos_pi, show 1 + p / q * -1 = (q - p) / q by field_simp; ring]
  have : q - p ≠ 0 := by linarith
  field_simp
  ring

/-- The focal distance oscillates between `rMin` and `rMax`. -/
theorem focalRadius_bounds {p q : ℝ} (hp : 0 ≤ p) (hpq : p < q) (θ : ℝ) :
    rMin p q ≤ focalRadius p q θ ∧ focalRadius p q θ ≤ rMax p q := by
  have hq : 0 < q := by linarith
  set K := semiMinorSq p q / (q / 2) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]; unfold semiMinorSq
    apply div_nonneg _ (by linarith); apply div_nonneg _ (by norm_num); nlinarith
  have he0 : 0 ≤ p / q := div_nonneg hp hq.le
  have he1 : p / q < 1 := (div_lt_one hq).2 hpq
  have c1 := neg_one_le_cos θ
  have c2 := cos_le_one θ
  have hD1 : 1 - p / q ≤ 1 + p / q * cos θ := by nlinarith
  have hD2 : 1 + p / q * cos θ ≤ 1 + p / q := by nlinarith
  have hmin : rMin p q = K / (1 + p / q) := by
    rw [hK]; unfold rMin semiMinorSq
    have : q + p ≠ 0 := by linarith
    field_simp; ring
  have hmax : rMax p q = K / (1 - p / q) := by
    rw [hK]; unfold rMax semiMinorSq
    have : q - p ≠ 0 := by linarith
    field_simp; ring
  unfold focalRadius
  rw [← hK, hmin, hmax]
  constructor
  · exact div_le_div_of_nonneg_left hK0 (by linarith) hD2
  · exact div_le_div_of_nonneg_left hK0 (by linarith) hD1

theorem bounds_sum (p q : ℝ) : rMax p q + rMin p q = q := by unfold rMax rMin; ring

theorem bounds_diff (p q : ℝ) : rMax p q - rMin p q = p := by unfold rMax rMin; ring

theorem bounds_mul (p q : ℝ) : rMin p q * rMax p q = semiMinorSq p q := by
  unfold rMax rMin semiMinorSq; ring

theorem bounds_sq_sub (p q : ℝ) : rMax p q ^ 2 - rMin p q ^ 2 = p * q := by
  unfold rMax rMin; ring

/-- Area and `n = p q` fix `q`: `q⁴ = n² + (4A/π)²`. -/
theorem area_sq {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    q ^ 4 = (p * q) ^ 2 + (4 * area p q / π) ^ 2 := by
  unfold area
  have hb : 0 ≤ semiMinorSq p q := by unfold semiMinorSq; nlinarith
  rw [show 4 * (π * (q / 2) * √(semiMinorSq p q)) / π = 2 * q * √(semiMinorSq p q) by
    field_simp [pi_ne_zero]; ring]
  rw [mul_pow (2 * q), sq_sqrt hb]; unfold semiMinorSq; ring

/-- Two pq ellipses with the same `n` and the same area are the same ellipse. -/
theorem area_determines {p q p' q' : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hp' : 0 ≤ p')
    (hpq' : p' ≤ q') (hn : p * q = p' * q') (hA : area p q = area p' q') (hn0 : 0 < p * q) :
    p = p' ∧ q = q' := by
  have h1 := area_sq hp hpq
  have h2 := area_sq hp' hpq'
  rw [← hn, ← hA] at h2
  have hq4 : q ^ 4 = q' ^ 4 := by rw [h1, h2]
  have hq : q = q' := (pow_left_inj₀ (by linarith) (by linarith) (by norm_num)).1 hq4
  subst hq
  have hq0 : 0 < q := by nlinarith
  exact ⟨mul_right_cancel₀ hq0.ne' hn, rfl⟩

/-- The eccentricity fixes the scale: `p² = n e`, `q² = n / e`. -/
theorem ecc_scale {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    p ^ 2 = (p * q) * (p / q) ∧ q ^ 2 = (p * q) / (p / q) := by
  constructor <;> field_simp

/-- An eccentricity band confines the smaller factor to `[√(n e₁), √(n e₂)]`. -/
theorem ecc_band {p q e₁ e₂ : ℝ} (hp : 0 < p) (hq : 0 < q) (h₁ : e₁ ≤ p / q) (h₂ : p / q ≤ e₂) :
    √((p * q) * e₁) ≤ p ∧ p ≤ √((p * q) * e₂) := by
  have key : p ^ 2 = (p * q) * (p / q) := by field_simp
  have hn : 0 < p * q := mul_pos hp hq
  constructor
  · calc √((p * q) * e₁) ≤ √((p * q) * (p / q)) :=
          sqrt_le_sqrt (mul_le_mul_of_nonneg_left h₁ hn.le)
      _ = p := by rw [← key, sqrt_sq hp.le]
  · calc p = √((p * q) * (p / q)) := by rw [← key, sqrt_sq hp.le]
      _ ≤ √((p * q) * e₂) := sqrt_le_sqrt (mul_le_mul_of_nonneg_left h₂ hn.le)

/-- Fermat's search: `rMax ≥ √n`, and the distance from `√n` to `rMax` is at most
`rMin² / (2√n)`. -/
theorem fermat_gap {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    √(p * q) ≤ rMax p q ∧ rMax p q - √(p * q) ≤ rMin p q ^ 2 / (2 * √(p * q)) := by
  have hn : 0 < p * q := mul_pos hp hq
  set s := √(p * q) with hs
  have hs0 : 0 < s := sqrt_pos.2 hn
  have hss : s ^ 2 = p * q := sq_sqrt hn.le
  have key := bounds_sq_sub p q
  have hR : 0 < rMax p q := by unfold rMax; linarith
  have h1 : s ≤ rMax p q := by nlinarith [sq_nonneg (rMin p q)]
  refine ⟨h1, ?_⟩
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (rMin p q)]

/-! ### Integer bounds and the partition of the `n`-dial -/

/-- For odd `p < q`, the integer bounds `(q − p)/2`, `(q + p)/2` satisfy
`rMax² = rMin² + p q`, `rMax − rMin = p`, `rMax + rMin = q`. -/
theorem intBounds {p q : ℕ} (hp : Odd p) (hq : Odd q) (hpq : p ≤ q) :
    ((q + p) / 2) ^ 2 = ((q - p) / 2) ^ 2 + p * q ∧ (q + p) / 2 - (q - p) / 2 = p ∧
      (q + p) / 2 + (q - p) / 2 = q := by
  obtain ⟨a, rfl⟩ := hp
  obtain ⟨b, rfl⟩ := hq
  have hu : (2 * b + 1 + (2 * a + 1)) / 2 = a + b + 1 := by omega
  have hv : (2 * b + 1 - (2 * a + 1)) / 2 = b - a := by omega
  rw [hu, hv]
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le (show a ≤ b by omega)
  rw [show a + c - a = c by omega]
  refine ⟨by ring, by omega, by omega⟩

/-- The integer bounds are coprime when `p` and `q` are. -/
theorem intBounds_coprime {p q : ℕ} (hp : Odd p) (hq : Odd q) (hpq : p ≤ q)
    (hc : Nat.Coprime p q) : Nat.Coprime ((q - p) / 2) ((q + p) / 2) := by
  obtain ⟨_, h2, h3⟩ := intBounds hp hq hpq
  set u := (q + p) / 2
  set v := (q - p) / 2
  have d1 : Nat.gcd v u ∣ p := h2 ▸ Nat.dvd_sub (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
  have d2 : Nat.gcd v u ∣ q := h3 ▸ Nat.dvd_add (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
  exact Nat.dvd_one.mp (by rw [← hc]; exact Nat.dvd_gcd d1 d2)

/-- Every representation `X² = Y² + n` comes from a ring of the `n`-dial:
`X − Y` divides `n` and `(X − Y)(X + Y) = n`. -/
theorem fermat_pair_divisor {n X Y : ℕ} (h : X ^ 2 = Y ^ 2 + n) :
    Y ≤ X ∧ (X - Y) * (X + Y) = n ∧ X - Y ∣ n := by
  have hYX : Y ≤ X := by
    by_contra hc
    push_neg at hc
    nlinarith
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hYX
  have e : (Y + d - Y) * (Y + d + Y) = n := by
    rw [Nat.add_sub_cancel_left]; nlinarith
  exact ⟨hYX, e, e ▸ dvd_mul_right _ _⟩

/-- **The ellipse bounds are the only non-trivial partition of the pq dial.**  For odd primes
`p < q`, the solutions of `X² = Y² + p q` are exactly the trivial pair and the pair
`(rMax, rMin)` of the pq ellipse. -/
theorem fermat_pairs_pq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hpq : p < q)
    (X Y : ℕ) :
    X ^ 2 = Y ^ 2 + p * q ↔
      (X = (p * q + 1) / 2 ∧ Y = (p * q - 1) / 2) ∨ (X = (q + p) / 2 ∧ Y = (q - p) / 2) := by
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hqo : Odd q := hq.odd_of_ne_two (by have := hp.two_le; omega)
  have hno : Odd (p * q) := hpo.mul hqo
  constructor
  · intro h
    obtain ⟨hYX, he, hd⟩ := fermat_pair_divisor h
    obtain ⟨d1, d2, h1, h2, hd12⟩ := Nat.dvd_mul.1 hd
    rcases (Nat.dvd_prime hp).1 h1 with e1 | e1 <;>
      rcases (Nat.dvd_prime hq).1 h2 with e2 | e2 <;> rw [e1, e2] at hd12
    · left
      rw [one_mul] at hd12
      rw [← hd12, one_mul] at he
      obtain ⟨k, hk⟩ := hno
      omega
    · exfalso
      rw [one_mul] at hd12
      rw [← hd12, mul_comm p q] at he
      have : X + Y = p := Nat.eq_of_mul_eq_mul_left hq.pos he
      omega
    · right
      rw [mul_one] at hd12
      rw [← hd12] at he
      have : X + Y = q := Nat.eq_of_mul_eq_mul_left hp.pos he
      omega
    · exfalso
      rw [← hd12] at he
      have : X + Y = 1 :=
        Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hp.pos hq.pos) (he.trans (mul_one _).symm)
      have := hp.two_le
      have : p * q ≥ 4 := by nlinarith [hq.two_le]
      omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · obtain ⟨k, hk⟩ := hno
      rw [hk, show (2 * k + 1 + 1) / 2 = k + 1 by omega, show (2 * k + 1 - 1) / 2 = k by omega]
      ring
    · exact (intBounds hpo hqo hpq.le).1

/-- Example: `19 · 181 = 3439`: bounds `81` and `100`, and `100² − 81² = 3439`. -/
theorem nineteen_bounds : (181 + 19) / 2 = 100 ∧ (181 - 19) / 2 = 81 ∧
    100 ^ 2 = 81 ^ 2 + 19 * 181 := by norm_num

end EllipseSearch
