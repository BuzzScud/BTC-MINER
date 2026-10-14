module

public import Mathlib

/-!
# Divisor sums of a completely multiplicative weight: one prime at a time

For a weight `f : ℕ → ℤ` with `f (p * d) = f p * f d`, the divisor sum `G(n) = Σ_{d ∣ n} f(d)`
satisfies, for every prime `p` and `m ≥ 1`,

  `G(p·m) = G(m) + f(p) · (G(m) − [p ∣ m] · G(m/p))`   (`divisorSum_prime_mul`).

(The divisors of `p·m` are the divisors of `m` together with `p` times them; the overlap is `p` times
the divisors of `m/p`.)  This is the recursion that the circle counts `r₂` and `r_hex` also satisfy,
which is how Jacobi's formulas are proved in `JacobiCircles.lean`.

The two weights used there are the characters `χ₄` and `χ₃`, written with `%`
(`chi4`, `chi3`), matching `LatticePatterns.chi4Sum` and `LatticePatterns.chi3Sum`.
-/

@[expose] public section

namespace DivisorRecursion

/-- `Σ_{d ∣ n} f(d)`. -/
def divisorSum (f : ℕ → ℤ) (n : ℕ) : ℤ := ∑ d ∈ n.divisors, f d

/-- The character mod 4: `1` on `1 (mod 4)`, `−1` on `3 (mod 4)`, `0` on even numbers. -/
def chi4 (d : ℕ) : ℤ := if d % 4 = 1 then 1 else if d % 4 = 3 then -1 else 0

/-- The character mod 3: `1` on `1 (mod 3)`, `−1` on `2 (mod 3)`, `0` on multiples of 3. -/
def chi3 (d : ℕ) : ℤ := if d % 3 = 1 then 1 else if d % 3 = 2 then -1 else 0

lemma chi4_mul (a b : ℕ) : chi4 (a * b) = chi4 a * chi4 b := by
  have h : (a * b) % 4 = ((a % 4) * (b % 4)) % 4 := Nat.mul_mod _ _ _
  have ha := Nat.mod_lt a (show 0 < 4 by norm_num)
  have hb := Nat.mod_lt b (show 0 < 4 by norm_num)
  unfold chi4
  rw [h]
  interval_cases (a % 4) <;> interval_cases (b % 4) <;> simp

lemma chi3_mul (a b : ℕ) : chi3 (a * b) = chi3 a * chi3 b := by
  have h : (a * b) % 3 = ((a % 3) * (b % 3)) % 3 := Nat.mul_mod _ _ _
  have ha := Nat.mod_lt a (show 0 < 3 by norm_num)
  have hb := Nat.mod_lt b (show 0 < 3 by norm_num)
  unfold chi3
  rw [h]
  interval_cases (a % 3) <;> interval_cases (b % 3) <;> simp

/-- **The one-prime recursion for divisor sums.** -/
theorem divisorSum_prime_mul (f : ℕ → ℤ) (hf : ∀ a b, f (a * b) = f a * f b) {p : ℕ}
    (hp : p.Prime) {m : ℕ} (hm : m ≠ 0) :
    divisorSum f (p * m) =
      divisorSum f m + f p * (divisorSum f m - if p ∣ m then divisorSum f (m / p) else 0) := by
  classical
  have hp0 : p ≠ 0 := hp.ne_zero
  have hinj : Function.Injective (fun d : ℕ => p * d) := fun a b h => by
    simpa [hp0] using h
  have hunion : (p * m).divisors = m.divisors ∪ m.divisors.image (fun d => p * d) := by
    ext d
    simp only [Finset.mem_union, Finset.mem_image, Nat.mem_divisors]
    constructor
    · rintro ⟨hd, -⟩
      by_cases hpd : p ∣ d
      · obtain ⟨e, rfl⟩ := hpd
        right
        exact ⟨e, ⟨Nat.dvd_of_mul_dvd_mul_left hp.pos hd, hm⟩, rfl⟩
      · left
        exact ⟨(Nat.Coprime.dvd_mul_left ((Nat.coprime_comm).1
          ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd))).1 hd, hm⟩
    · rintro (⟨hd, -⟩ | ⟨e, ⟨he, -⟩, rfl⟩)
      · exact ⟨hd.mul_left p, mul_ne_zero hp0 hm⟩
      · exact ⟨Nat.mul_dvd_mul_left p he, mul_ne_zero hp0 hm⟩
  have hB : ∑ d ∈ m.divisors.image (fun d => p * d), f d = f p * divisorSum f m := by
    rw [Finset.sum_image (fun a _ b _ h => hinj h), divisorSum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun d _ => hf p d)
  have hI : ∑ d ∈ m.divisors ∩ m.divisors.image (fun d => p * d), f d =
      f p * (if p ∣ m then divisorSum f (m / p) else 0) := by
    split_ifs with hpm
    · obtain ⟨k, rfl⟩ := hpm
      have hk : k ≠ 0 := by rintro rfl; simp at hm
      have hset : (p * k).divisors ∩ (p * k).divisors.image (fun d => p * d) =
          k.divisors.image (fun d => p * d) := by
        ext d
        simp only [Finset.mem_inter, Finset.mem_image, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨hd, -⟩, e, -, rfl⟩
          exact ⟨e, ⟨Nat.dvd_of_mul_dvd_mul_left hp.pos hd, hk⟩, rfl⟩
        · rintro ⟨e, ⟨he, -⟩, rfl⟩
          exact ⟨⟨Nat.mul_dvd_mul_left p he, hm⟩, e, ⟨he.mul_left p, hm⟩, rfl⟩
      rw [hset, Finset.sum_image (fun a _ b _ h => hinj h), Nat.mul_div_cancel_left k hp.pos,
        divisorSum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun d _ => hf p d)
    · have hset : m.divisors ∩ m.divisors.image (fun d => p * d) = ∅ := by
        ext d
        simp only [Finset.mem_inter, Finset.mem_image, Nat.mem_divisors, Finset.notMem_empty,
          iff_false, not_and]
        rintro ⟨hd, -⟩ ⟨e, -, rfl⟩
        exact hpm (dvd_trans (Dvd.intro e rfl) hd)
      rw [hset, Finset.sum_empty, mul_zero]
  have key := Finset.sum_union_inter (s₁ := m.divisors) (s₂ := m.divisors.image (fun d => p * d))
    (f := f)
  rw [← hunion, hB, hI] at key
  unfold divisorSum at *
  linarith

lemma divisorSum_one (f : ℕ → ℤ) : divisorSum f 1 = f 1 := by simp [divisorSum]

/-- **Uniqueness of the recursion.** A function `R` with `R(1) = c · f(1)` that obeys the same
one-prime recursion as `divisorSum f` is `c · divisorSum f` on all `n ≥ 1`. -/
theorem eq_of_recursion (f : ℕ → ℤ) (hf : ∀ a b, f (a * b) = f a * f b) (R : ℕ → ℤ) (c : ℤ)
    (h1 : R 1 = c * f 1)
    (hrec : ∀ p m : ℕ, p.Prime → m ≠ 0 →
      R (p * m) = R m + f p * (R m - if p ∣ m then R (m / p) else 0)) :
    ∀ n : ℕ, n ≠ 0 → R n = c * divisorSum f n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hn1 : n = 1
    · subst hn1; rw [h1, divisorSum_one]
    · have hp := Nat.minFac_prime hn1
      set p := n.minFac
      obtain ⟨m, hm⟩ := Nat.minFac_dvd n
      have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact hn hm
      have hmn : m < n := by
        rw [hm]; exact lt_mul_left (Nat.pos_of_ne_zero hm0) hp.one_lt
      rw [hm, hrec p m hp hm0, divisorSum_prime_mul f hf hp hm0, ih m hmn hm0]
      split_ifs with hpm
      · have hmp0 : m / p ≠ 0 := by
          obtain ⟨k, rfl⟩ := hpm
          rw [Nat.mul_div_cancel_left k hp.pos]; rintro rfl; simp at hm0
        rw [ih (m / p) (lt_of_le_of_lt (Nat.div_le_self m p) hmn) hmp0]; ring
      · ring

end DivisorRecursion
