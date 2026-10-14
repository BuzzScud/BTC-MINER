module

public import Mathlib
public import RequestProject.UnitsSquareOne

/-!
# Prime towers fold flat on every dial

A tetration tower is `a ↑↑ k = a^a^…^a` (`k` copies of `a`).  Here: `tower a 0 = 1`,
`tower a (k + 1) = a ^ tower a k`.

* **Every tower folds onto one mark of any dial** (`tower_eventually_const`): for every base
  `a ≥ 1` and every dial size `m ≥ 1`, the marks `tower a k mod m` are eventually constant.
  The proof peels the dial down the totient chain `m → φ(m) → φ(φ(m)) → … → 1`, using the
  generalized Euler congruence `a^(x + φ(m)) ≡ a^x (mod m)` for `x ≥ m`
  (`pow_add_totient_modEq`), which needs no coprimality.
* **On the 12- and 24-hour dials, towers of primes `p ≥ 5` fold at the first level**
  (`tower_mod_24`): `p ↑↑ k ≡ p (mod 24)` for every height `k ≥ 1`, because every unit modulo 24
  squares to 1 (`units_sq_mod_24`).  Among dial sizes up to 1000, 24 and its divisors are the
  only ones with that property (`units_sq_one_only_24`).
* **On the 360 dial they fold at the second level** (`tower_mod_360`): for every prime
  `p ≥ 7`, `p ↑↑ k ≡ p^p (mod 360)` for every height `k ≥ 2`.  When `p² ≡ 1 (mod 360)` (the
  qualifying residues `1, 19, 71, 89 mod 90` of the thesis), every tower of `p` sits on the mark
  `p` itself (`tower_mod_360_of_sq_one`); for example all towers of 19.
* The base 0 is excluded for a reason: its towers alternate `1, 0, 1, 0, …`
  (`tower_zero_alternates`).
-/

@[expose] public section

namespace TowerFold

/-- The tetration tower `a ↑↑ k`. -/
def tower (a : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => a ^ tower a k

@[simp] theorem tower_zero (a : ℕ) : tower a 0 = 1 := rfl
@[simp] theorem tower_succ (a k : ℕ) : tower a (k + 1) = a ^ tower a k := rfl

theorem tower_zero_alternates (k : ℕ) : tower 0 (2 * k) = 1 ∧ tower 0 (2 * k + 1) = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, tower_succ, ih.2, pow_zero]
    simp [ih.1]

theorem tower_one (k : ℕ) : tower 1 k = 1 := by
  cases k <;> simp

theorem tower_ge (a : ℕ) (ha : 2 ≤ a) (k : ℕ) : k ≤ tower a k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [tower_succ]
    have : tower a k < a ^ tower a k := Nat.lt_pow_self (by omega)
    omega

/-- The prime-power piece of the generalized Euler congruence. -/
lemma prime_pow_dvd (a m x p : ℕ) (hp : p.Prime) (hm : m ≠ 0) (hx : m ≤ x) (ha : 1 ≤ a) :
    p ^ m.factorization p ∣ a ^ x * (a ^ m.totient - 1) := by
  set e := m.factorization p
  have hq : p ^ e ∣ m := Nat.ordProj_dvd m p
  by_cases hpa : p ∣ a
  · have hem : e ≤ x := by
      have h1 : p ^ e ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hq
      have h2 : e < p ^ e := Nat.lt_pow_self hp.one_lt
      omega
    exact Dvd.dvd.mul_right ((pow_dvd_pow p hem).trans (pow_dvd_pow_of_dvd hpa x)) _
  · apply Dvd.dvd.mul_left
    have hcop : Nat.Coprime a (p ^ e) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_comm).1 ((hp.coprime_iff_not_dvd).2 hpa))
    have h1 : a ^ (p ^ e).totient ≡ 1 [MOD p ^ e] := Nat.ModEq.pow_totient hcop
    obtain ⟨j, hj⟩ := Nat.totient_dvd_of_dvd hq
    have h2 : a ^ m.totient ≡ 1 [MOD p ^ e] := by
      rw [hj, pow_mul]
      simpa using h1.pow j
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ ha)).1 h2.symm

/-- **Generalized Euler congruence**: `a^(x + φ(m)) ≡ a^x (mod m)` whenever `x ≥ m`, with no
coprimality assumption. -/
theorem pow_add_totient_modEq (a m x : ℕ) (hm : m ≠ 0) (hx : m ≤ x) :
    a ^ (x + m.totient) ≡ a ^ x [MOD m] := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have : 0 < x := by omega
    rw [zero_pow (by omega), zero_pow (by omega)]
  have hdvd : m ∣ a ^ x * (a ^ m.totient - 1) := by
    by_cases hN : a ^ x * (a ^ m.totient - 1) = 0
    · rw [hN]; exact dvd_zero m
    rw [← Nat.factorization_prime_le_iff_dvd hm hN]
    intro p hp
    rw [← hp.pow_dvd_iff_le_factorization hN]
    exact prime_pow_dvd a m x p hp hm hx ha
  have hle : a ^ x ≤ a ^ (x + m.totient) := Nat.pow_le_pow_right ha (by omega)
  apply Nat.ModEq.symm
  rw [Nat.modEq_iff_dvd' hle, pow_add, ← Nat.mul_sub_one]
  exact hdvd

theorem pow_add_mul_totient_modEq (a m x j : ℕ) (hm : m ≠ 0) (hx : m ≤ x) :
    a ^ (x + j * m.totient) ≡ a ^ x [MOD m] := by
  induction j with
  | zero => simpa using Nat.ModEq.refl (a ^ x)
  | succ j ih =>
    rw [show x + (j + 1) * m.totient = (x + j * m.totient) + m.totient by ring]
    exact (pow_add_totient_modEq a m _ hm (by nlinarith)).trans ih

/-- Exponents that agree modulo `φ(m)` and are at least `m` give the same mark on the
`m` dial. -/
theorem pow_modEq_of_exp_modEq (a m x y : ℕ) (hm : m ≠ 0) (hx : m ≤ x) (hy : m ≤ y)
    (hxy : x ≡ y [MOD m.totient]) : a ^ x ≡ a ^ y [MOD m] := by
  wlog h : x ≤ y generalizing x y
  · exact (this y x hy hx hxy.symm (by omega)).symm
  obtain ⟨j, hj⟩ := (Nat.modEq_iff_dvd' h).1 hxy
  rw [show y = x + j * m.totient by rw [mul_comm, ← hj]; omega]
  exact (pow_add_mul_totient_modEq a m x j hm hx).symm

/-- **Every tower folds onto a single mark of every dial.** -/
theorem tower_eventually_const (a : ℕ) (ha : 1 ≤ a) (m : ℕ) (hm : 1 ≤ m) :
    ∃ K, ∀ k, K ≤ k → tower a k ≡ tower a K [MOD m] := by
  rcases Nat.lt_or_ge a 2 with ha1 | ha2
  · obtain rfl : a = 1 := by omega
    exact ⟨0, fun k _ => by rw [tower_one, tower_one]⟩
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge m 2 with hm1 | hm2
    · obtain rfl : m = 1 := by omega
      exact ⟨0, fun k _ => Nat.modEq_one⟩
    have ht : m.totient < m := Nat.totient_lt m (by omega)
    have ht1 : 1 ≤ m.totient := Nat.totient_pos.2 (by omega)
    obtain ⟨K', hK'⟩ := ih m.totient ht ht1
    refine ⟨max K' m + 1, fun k hk => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [tower_succ, tower_succ]
    apply pow_modEq_of_exp_modEq a m _ _ (by omega)
    · exact le_trans (by omega) (tower_ge a ha2 k)
    · exact le_trans (by omega) (tower_ge a ha2 _)
    · exact (hK' k (by omega)).trans (hK' _ (by omega)).symm

/-! ## The 24-hour and 360 dials -/

lemma coprime_mod_left {u n : ℕ} (hu : Nat.Coprime u n) : Nat.Coprime (u % n) n := by
  unfold Nat.Coprime
  rw [← Nat.gcd_rec]
  exact Nat.coprime_comm.1 hu

/-- Every unit modulo 24 squares to 1. -/
theorem units_sq_mod_24 (u : ℕ) (hu : Nat.Coprime u 24) : u ^ 2 ≡ 1 [MOD 24] := by
  have h : ∀ r < 24, Nat.Coprime r 24 → r ^ 2 % 24 = 1 := by decide
  unfold Nat.ModEq
  rw [Nat.pow_mod]
  exact h (u % 24) (Nat.mod_lt _ (by norm_num)) (coprime_mod_left hu)

/-- Among dial sizes `2 ≤ n ≤ 1000`, only the divisors of 24 have every unit squaring to 1.
(Formerly a compiled finite check; now the bounded case of the general theorem
`UnitsSquareOne.units_sq_one_only_24_all`.) -/
theorem units_sq_one_only_24 :
    ∀ n ∈ Finset.Icc 2 1000,
      (∀ u ∈ Finset.range n, Nat.Coprime u n → u ^ 2 % n = 1) → n ∣ 24 :=
  fun n hn h => UnitsSquareOne.units_sq_one_only_24_all n (Finset.mem_Icc.1 hn).1 h

theorem tower_odd (a : ℕ) (ha : Odd a) (k : ℕ) : Odd (tower a k) := by
  cases k with
  | zero => simp
  | succ k => rw [tower_succ]; exact ha.pow

/-- **On the 24-hour dial every tower of a prime `p ≥ 5` sits on the mark `p` at every
height.** -/
theorem tower_mod_24 (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (k : ℕ) (hk : 1 ≤ k) :
    tower p k ≡ p [MOD 24] := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hcop : Nat.Coprime p 24 := by
    rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num]
    apply Nat.Coprime.mul_right
    · apply Nat.Coprime.pow_right
      exact (Nat.coprime_primes hp Nat.prime_two).2 (by omega)
    · exact (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨j, hj⟩ := tower_odd p hodd k
  rw [tower_succ, hj, pow_succ, pow_mul]
  have := (units_sq_mod_24 p hcop).pow j
  rw [one_pow] at this
  simpa using this.mul_right p

/-- Every unit modulo 360 has twelfth power 1 (the Carmichael exponent of 360 is 12). -/
theorem units_pow_twelve_mod_360 (u : ℕ) (hu : Nat.Coprime u 360) : u ^ 12 ≡ 1 [MOD 360] := by
  have h : ∀ r < 360, Nat.Coprime r 360 → r ^ 12 % 360 = 1 := by decide +kernel
  unfold Nat.ModEq
  rw [Nat.pow_mod]
  exact h (u % 360) (Nat.mod_lt _ (by norm_num)) (coprime_mod_left hu)

lemma prime_coprime_360 (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) : Nat.Coprime p 360 := by
  rw [show (360 : ℕ) = 2 ^ 3 * 3 ^ 2 * 5 by norm_num]
  refine Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ ?_) ?_
  · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 (by omega))
  · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_three).2 (by omega))
  · exact (Nat.coprime_primes hp Nat.prime_five).2 (by omega)

/-- **On the 360 dial every tower of a prime `p ≥ 7` of height at least 2 sits on the mark of
`p^p`.** -/
theorem tower_mod_360 (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) (k : ℕ) (hk : 2 ≤ k) :
    tower p k ≡ p ^ p [MOD 360] := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h24 := tower_mod_24 p hp (by omega) k (by omega)
  have h12 : tower p k ≡ p [MOD 12] := Nat.ModEq.of_mul_left 2 h24
  have hle : p ≤ tower p k := by
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [tower_succ]
    have := Nat.one_le_iff_ne_zero.2 (show tower p k ≠ 0 from (tower_odd p
      (hp.odd_of_ne_two (by omega)) k).pos.ne')
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ tower p k := Nat.pow_le_pow_right hp.pos this
  obtain ⟨j, hj⟩ := (Nat.modEq_iff_dvd' hle).1 h12.symm
  rw [tower_succ, show tower p k = p + 12 * j by omega, pow_add, pow_mul]
  have := (units_pow_twelve_mod_360 p (prime_coprime_360 p hp h7)).pow j
  rw [one_pow] at this
  simpa using this.mul_left (p ^ p)

/-- **If `p² ≡ 1 (mod 360)`, every tower of `p` sits on the mark `p` of the 360 dial.** -/
theorem tower_mod_360_of_sq_one (p : ℕ) (hp : p.Prime) (hsq : p ^ 2 ≡ 1 [MOD 360])
    (k : ℕ) (hk : 1 ≤ k) : tower p k ≡ p [MOD 360] := by
  have h2 : p ≠ 2 := by rintro rfl; revert hsq; decide
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨j, hj⟩ := tower_odd p (hp.odd_of_ne_two h2) k
  rw [tower_succ, hj, pow_succ, pow_mul]
  have := hsq.pow j
  rw [one_pow] at this
  simpa using this.mul_right p

/-- For example, every tower of 19 sits on the mark 19 of the 360 dial. -/
theorem tower_nineteen (k : ℕ) (hk : 1 ≤ k) : tower 19 k ≡ 19 [MOD 360] :=
  tower_mod_360_of_sq_one 19 (by norm_num) (by decide) k hk

/-- The marks `p^p mod 360` on which the towers of the primes `7 … 31` settle. -/
theorem tower_marks_360 :
    [7, 11, 13, 17, 19, 23, 29, 31].map (fun p => p ^ p % 360) =
      [223, 131, 13, 17, 19, 47, 149, 31] := by
  decide

end TowerFold
