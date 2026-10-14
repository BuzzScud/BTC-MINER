module

public import Mathlib

/-!
# Consecutive 5-smooth numbers and the complete dual-smooth prime census

`THESIS.md` (ledger rows BG-020, BG-023, XP-DT-028, XP-DT-036) reports, *inside an audited
bound*, that the primes `p` for which both `p - 1` and `p + 1` are `{2,3,5}`-smooth are exactly
`{2, 3, 5, 7, 11, 17, 19, 31}`.

This file removes the bound.  We prove Størmer's theorem for the primes `{2, 3, 5}`:

* `consecutive_smooth` — the only pairs `(m, m + 1)` of consecutive 5-smooth numbers are
  `m ∈ {1, 2, 3, 4, 5, 8, 9, 15, 24, 80}`;
* `superparticular_five_limit` — equivalently, the only 5-limit superparticular ratios
  `(m+1)/m` are `2/1, 3/2, 4/3, 5/4, 6/5, 9/8, 10/9, 16/15, 25/24, 81/80`
  (the last is the syntonic comma);
* `dual_smooth_prime_iff` — a prime `p` has both `p - 1` and `p + 1` 5-smooth iff
  `p ∈ {2, 3, 5, 7, 11, 17, 19, 31}`, with no bound on `p`.

The proof reduces to six exponential equations `x + 1 = y` between coprime 5-smooth numbers,
each solved by elementary congruences (orders of `2, 3, 5` modulo `8, 9, 25, 64` and a second
modulus such as `7, 11, 17, 41, 1181`).
-/

@[expose] public section

namespace DualSmooth

/-- `n` is 5-smooth (regular): `n = 2^a 3^b 5^c`. -/
def Smooth5 (n : ℕ) : Prop := ∃ a b c : ℕ, n = 2 ^ a * 3 ^ b * 5 ^ c

/-! ### Elementary tools -/

lemma pow_mod_cycle {b M k : ℕ} (hk : b ^ k % M = 1) (n : ℕ) :
    b ^ n % M = b ^ (n % k) % M := by
  conv_lhs => rw [← Nat.div_add_mod n k, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod, hk, one_pow]
  have hM : M ≠ 1 := by
    intro hM1
    rw [hM1, Nat.mod_one] at hk
    exact zero_ne_one hk
  rw [Nat.one_mod_eq_one.mpr hM, one_mul, Nat.mod_mod]

lemma not_dvd_of_coprime {q X : ℕ} (hq : 1 < q) (h : Nat.Coprime q X) : ¬ q ∣ X := fun hd => by
  have := Nat.Coprime.eq_one_of_dvd h hd
  omega

lemma coprime_pp {q u v : ℕ} (hu : Nat.Coprime q u) (hv : Nat.Coprime q v) (i j : ℕ) :
    Nat.Coprime q (u ^ i * v ^ j) :=
  Nat.Coprime.mul_right (Nat.Coprime.pow_right i hu) (Nat.Coprime.pow_right j hv)

lemma pow_dvd_of_le {p i j : ℕ} (h : i ≤ j) : p ^ i ∣ p ^ j := pow_dvd_pow p h

/-! ### The six exponential equations -/

/-- `3^b 5^c + 1 = 2^d`: only `1 + 1 = 2`, `3 + 1 = 4`, `15 + 1 = 16`. -/
lemma eq_D_plus {b c d : ℕ} (h : 3 ^ b * 5 ^ c + 1 = 2 ^ d) :
    3 ^ b * 5 ^ c = 1 ∨ 3 ^ b * 5 ^ c = 3 ∨ 3 ^ b * 5 ^ c = 15 := by
  have hX : 0 < 3 ^ b * 5 ^ c := by positivity
  by_cases hd : d < 3
  · interval_cases d <;> norm_num at h <;> omega
  push_neg at hd
  have h8 : (3 ^ b * 5 ^ c) % 8 = 7 := by
    have : 2 ^ 3 ∣ 2 ^ d := pow_dvd_of_le hd
    omega
  rw [Nat.mul_mod, pow_mod_cycle (k := 2) (by norm_num : 3 ^ 2 % 8 = 1) b,
    pow_mod_cycle (k := 2) (by norm_num : 5 ^ 2 % 8 = 1) c] at h8
  have hbc : b % 2 = 1 ∧ c % 2 = 1 := by
    have key : ∀ r < 2, ∀ s < 2, (3 ^ r % 8 % 8 * (5 ^ s % 8 % 8)) % 8 = 7 → r = 1 ∧ s = 1 := by
      decide
    exact key _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num)) (by simpa using h8)
  have hb1 : 1 ≤ b := by omega
  have hc1 : 1 ≤ c := by omega
  -- `d ≡ 0 (mod 4)` from `2^d ≡ 1 (mod 5)`
  have h5 : 2 ^ d % 5 = 1 := by
    have : 5 ∣ 3 ^ b * 5 ^ c := Dvd.dvd.mul_left (dvd_pow_self 5 (by omega)) _
    omega
  rw [pow_mod_cycle (k := 4) (by norm_num : 2 ^ 4 % 5 = 1)] at h5
  have hd4 : d % 4 = 0 := by
    have key : ∀ r < 4, 2 ^ r % 5 = 1 → r = 0 := by decide
    exact key _ (Nat.mod_lt _ (by norm_num)) h5
  have hb : b = 1 := by
    by_contra hb
    have h9 : 2 ^ d % 9 = 1 := by
      have : 9 ∣ 3 ^ b * 5 ^ c :=
        Dvd.dvd.mul_right (by simpa using (pow_dvd_of_le (p := 3) (show 2 ≤ b by omega))) _
      omega
    rw [pow_mod_cycle (k := 6) (by norm_num : 2 ^ 6 % 9 = 1)] at h9
    have hd6 : d % 6 = 0 := by
      have key : ∀ r < 6, 2 ^ r % 9 = 1 → r = 0 := by decide
      exact key _ (Nat.mod_lt _ (by norm_num)) h9
    have h7 : 2 ^ d % 7 = 1 := by
      rw [pow_mod_cycle (k := 3) (by norm_num : 2 ^ 3 % 7 = 1)]
      have : d % 3 = 0 := by omega
      rw [this]; norm_num
    have : 7 ∣ 3 ^ b * 5 ^ c := by omega
    exact not_dvd_of_coprime (by norm_num) (coprime_pp (by norm_num) (by norm_num) b c) this
  have hc : c = 1 := by
    by_contra hc
    have h25 : 2 ^ d % 25 = 1 := by
      have : 25 ∣ 3 ^ b * 5 ^ c :=
        Dvd.dvd.mul_left (by simpa using (pow_dvd_of_le (p := 5) (show 2 ≤ c by omega))) _
      omega
    rw [pow_mod_cycle (k := 20) (by norm_num : 2 ^ 20 % 25 = 1)] at h25
    have hd20 : d % 20 = 0 := by
      have key : ∀ r < 20, 2 ^ r % 25 = 1 → r = 0 := by decide
      exact key _ (Nat.mod_lt _ (by norm_num)) h25
    have h11 : 2 ^ d % 11 = 1 := by
      rw [pow_mod_cycle (k := 10) (by norm_num : 2 ^ 10 % 11 = 1)]
      have : d % 10 = 0 := by omega
      rw [this]; norm_num
    have : 11 ∣ 3 ^ b * 5 ^ c := by omega
    exact not_dvd_of_coprime (by norm_num) (coprime_pp (by norm_num) (by norm_num) b c) this
  subst hb hc
  norm_num

/-- `2^a + 1 = 3^e 5^f`: only `2 + 1 = 3`, `4 + 1 = 5`, `8 + 1 = 9`. -/
lemma eq_D_minus {a e f : ℕ} (h : 2 ^ a + 1 = 3 ^ e * 5 ^ f) :
    2 ^ a = 2 ∨ 2 ^ a = 4 ∨ 2 ^ a = 8 := by
  by_cases ha : a < 6
  · have he : e < 4 := by
      by_contra he
      have : 3 ^ 4 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 1 ≤ 5 ^ f := Nat.one_le_pow _ _ (by norm_num)
      have : 2 ^ a ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
      nlinarith
    have hf : f < 3 := by
      by_contra hf
      have : 5 ^ 3 ≤ 5 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 1 ≤ 3 ^ e := Nat.one_le_pow _ _ (by norm_num)
      have : 2 ^ a ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
      nlinarith
    interval_cases a <;> interval_cases e <;> interval_cases f <;> simp_all
  push_neg at ha
  have h8 : (3 ^ e * 5 ^ f) % 8 = 1 := by
    have : 2 ^ 3 ∣ 2 ^ a := pow_dvd_of_le (by omega)
    omega
  rw [Nat.mul_mod, pow_mod_cycle (k := 2) (by norm_num : 3 ^ 2 % 8 = 1) e,
    pow_mod_cycle (k := 2) (by norm_num : 5 ^ 2 % 8 = 1) f] at h8
  have hef : e % 2 = 0 ∧ f % 2 = 0 := by
    have key : ∀ r < 2, ∀ s < 2, (3 ^ r % 8 % 8 * (5 ^ s % 8 % 8)) % 8 = 1 → r = 0 ∧ s = 0 := by
      decide
    exact key _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num)) (by simpa using h8)
  rcases Nat.eq_zero_or_pos f with hf | hf
  · -- `3^e = 2^a + 1` with `a ≥ 6`: then `3^e ≡ 1 (mod 64)`, so `16 ∣ e`, so `17 ∣ 2^a`.
    subst hf
    simp only [pow_zero, mul_one] at h
    have h64 : 3 ^ e % 64 = 1 := by
      have : 2 ^ 6 ∣ 2 ^ a := pow_dvd_of_le ha
      omega
    rw [pow_mod_cycle (k := 16) (by norm_num : 3 ^ 16 % 64 = 1)] at h64
    have he16 : e % 16 = 0 := by
      have key : ∀ r < 16, 3 ^ r % 64 = 1 → r = 0 := by decide
      exact key _ (Nat.mod_lt _ (by norm_num)) h64
    have h17 : 3 ^ e % 17 = 1 := by
      rw [pow_mod_cycle (k := 16) (by norm_num : 3 ^ 16 % 17 = 1), he16]; norm_num
    have : 17 ∣ 2 ^ a := by omega
    exact (not_dvd_of_coprime (by norm_num) (Nat.Coprime.pow_right a (by norm_num)) this).elim
  · -- `f ≥ 2` (even): `2^a ≡ -1 (mod 25)`, so `a ≡ 10 (mod 20)`, so `41 ∣ 3^e 5^f`.
    have h25 : 2 ^ a % 25 = 24 := by
      have : 25 ∣ 3 ^ e * 5 ^ f :=
        Dvd.dvd.mul_left (by simpa using (pow_dvd_of_le (p := 5) (show 2 ≤ f by omega))) _
      omega
    rw [pow_mod_cycle (k := 20) (by norm_num : 2 ^ 20 % 25 = 1)] at h25
    have ha20 : a % 20 = 10 := by
      have key : ∀ r < 20, 2 ^ r % 25 = 24 → r = 10 := by decide
      exact key _ (Nat.mod_lt _ (by norm_num)) h25
    have h41 : 2 ^ a % 41 = 40 := by
      rw [pow_mod_cycle (k := 20) (by norm_num : 2 ^ 20 % 41 = 1), ha20]; norm_num
    have : 41 ∣ 3 ^ e * 5 ^ f := by omega
    exact (not_dvd_of_coprime (by norm_num) (coprime_pp (by norm_num) (by norm_num) e f) this).elim

/-- `2^a 5^c + 1 = 3^e`: only `2 + 1 = 3`, `8 + 1 = 9`, `80 + 1 = 81`. -/
lemma eq_E_plus {a c e : ℕ} (h : 2 ^ a * 5 ^ c + 1 = 3 ^ e) :
    2 ^ a * 5 ^ c = 2 ∨ 2 ^ a * 5 ^ c = 8 ∨ 2 ^ a * 5 ^ c = 80 := by
  have ha : a < 6 := by
    by_contra ha
    push_neg at ha
    have h64 : 3 ^ e % 64 = 1 := by
      have : 2 ^ 6 ∣ 2 ^ a * 5 ^ c := Dvd.dvd.mul_right (pow_dvd_of_le ha) _
      omega
    rw [pow_mod_cycle (k := 16) (by norm_num : 3 ^ 16 % 64 = 1)] at h64
    have he16 : e % 16 = 0 := by
      have key : ∀ r < 16, 3 ^ r % 64 = 1 → r = 0 := by decide
      exact key _ (Nat.mod_lt _ (by norm_num)) h64
    have h17 : 3 ^ e % 17 = 1 := by
      rw [pow_mod_cycle (k := 16) (by norm_num : 3 ^ 16 % 17 = 1), he16]; norm_num
    have : 17 ∣ 2 ^ a * 5 ^ c := by omega
    exact not_dvd_of_coprime (by norm_num) (coprime_pp (by norm_num) (by norm_num) a c) this
  have hc : c < 2 := by
    by_contra hc
    push_neg at hc
    have h25 : 3 ^ e % 25 = 1 := by
      have : 5 ^ 2 ∣ 2 ^ a * 5 ^ c := Dvd.dvd.mul_left (pow_dvd_of_le hc) _
      omega
    rw [pow_mod_cycle (k := 20) (by norm_num : 3 ^ 20 % 25 = 1)] at h25
    have he20 : e % 20 = 0 := by
      have key : ∀ r < 20, 3 ^ r % 25 = 1 → r = 0 := by decide
      exact key _ (Nat.mod_lt _ (by norm_num)) h25
    have h11 : 3 ^ e % 11 = 1 := by
      rw [pow_mod_cycle (k := 5) (by norm_num : 3 ^ 5 % 11 = 1)]
      have : e % 5 = 0 := by omega
      rw [this]; norm_num
    have : 11 ∣ 2 ^ a * 5 ^ c := by omega
    exact not_dvd_of_coprime (by norm_num) (coprime_pp (by norm_num) (by norm_num) a c) this
  have he : e < 5 := by
    by_contra he
    have : 3 ^ 5 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ a * 5 ^ c ≤ 2 ^ 5 * 5 ^ 1 := Nat.mul_le_mul
      (Nat.pow_le_pow_right (by norm_num) (by omega)) (Nat.pow_le_pow_right (by norm_num) (by omega))
    norm_num at *; omega
  interval_cases a <;> interval_cases c <;> interval_cases e <;> simp_all

/-- `3^b + 1 = 2^d 5^f`: only `1 + 1 = 2`, `3 + 1 = 4`, `9 + 1 = 10`. -/
lemma eq_E_minus {b d f : ℕ} (h : 3 ^ b + 1 = 2 ^ d * 5 ^ f) :
    3 ^ b = 1 ∨ 3 ^ b = 3 ∨ 3 ^ b = 9 := by
  have hd : d < 3 := by
    by_contra hd
    push_neg at hd
    have h8 : 3 ^ b % 8 = 7 := by
      have : 2 ^ 3 ∣ 2 ^ d * 5 ^ f := Dvd.dvd.mul_right (pow_dvd_of_le hd) _
      omega
    rw [pow_mod_cycle (k := 2) (by norm_num : 3 ^ 2 % 8 = 1)] at h8
    have key : ∀ r < 2, 3 ^ r % 8 ≠ 7 := by decide
    exact key _ (Nat.mod_lt _ (by norm_num)) h8
  have hf : f < 2 := by
    by_contra hf
    push_neg at hf
    have h25 : 3 ^ b % 25 = 24 := by
      have : 5 ^ 2 ∣ 2 ^ d * 5 ^ f := Dvd.dvd.mul_left (pow_dvd_of_le hf) _
      omega
    rw [pow_mod_cycle (k := 20) (by norm_num : 3 ^ 20 % 25 = 1)] at h25
    have hb20 : b % 20 = 10 := by
      have key : ∀ r < 20, 3 ^ r % 25 = 24 → r = 10 := by decide
      exact key _ (Nat.mod_lt _ (by norm_num)) h25
    have h1181 : 3 ^ b % 1181 = 1180 := by
      rw [pow_mod_cycle (k := 20) (by norm_num : 3 ^ 20 % 1181 = 1), hb20]; norm_num
    have : 1181 ∣ 2 ^ d * 5 ^ f := by omega
    exact not_dvd_of_coprime (by norm_num) (coprime_pp (by norm_num) (by norm_num) d f) this
  have hb : b < 3 := by
    by_contra hb
    have : 3 ^ 3 ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ d * 5 ^ f ≤ 2 ^ 2 * 5 ^ 1 := Nat.mul_le_mul
      (Nat.pow_le_pow_right (by norm_num) (by omega)) (Nat.pow_le_pow_right (by norm_num) (by omega))
    norm_num at *; omega
  interval_cases b <;> simp

/-- `2^a 3^b + 1 = 5^f`: only `4 + 1 = 5`, `24 + 1 = 25`. -/
lemma eq_F_plus {a b f : ℕ} (h : 2 ^ a * 3 ^ b + 1 = 5 ^ f) :
    2 ^ a * 3 ^ b = 4 ∨ 2 ^ a * 3 ^ b = 24 := by
  have ha : a < 6 := by
    by_contra ha
    push_neg at ha
    have h64 : 5 ^ f % 64 = 1 := by
      have : 2 ^ 6 ∣ 2 ^ a * 3 ^ b := Dvd.dvd.mul_right (pow_dvd_of_le ha) _
      omega
    rw [pow_mod_cycle (k := 16) (by norm_num : 5 ^ 16 % 64 = 1)] at h64
    have hf16 : f % 16 = 0 := by
      have key : ∀ r < 16, 5 ^ r % 64 = 1 → r = 0 := by decide
      exact key _ (Nat.mod_lt _ (by norm_num)) h64
    have h17 : 5 ^ f % 17 = 1 := by
      rw [pow_mod_cycle (k := 16) (by norm_num : 5 ^ 16 % 17 = 1), hf16]; norm_num
    have : 17 ∣ 2 ^ a * 3 ^ b := by omega
    exact not_dvd_of_coprime (by norm_num) (coprime_pp (by norm_num) (by norm_num) a b) this
  have hb : b < 2 := by
    by_contra hb
    push_neg at hb
    have h9 : 5 ^ f % 9 = 1 := by
      have : 3 ^ 2 ∣ 2 ^ a * 3 ^ b := Dvd.dvd.mul_left (pow_dvd_of_le hb) _
      omega
    rw [pow_mod_cycle (k := 6) (by norm_num : 5 ^ 6 % 9 = 1)] at h9
    have hf6 : f % 6 = 0 := by
      have key : ∀ r < 6, 5 ^ r % 9 = 1 → r = 0 := by decide
      exact key _ (Nat.mod_lt _ (by norm_num)) h9
    have h7 : 5 ^ f % 7 = 1 := by
      rw [pow_mod_cycle (k := 6) (by norm_num : 5 ^ 6 % 7 = 1), hf6]; norm_num
    have : 7 ∣ 2 ^ a * 3 ^ b := by omega
    exact not_dvd_of_coprime (by norm_num) (coprime_pp (by norm_num) (by norm_num) a b) this
  have hf : f < 3 := by
    by_contra hf
    have : 5 ^ 3 ≤ 5 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ a * 3 ^ b ≤ 2 ^ 5 * 3 ^ 1 := Nat.mul_le_mul
      (Nat.pow_le_pow_right (by norm_num) (by omega)) (Nat.pow_le_pow_right (by norm_num) (by omega))
    norm_num at *; omega
  interval_cases a <;> interval_cases b <;> interval_cases f <;> simp_all

/-- `5^c + 1 = 2^d 3^e`: only `1 + 1 = 2`, `5 + 1 = 6`. -/
lemma eq_F_minus {c d e : ℕ} (h : 5 ^ c + 1 = 2 ^ d * 3 ^ e) :
    5 ^ c = 1 ∨ 5 ^ c = 5 := by
  have hd : d < 2 := by
    by_contra hd
    push_neg at hd
    have h4 : 5 ^ c % 4 = 3 := by
      have : 2 ^ 2 ∣ 2 ^ d * 3 ^ e := Dvd.dvd.mul_right (pow_dvd_of_le hd) _
      omega
    rw [Nat.pow_mod] at h4
    norm_num at h4
  have he : e < 2 := by
    by_contra he
    push_neg at he
    have h9 : 5 ^ c % 9 = 8 := by
      have : 3 ^ 2 ∣ 2 ^ d * 3 ^ e := Dvd.dvd.mul_left (pow_dvd_of_le he) _
      omega
    rw [pow_mod_cycle (k := 6) (by norm_num : 5 ^ 6 % 9 = 1)] at h9
    have hc6 : c % 6 = 3 := by
      have key : ∀ r < 6, 5 ^ r % 9 = 8 → r = 3 := by decide
      exact key _ (Nat.mod_lt _ (by norm_num)) h9
    have h7 : 5 ^ c % 7 = 6 := by
      rw [pow_mod_cycle (k := 6) (by norm_num : 5 ^ 6 % 7 = 1), hc6]; norm_num
    have : 7 ∣ 2 ^ d * 3 ^ e := by omega
    exact not_dvd_of_coprime (by norm_num) (coprime_pp (by norm_num) (by norm_num) d e) this
  have hc : c < 2 := by
    by_contra hc
    have : 5 ^ 2 ≤ 5 ^ c := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ d * 3 ^ e ≤ 2 ^ 1 * 3 ^ 1 := Nat.mul_le_mul
      (Nat.pow_le_pow_right (by norm_num) (by omega)) (Nat.pow_le_pow_right (by norm_num) (by omega))
    norm_num at *; omega
  interval_cases c <;> simp

/-! ### Størmer's theorem for `{2, 3, 5}` -/

/-- The ten values `m` with `m` and `m + 1` both 5-smooth. -/
def consecutiveSmoothStarts : Finset ℕ := {1, 2, 3, 4, 5, 8, 9, 15, 24, 80}

lemma two_not_dvd_both {m : ℕ} (h1 : 2 ∣ m) (h2 : 2 ∣ m + 1) : False := by omega

/-- **Størmer's theorem for `{2,3,5}`.**  If `m` and `m + 1` are both 5-smooth then
`m ∈ {1, 2, 3, 4, 5, 8, 9, 15, 24, 80}`; conversely all ten work. -/
theorem consecutive_smooth (m : ℕ) :
    (Smooth5 m ∧ Smooth5 (m + 1)) ↔ m ∈ consecutiveSmoothStarts := by
  constructor
  · rintro ⟨⟨a, b, c, hm⟩, ⟨d, e, f, hm1⟩⟩
    have hmpos : 0 < m := by rw [hm]; positivity
    -- each prime divides at most one of `m`, `m + 1`
    have k2 : a = 0 ∨ d = 0 := by
      by_contra hc; push_neg at hc
      have : 2 ∣ m := hm ▸ Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow_self 2 hc.1) _) _
      have : 2 ∣ m + 1 := hm1 ▸ Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow_self 2 hc.2) _) _
      omega
    have k3 : b = 0 ∨ e = 0 := by
      by_contra hc; push_neg at hc
      have : 3 ∣ m := hm ▸ Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self 3 hc.1) _) _
      have : 3 ∣ m + 1 := hm1 ▸ Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self 3 hc.2) _) _
      omega
    have k5 : c = 0 ∨ f = 0 := by
      by_contra hc; push_neg at hc
      have : 5 ∣ m := hm ▸ Dvd.dvd.mul_left (dvd_pow_self 5 hc.1) _
      have : 5 ∣ m + 1 := hm1 ▸ Dvd.dvd.mul_left (dvd_pow_self 5 hc.2) _
      omega
    simp only [consecutiveSmoothStarts, Finset.mem_insert, Finset.mem_singleton]
    rcases k2 with rfl | rfl <;> rcases k3 with rfl | rfl <;> rcases k5 with rfl | rfl <;>
      simp only [pow_zero, one_mul, mul_one] at hm hm1
    · omega
    · -- m = 5^c, m + 1 = 2^d 3^e
      rcases eq_F_minus (c := c) (d := d) (e := e) (by rw [← hm, ← hm1]) with h | h <;> omega
    · -- m = 3^b, m + 1 = 2^d 5^f
      rcases eq_E_minus (b := b) (d := d) (f := f) (by rw [← hm, ← hm1]) with h | h | h <;> omega
    · -- m = 3^b 5^c, m + 1 = 2^d
      rcases eq_D_plus (b := b) (c := c) (d := d) (by rw [← hm, ← hm1]) with h | h | h <;> omega
    · -- m = 2^a, m + 1 = 3^e 5^f
      rcases eq_D_minus (a := a) (e := e) (f := f) (by rw [← hm, ← hm1]) with h | h | h <;> omega
    · -- m = 2^a 5^c, m + 1 = 3^e
      rcases eq_E_plus (a := a) (c := c) (e := e) (by rw [← hm, ← hm1]) with h | h | h <;> omega
    · -- m = 2^a 3^b, m + 1 = 5^f
      rcases eq_F_plus (a := a) (b := b) (f := f) (by rw [← hm, ← hm1]) with h | h <;> omega
    · -- m + 1 = 1
      omega
  · intro hm
    simp only [consecutiveSmoothStarts, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨0, 0, 0, rfl⟩, ⟨1, 0, 0, rfl⟩⟩
    · exact ⟨⟨1, 0, 0, rfl⟩, ⟨0, 1, 0, rfl⟩⟩
    · exact ⟨⟨0, 1, 0, rfl⟩, ⟨2, 0, 0, rfl⟩⟩
    · exact ⟨⟨2, 0, 0, rfl⟩, ⟨0, 0, 1, rfl⟩⟩
    · exact ⟨⟨0, 0, 1, rfl⟩, ⟨1, 1, 0, rfl⟩⟩
    · exact ⟨⟨3, 0, 0, rfl⟩, ⟨0, 2, 0, rfl⟩⟩
    · exact ⟨⟨0, 2, 0, rfl⟩, ⟨1, 0, 1, rfl⟩⟩
    · exact ⟨⟨0, 1, 1, rfl⟩, ⟨4, 0, 0, rfl⟩⟩
    · exact ⟨⟨3, 1, 0, rfl⟩, ⟨0, 0, 2, rfl⟩⟩
    · exact ⟨⟨4, 0, 1, rfl⟩, ⟨0, 4, 0, rfl⟩⟩

/-- **5-limit superparticular ratios.**  A ratio `(m+1)/m` whose numerator and denominator are
both 5-smooth (a "5-limit" superparticular interval) is one of
`2/1, 3/2, 4/3, 5/4, 6/5, 9/8, 10/9, 16/15, 25/24, 81/80`.  The smallest, `81/80`, is the
syntonic comma. -/
theorem superparticular_five_limit (m : ℕ) (h1 : Smooth5 m) (h2 : Smooth5 (m + 1)) :
    ((m + 1 : ℚ) / m) ∈ ({2, 3/2, 4/3, 5/4, 6/5, 9/8, 10/9, 16/15, 25/24, 81/80} : Set ℚ) := by
  have := (consecutive_smooth m).1 ⟨h1, h2⟩
  simp only [consecutiveSmoothStarts, Finset.mem_insert, Finset.mem_singleton] at this
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-! ### The dual-smooth prime census, without a bound -/

/-- The dual-smooth primes of `THESIS.md` (BG-020/BG-023/XP-DT-036). -/
def dualSmoothPrimes : Finset ℕ := {2, 3, 5, 7, 11, 17, 19, 31}

lemma smooth5_of_two_mul {k : ℕ} (h : Smooth5 (2 * k)) : Smooth5 k := by
  obtain ⟨a, b, c, hk⟩ := h
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exfalso
    have hodd : ¬ 2 ∣ 3 ^ b * 5 ^ c :=
      not_dvd_of_coprime (by norm_num) (coprime_pp (by norm_num) (by norm_num) b c)
    exact hodd ⟨k, by simpa using hk.symm⟩
  · refine ⟨a - 1, b, c, ?_⟩
    have : 2 ^ a = 2 * 2 ^ (a - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this] at hk
    have : 2 * k = 2 * (2 ^ (a - 1) * 3 ^ b * 5 ^ c) := by rw [hk]; ring
    omega

/-- **Complete dual-smooth prime census.**  For a prime `p`, both `p - 1` and `p + 1` are
5-smooth if and only if `p ∈ {2, 3, 5, 7, 11, 17, 19, 31}`.  No search bound is involved. -/
theorem dual_smooth_prime_iff (p : ℕ) (hp : p.Prime) :
    (Smooth5 (p - 1) ∧ Smooth5 (p + 1)) ↔ p ∈ dualSmoothPrimes := by
  constructor
  · rintro ⟨h1, h2⟩
    rcases hp.eq_two_or_odd' with rfl | hodd
    · decide
    obtain ⟨k, hk⟩ := hodd
    have hk0 : 0 < k := by have := hp.two_le; omega
    have hA : Smooth5 k := smooth5_of_two_mul (by rw [show 2 * k = p - 1 by omega]; exact h1)
    have hB : Smooth5 (k + 1) :=
      smooth5_of_two_mul (by rw [show 2 * (k + 1) = p + 1 by omega]; exact h2)
    have hkmem := (consecutive_smooth k).1 ⟨hA, hB⟩
    simp only [consecutiveSmoothStarts, Finset.mem_insert, Finset.mem_singleton] at hkmem
    simp only [dualSmoothPrimes, Finset.mem_insert, Finset.mem_singleton]
    subst hk
    rcases hkmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (try norm_num at hp) <;> norm_num
  · intro h
    simp only [dualSmoothPrimes, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨0, 0, 0, rfl⟩, ⟨0, 1, 0, rfl⟩⟩
    · exact ⟨⟨1, 0, 0, rfl⟩, ⟨2, 0, 0, rfl⟩⟩
    · exact ⟨⟨2, 0, 0, rfl⟩, ⟨1, 1, 0, rfl⟩⟩
    · exact ⟨⟨1, 1, 0, rfl⟩, ⟨3, 0, 0, rfl⟩⟩
    · exact ⟨⟨1, 0, 1, rfl⟩, ⟨2, 1, 0, rfl⟩⟩
    · exact ⟨⟨4, 0, 0, rfl⟩, ⟨1, 2, 0, rfl⟩⟩
    · exact ⟨⟨1, 2, 0, rfl⟩, ⟨2, 0, 1, rfl⟩⟩
    · exact ⟨⟨1, 1, 1, rfl⟩, ⟨5, 0, 0, rfl⟩⟩

/-- `Smooth5` agrees with the prime-factor formulation (`0 < n` and every prime factor is
`2`, `3` or `5`). -/
theorem smooth5_iff (n : ℕ) :
    Smooth5 n ↔ 0 < n ∧ ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3 ∨ p = 5 := by
  constructor
  · rintro ⟨a, b, c, rfl⟩
    refine ⟨by positivity, fun p hp => ?_⟩
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hd := Nat.dvd_of_mem_primeFactors hp
    rcases (Nat.Prime.dvd_mul hp').1 hd with h | h
    · rcases (Nat.Prime.dvd_mul hp').1 h with h | h
      · left; exact (Nat.prime_dvd_prime_iff_eq hp' Nat.prime_two).1 (hp'.dvd_of_dvd_pow h)
      · right; left; exact (Nat.prime_dvd_prime_iff_eq hp' Nat.prime_three).1 (hp'.dvd_of_dvd_pow h)
    · right; right; exact (Nat.prime_dvd_prime_iff_eq hp' Nat.prime_five).1 (hp'.dvd_of_dvd_pow h)
  · rintro ⟨hn, hpf⟩
    refine ⟨n.factorization 2, n.factorization 3, n.factorization 5, ?_⟩
    have hsub : n.factorization.support ⊆ {2, 3, 5} := by
      intro p hp
      rw [Nat.support_factorization] at hp
      simpa using hpf p hp
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn.ne']
    rw [Finsupp.prod_of_support_subset _ hsub _ (fun _ _ => pow_zero _)]
    simp [mul_assoc]

end DualSmooth

end
