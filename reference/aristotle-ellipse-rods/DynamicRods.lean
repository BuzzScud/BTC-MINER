module

public import Mathlib
public import LatticeCalc.Rods

/-!
# Prime rods, the coprime window, and adding rods dynamically

This file works with the rod abacus `LatticeCalc.Abacus` of the library.  A number `x`
**passes** the abacus when its bead reading is nonzero on every rod.  Only the mathematics is
treated here; how a number is shown to a user or stored is a separate matter and plays no role.

* `passCount_snd`: checking `x` inspects each rod exactly once, so the number of rod checks is the
  number of rods, whatever `x` is.  `passCount_fst`: the checks compute `passes`.
* `least_coprime_prime`: for **any** modulus `M`, the least `m > 1` coprime to `M` is a prime.
  So "the next rod chosen by coprimality" is always a prime.
* The prime-rod abacus `primeRods r` has one rod for each prime below `r`.
  - `window` (any `r`): for `1 < x < r²`, `x` passes **iff** `x` is a prime `≥ r`.  Inside the volume `r²`
    the coprime positions *are* the next prime set.
  For a prime `r`:
  - `next_rod`: `r` is the least number `> 1` that passes, so the abacus itself names its next rod.
  - `window_sharp`: `r²` passes but is not prime; the volume `r²` cannot be enlarged.
  - `add_rod`: if `s` is the next prime after `r`, the abacus for `s` is the abacus for `r` with
    the single rod `r` appended; its window grows from `r²` to `s²`.
* `extend_pairwise`, `extend_capacity`, `extendEquiv`: appending a rod coprime to the capacity
  keeps the rods pairwise coprime, multiplies the capacity, and splits the arithmetic as a ring
  isomorphism (Chinese remainder theorem), so old rods are untouched when a rod is added.
* Limits:
  - `no_finite_abacus`: no finite abacus decides primality for all `x > 1`;
  - `rods_needed`: an abacus (without a rod of size 1) that is correct on a window `[L, V)` has at
    least as many rods as there are primes `p` with `L ≤ p² < V`.  So the number of rods, a
    property of the abacus itself, must grow with the volume.
* `factor_on_rods`: for `n = p q` with `n < r²`, the smaller factor `p` is one of the rods and
  reads zero there.
* Example (`rods19`, `window19`, checked by the kernel): the seven rods `2, …, 17` pick out
  exactly the 65 primes in `[19, 361)`.
-/

@[expose] public section

namespace DynamicRods

open LatticeCalc

/-- `x` passes the abacus: its reading is nonzero on every rod. -/
def passes (A : Abacus) (x : ℕ) : Prop := ∀ m ∈ A.rods, x % m ≠ 0

instance (A : Abacus) : DecidablePred (passes A) := fun x =>
  inferInstanceAs (Decidable (∀ m ∈ A.rods, x % m ≠ 0))

/-- Rod-by-rod check that also counts the rod checks performed. -/
def passCount : List ℕ → ℕ → Bool × ℕ
  | [], _ => (true, 0)
  | m :: ms, x => ((x % m != 0) && (passCount ms x).1, (passCount ms x).2 + 1)

theorem passCount_fst (A : Abacus) (x : ℕ) : (passCount A.rods x).1 = decide (passes A x) := by
  have key : ∀ l : List ℕ, (passCount l x).1 = true ↔ ∀ m ∈ l, x % m ≠ 0 := by
    intro l
    induction l with
    | nil => simp [passCount]
    | cons m ms ih => simp [passCount, ih]
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact key _

/-- The number of rod checks equals the number of rods; it does not depend on `x`. -/
theorem passCount_snd (rods : List ℕ) (x : ℕ) : (passCount rods x).2 = rods.length := by
  induction rods with
  | nil => rfl
  | cons m ms ih => simp [passCount, ih]

/-- One rod for each prime below `r`. -/
def primeRods (r : ℕ) : Abacus := ⟨(List.range r).filter Nat.Prime⟩

theorem mem_primeRods {r m : ℕ} : m ∈ (primeRods r).rods ↔ m < r ∧ m.Prime := by
  simp [primeRods]

theorem primeRods_pairwise (r : ℕ) : (primeRods r).rods.Pairwise Nat.Coprime := by
  unfold primeRods
  refine List.Pairwise.imp_of_mem ?_ (List.Pairwise.filter _ (List.nodup_range))
  intro a b ha hb hab
  simp at ha hb
  exact (Nat.coprime_primes ha.2 hb.2).2 hab

theorem passes_primeRods {r x : ℕ} :
    passes (primeRods r) x ↔ ∀ m, m.Prime → m < r → x % m ≠ 0 := by
  simp only [passes, mem_primeRods]
  constructor
  · intro h m hm hmr; exact h m ⟨hmr, hm⟩
  · intro h m ⟨hmr, hm⟩; exact h m hm hmr

/-- The least `m > 1` coprime to `M` is prime, for every `M`. -/
theorem least_coprime_prime {M m : ℕ} (hm : 1 < m) (hc : Nat.Coprime m M)
    (hmin : ∀ j, 1 < j → j < m → ¬ Nat.Coprime j M) : m.Prime := by
  have hpm := Nat.minFac_prime (show m ≠ 1 by omega)
  have hc' : Nat.Coprime m.minFac M := Nat.Coprime.coprime_dvd_left (Nat.minFac_dvd m) hc
  have hle := Nat.minFac_le (show 0 < m by omega)
  have heq : m.minFac = m := by
    by_contra hne
    exact hmin _ hpm.one_lt (lt_of_le_of_ne hle hne) hc'
  rw [← heq]; exact hpm

/-- **The window.**  Inside the volume `r²`, the numbers that pass the prime-rod abacus are
exactly the primes from `r` on. -/
theorem window {r x : ℕ} (hx1 : 1 < x) (hx : x < r * r) :
    passes (primeRods r) x ↔ x.Prime ∧ r ≤ x := by
  rw [passes_primeRods]
  constructor
  · intro h
    have hmp := Nat.minFac_prime (show x ≠ 1 by omega)
    have hrm : r ≤ x.minFac := by
      by_contra hlt
      push_neg at hlt
      exact h _ hmp hlt (Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd x))
    have hxp : x.Prime := by
      by_contra hnp
      have := Nat.minFac_sq_le_self (show 0 < x by omega) hnp
      nlinarith
    exact ⟨hxp, hrm.trans (Nat.minFac_le (by omega))⟩
  · rintro ⟨hxp, hrx⟩ m hm hmr h0
    rcases hxp.eq_one_or_self_of_dvd m (Nat.dvd_of_mod_eq_zero h0) with h | h
    · exact hm.one_lt.ne' h
    · omega

/-- The abacus names its own next rod: `r` is the least number `> 1` that passes. -/
theorem next_rod {r : ℕ} (hr : r.Prime) :
    passes (primeRods r) r ∧ ∀ j, 1 < j → j < r → ¬ passes (primeRods r) j := by
  have h2 := hr.two_le
  refine ⟨(window hr.one_lt (by nlinarith)).2 ⟨hr, le_rfl⟩, fun j hj hjr hp => ?_⟩
  have := ((window hj (by nlinarith)).1 hp).2
  omega

/-- The window is sharp: `r²` passes but is not prime. -/
theorem window_sharp {r : ℕ} (hr : r.Prime) : passes (primeRods r) (r * r) ∧ ¬ (r * r).Prime := by
  refine ⟨?_, Nat.not_prime_mul hr.ne_one hr.ne_one⟩
  rw [passes_primeRods]
  intro m hm hmr h0
  have hd := Nat.dvd_of_mod_eq_zero h0
  rcases (Nat.Prime.dvd_mul hm).1 hd with h | h <;>
  · rcases hr.eq_one_or_self_of_dvd m h with h' | h'
    · exact hm.one_lt.ne' h'
    · omega

/-- **Adding the next rod.**  If `s` is the next prime after `r`, the abacus for `s` is the
abacus for `r` with the rod `r` appended. -/
theorem add_rod {r s : ℕ} (hr : r.Prime) (hrs : r < s) (hgap : ∀ t, r < t → t < s → ¬ t.Prime) :
    (primeRods s).rods = (primeRods r).rods ++ [r] := by
  unfold primeRods
  simp only
  have key : ∀ k, r + 1 ≤ k → k ≤ s →
      (List.range k).filter Nat.Prime = (List.range r).filter Nat.Prime ++ [r] := by
    intro k hk hks
    induction k, hk using Nat.le_induction with
    | base => simp [List.range_succ, List.filter_append, hr]
    | succ k hk ih =>
      rw [List.range_succ, List.filter_append, ih (by omega)]
      have : ¬ k.Prime := hgap k (by omega) (by omega)
      simp [this]
  exact key s (by omega) le_rfl

/-- Append a rod. -/
def extend (A : Abacus) (p : ℕ) : Abacus := ⟨A.rods ++ [p]⟩

theorem extend_pairwise {A : Abacus} {p : ℕ} (hA : A.rods.Pairwise Nat.Coprime)
    (hp : Nat.Coprime A.capacity p) : (extend A p).rods.Pairwise Nat.Coprime := by
  unfold extend
  simp only
  rw [List.pairwise_append]
  refine ⟨hA, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
  rw [List.mem_singleton] at hb
  subst hb
  exact Nat.Coprime.coprime_dvd_left (List.dvd_prod ha) hp

theorem extend_capacity (A : Abacus) (p : ℕ) : (extend A p).capacity = A.capacity * p := by
  simp [extend, Abacus.capacity]

/-- Adding a rod coprime to the capacity splits the arithmetic into the old abacus and the new
rod (Chinese remainder theorem). -/
def extendEquiv (A : Abacus) (p : ℕ) (hp : Nat.Coprime A.capacity p) :
    ZMod (extend A p).capacity ≃+* ZMod A.capacity × ZMod p :=
  (ZMod.ringEquivCongr (extend_capacity A p)).trans (ZMod.chineseRemainder hp)

/-- The divisors of `p²` for a prime `p`. -/
theorem dvd_sq_prime {p m : ℕ} (hp : p.Prime) (h : m ∣ p * p) : m = 1 ∨ m = p ∨ m = p * p := by
  rw [← pow_two] at h
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 h
  interval_cases i <;> simp [pow_two]

/-- No finite abacus decides primality for every `x > 1`. -/
theorem no_finite_abacus (A : Abacus) : ∃ x, 1 < x ∧ (passes A x ↔ ¬ x.Prime) := by
  by_cases h1 : 1 ∈ A.rods
  · refine ⟨2, by norm_num, ?_⟩
    simp only [Nat.prime_two, not_true_eq_false, iff_false]
    intro h
    exact h 1 h1 (by norm_num)
  · obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (A.rods.sum + 1)
    refine ⟨p * p, by nlinarith [hp.two_le], ?_⟩
    simp only [Nat.not_prime_mul hp.ne_one hp.ne_one, not_false_eq_true, iff_true]
    intro m hm h0
    have hle : m ≤ A.rods.sum := List.le_sum_of_mem hm
    rcases dvd_sq_prime hp (Nat.dvd_of_mod_eq_zero h0) with h | h | h
    · exact h1 (h ▸ hm)
    · omega
    · nlinarith [hp.two_le]

/-- **Rods needed.**  An abacus without a rod of size `1` that is correct on `[L, V)` has at least
as many rods as there are primes `p` with `L ≤ p² < V`. -/
theorem rods_needed (A : Abacus) (h1 : 1 ∉ A.rods) {L V : ℕ}
    (hcorrect : ∀ x, L ≤ x → x < V → (passes A x ↔ x.Prime)) :
    ((Finset.range V).filter (fun p => p.Prime ∧ L ≤ p * p ∧ p * p < V)).card ≤
      A.rods.length := by
  classical
  set S := (Finset.range V).filter (fun p => p.Prime ∧ L ≤ p * p ∧ p * p < V)
  let f : ℕ → ℕ := fun p => if p ∈ A.rods then p else p * p
  have hmaps : ∀ p ∈ S, f p ∈ A.rods.toFinset := by
    intro p hpS
    simp only [S, Finset.mem_filter] at hpS
    obtain ⟨_, hp, hL, hV⟩ := hpS
    have hnp : ¬ passes A (p * p) := fun hpass =>
      Nat.not_prime_mul hp.ne_one hp.ne_one ((hcorrect _ hL hV).1 hpass)
    simp only [passes, not_forall, not_not] at hnp
    obtain ⟨m, hm, h0⟩ := hnp
    rw [List.mem_toFinset]
    rcases dvd_sq_prime hp (Nat.dvd_of_mod_eq_zero h0) with h | h | h
    · exact absurd (h ▸ hm) h1
    · simp only [f, if_pos (h ▸ hm)]; exact h ▸ hm
    · by_cases hpr : p ∈ A.rods
      · simp only [f, if_pos hpr]; exact hpr
      · simp only [f, if_neg hpr]; exact h ▸ hm
  have hinj : Set.InjOn f S := by
    intro p hpS p' hpS' hff
    simp only [S, Finset.coe_filter, Set.mem_setOf_eq] at hpS hpS'
    have hp := hpS.2.1
    have hp' := hpS'.2.1
    simp only [f] at hff
    split_ifs at hff with ha hb hb
    · exact hff
    · exact absurd (hff ▸ hp) (Nat.not_prime_mul hp'.ne_one hp'.ne_one)
    · exact absurd (hff.symm ▸ hp') (Nat.not_prime_mul hp.ne_one hp.ne_one)
    · exact Nat.mul_self_inj.1 hff
  calc S.card ≤ A.rods.toFinset.card := Finset.card_le_card_of_injOn f hmaps hinj
    _ ≤ A.rods.length := List.toFinset_card_le _

/-- For `n = p q < r²` with primes `p ≤ q`, the factor `p` is a rod of `primeRods r` and `n`
reads zero on it. -/
theorem factor_on_rods {p q r : ℕ} (hp : p.Prime) (hpq : p ≤ q) (hn : p * q < r * r) :
    p ∈ (primeRods r).rods ∧ (p * q) % p = 0 := by
  refine ⟨mem_primeRods.2 ⟨?_, hp⟩, Nat.mul_mod_right p q⟩
  have : p * p < r * r := lt_of_le_of_lt (Nat.mul_le_mul_left p hpq) hn
  exact Nat.mul_self_lt_mul_self_iff.1 this

/-- The abacus for `r = 19` has the seven rods `2, 3, 5, 7, 11, 13, 17`. -/
theorem rods19 : (primeRods 19).rods = [2, 3, 5, 7, 11, 13, 17] := by decide +kernel

/-- On `[19, 361)`, the numbers passing those seven rods are exactly the primes (65 of them). -/
theorem window19 : ((List.range' 19 342).filter (fun x => decide (passes (primeRods 19) x))) =
    (List.range' 19 342).filter Nat.Prime := by decide +kernel

end DynamicRods
