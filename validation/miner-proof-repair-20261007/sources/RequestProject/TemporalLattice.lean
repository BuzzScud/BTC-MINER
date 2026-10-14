module

public import Mathlib
public import RequestProject.DualSmooth

/-!
# The temporal-layer family as a divisor lattice (`THESIS.md` §6, §10, §12; BG-003, BG-012,
BG-016, BG-022, BG-030, BG-031; XP-DT-002..005, XP-DT-020, XP-SQ-026, XP-SQ-027)

`THESIS.md` records a number of *finite audits* over the temporal layers
`(7200, 14400, 28800, 36000, 72000, 144000)`.  Here the same facts are proved as statements
about **all** natural numbers, and the reason behind each audit is made explicit:

* the layers are the divisor lattice `2^{5,6,7} · 3^2 · 5^{2,3}`; "divides every layer" means
  "divides `7200`", "divides some layer" means "divides `144000`" (`dvd_some_layer_iff`);
* the number of layers hit by any `d` is always one of `0, 1, 2, 3, 4, 6` — never `5`
  (`hits_mem`); this is why the observed multiplicities in BG-030 are `{6, 4, 3, 2, 1}`;
* a multiplier with a prime factor `≥ 7` hits no layer (`no_hit_of_large_prime_factor`); this is
  the general reason behind the BG-003 audit ("no audited prime-family multiplier closes");
* the qualifying-prime set of XP-DT-003 is exactly the 35 primes listed in `qualifyingPrimes`,
  with **no search bound** (`qualifies_iff`); the 5-smoothness condition in its definition is
  automatic (`smooth_of_dvd_144000`);
* a pair `p, p + 2` has both squares `≡ 1 (mod 360)` iff `p ≡ 89 (mod 90)`
  (`twin_kissing_iff`), which explains the twin pairs `(179, 181)`, `(269, 271)` of XP-SQ-027.
-/

@[expose] public section

namespace TemporalLattice

open DualSmooth

/-- The temporal layers. -/
def layers : List ℕ := [7200, 14400, 28800, 36000, 72000, 144000]

/-- Number of layers divisible by `d` (the "temporal hit function"). -/
def hits (d : ℕ) : ℕ := (layers.filter (fun L => d ∣ L)).length

lemma layer_dvd_144000 : ∀ L ∈ layers, L ∣ 144000 := by decide

lemma dvd_7200_of_mem : ∀ L ∈ layers, 7200 ∣ L := by decide

/-- "Divides some layer" is the same as "divides `144000`". -/
theorem dvd_some_layer_iff (d : ℕ) : (∃ L ∈ layers, d ∣ L) ↔ d ∣ 144000 := by
  constructor
  · rintro ⟨L, hL, hd⟩; exact hd.trans (layer_dvd_144000 L hL)
  · intro h; exact ⟨144000, by decide, h⟩

/-- "Divides every layer" is the same as "divides `7200`". -/
theorem dvd_all_layers_iff (d : ℕ) : (∀ L ∈ layers, d ∣ L) ↔ d ∣ 7200 := by
  constructor
  · intro h; exact h 7200 (by decide)
  · intro h L hL; exact h.trans (dvd_7200_of_mem L hL)

/-- Every divisor of `144000 = 2^7 3^2 5^3` has the form `2^i 3^j 5^k` with `i ≤ 7, j ≤ 2, k ≤ 3`. -/
lemma dvd_144000_iff (d : ℕ) :
    d ∣ 144000 ↔ ∃ i ≤ 7, ∃ j ≤ 2, ∃ k ≤ 3, d = 2 ^ i * 3 ^ j * 5 ^ k := by
  constructor
  · intro h
    rw [show (144000 : ℕ) = 2 ^ 7 * 3 ^ 2 * 5 ^ 3 by norm_num] at h
    obtain ⟨d1, d2, h1, h2, rfl⟩ := Nat.dvd_mul.1 h
    obtain ⟨e1, e2, h11, h12, rfl⟩ := Nat.dvd_mul.1 h1
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h11
    obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h12
    obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 h2
    exact ⟨i, hi, j, hj, k, hk, rfl⟩
  · rintro ⟨i, hi, j, hj, k, hk, rfl⟩
    rw [show (144000 : ℕ) = 2 ^ 7 * 3 ^ 2 * 5 ^ 3 by norm_num]
    exact Nat.mul_dvd_mul (Nat.mul_dvd_mul (pow_dvd_pow _ hi) (pow_dvd_pow _ hj)) (pow_dvd_pow _ hk)

/-- A divisor of `144000` is automatically 5-smooth. -/
theorem smooth_of_dvd_144000 {d : ℕ} (h : d ∣ 144000) : Smooth5 d := by
  obtain ⟨i, -, j, -, k, -, rfl⟩ := (dvd_144000_iff d).1 h
  exact ⟨i, j, k, rfl⟩

lemma hits_eq_zero_of_not_dvd {d : ℕ} (h : ¬ d ∣ 144000) : hits d = 0 := by
  unfold hits
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro L hL hd
  exact h ((decide_eq_true_iff.1 hd).trans (layer_dvd_144000 L hL))

lemma hits_smooth_table : ∀ i ≤ 7, ∀ j ≤ 2, ∀ k ≤ 3,
    hits (2 ^ i * 3 ^ j * 5 ^ k) ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  unfold hits layers; decide

/-- **The hit count is never `5`.**  For every `d`, the number of temporal layers divisible by
`d` is one of `0, 1, 2, 3, 4, 6`.  (The layers form the product poset `{5,6,7} × {2,3}` of
exponents of `2` and `5`, so a hit set is a product of an up-set of sizes `1,2,3` and one of
sizes `1,2`.) -/
theorem hits_mem (d : ℕ) : hits d ∈ ({0, 1, 2, 3, 4, 6} : Finset ℕ) := by
  by_cases h : d ∣ 144000
  · obtain ⟨i, hi, j, hj, k, hk, rfl⟩ := (dvd_144000_iff d).1 h
    have := hits_smooth_table i hi j hj k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
    omega
  · rw [hits_eq_zero_of_not_dvd h]; simp

/-- Each of the values `1, 2, 3, 4, 6` is attained by a qualifying prime (`p - 1` for
`p = 16001, 641, 251, 193, 19`); `5` never is (`hits_mem`). -/
theorem hits_levels :
    hits 16000 = 1 ∧ hits 640 = 2 ∧ hits 250 = 3 ∧ hits 192 = 4 ∧ hits 18 = 6 := by
  unfold hits layers; decide

/-- **BG-003, generalised.**  A multiplier with a prime factor `q ≥ 7` divides no temporal
layer.  So no product of qualifying primes (all `≥ 7`) can achieve layer closure, whatever
family is audited. -/
theorem no_hit_of_large_prime_factor {m q : ℕ} (hq : q.Prime) (h7 : 7 ≤ q) (hqm : q ∣ m) :
    ∀ L ∈ layers, ¬ m ∣ L := by
  intro L hL hmL
  have h1 : q ∣ 144000 := hqm.trans (hmL.trans (layer_dvd_144000 L hL))
  rw [show (144000 : ℕ) = 2 ^ 7 * 3 ^ 2 * 5 ^ 3 by norm_num] at h1
  rcases (Nat.Prime.dvd_mul hq).1 h1 with h | h
  · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h); omega
    · have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 (hq.dvd_of_dvd_pow h); omega
  · have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).1 (hq.dvd_of_dvd_pow h); omega

/-- …while a multiplier closes on every layer exactly when it divides `7200`. -/
theorem closes_all_iff (m : ℕ) : (∀ L ∈ layers, m ∣ L) ↔ m ∣ 7200 := dvd_all_layers_iff m

/-! ### Qualifying primes (XP-DT-003, XP-DT-004, BG-012) -/

/-- XP-DT-003: `p` qualifies iff `p ≥ 7` is prime, `p - 1` is 5-smooth and `p - 1` divides at
least one temporal layer. -/
def Qualifies (p : ℕ) : Prop :=
  p.Prime ∧ 7 ≤ p ∧ Smooth5 (p - 1) ∧ ∃ L ∈ layers, (p - 1) ∣ L

/-- The 35 qualifying primes. -/
def qualifyingPrimes : Finset ℕ :=
  {7, 11, 13, 17, 19, 31, 37, 41, 61, 73, 97, 101, 151, 181, 193, 241, 251, 401, 577, 601, 641,
    751, 1153, 1201, 1601, 1801, 2251, 3001, 4001, 4801, 9001, 9601, 14401, 16001, 24001}

theorem qualifyingPrimes_card : qualifyingPrimes.card = 35 := by decide

lemma qualifies_iff_aux (p : ℕ) : Qualifies p ↔ p.Prime ∧ 7 ≤ p ∧ (p - 1) ∣ 144000 := by
  unfold Qualifies
  rw [dvd_some_layer_iff]
  constructor
  · rintro ⟨h1, h2, -, h4⟩; exact ⟨h1, h2, h4⟩
  · rintro ⟨h1, h2, h4⟩; exact ⟨h1, h2, smooth_of_dvd_144000 h4, h4⟩

lemma qualifying_table : ∀ i ≤ 7, ∀ j ≤ 2, ∀ k ≤ 3,
    ((2 ^ i * 3 ^ j * 5 ^ k + 1).Prime ∧ 7 ≤ 2 ^ i * 3 ^ j * 5 ^ k + 1) ↔
      2 ^ i * 3 ^ j * 5 ^ k + 1 ∈ qualifyingPrimes := by
  intro i hi j hj k hk
  have key : ∀ n : ℕ, n ∈ qualifyingPrimes ↔ n ∈ qualifyingPrimes.val := fun _ => Iff.rfl
  interval_cases i <;> interval_cases j <;> interval_cases k <;> rw [key] <;> norm_num <;> decide

lemma qualifyingPrimes_spec : ∀ p ∈ qualifyingPrimes, p.Prime ∧ 7 ≤ p ∧ (p - 1) ∣ 144000 := by
  intro p hp
  simp only [qualifyingPrimes, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- **The qualifying-prime set is exactly the 35 listed primes — with no search bound.**
In particular every qualifying prime is at most `24001`, so the audits "up to 24001" and
"up to 144003" of BG-012 are already complete. -/
theorem qualifies_iff (p : ℕ) : Qualifies p ↔ p ∈ qualifyingPrimes := by
  rw [qualifies_iff_aux]
  constructor
  · rintro ⟨hp, h7, hd⟩
    obtain ⟨i, hi, j, hj, k, hk, he⟩ := (dvd_144000_iff (p - 1)).1 hd
    have hp' : p = 2 ^ i * 3 ^ j * 5 ^ k + 1 := by omega
    subst hp'
    exact (qualifying_table i hi j hj k hk).1 ⟨hp, h7⟩
  · exact qualifyingPrimes_spec p

/-- Of the 35, exactly 19 hit all six layers (`p - 1 ∣ 7200`). -/
theorem full_coverage_count :
    (qualifyingPrimes.filter (fun p => (p - 1) ∣ 7200)).card = 19 := by decide

/-- BG-016/BG-030: distribution of the 35 qualifying primes by number of layers hit:
19 hit all six, 5 hit four, 6 hit three, 4 hit two, 1 (`16001`) hits one. -/
theorem hit_distribution :
    (qualifyingPrimes.filter (fun p => hits (p - 1) = 6)).card = 19 ∧
    (qualifyingPrimes.filter (fun p => hits (p - 1) = 4)).card = 5 ∧
    (qualifyingPrimes.filter (fun p => hits (p - 1) = 3)).card = 6 ∧
    (qualifyingPrimes.filter (fun p => hits (p - 1) = 2)).card = 4 ∧
    (qualifyingPrimes.filter (fun p => hits (p - 1) = 1)).card = 1 := by
  unfold hits layers; decide

/-- **The 19-anchor is local, not global.**  Over *all* primes, the two tests of BG-007
(`p² ≡ 1 (mod 360)` and `p - 1` divides every temporal layer) are passed exactly by
`19`, `181` and `1801`. -/
theorem boundary_anchor_global (p : ℕ) (hp : p.Prime) :
    (p ^ 2 % 360 = 1 ∧ (p - 1) ∣ 7200) ↔ p ∈ ({19, 181, 1801} : Finset ℕ) := by
  constructor
  · rintro ⟨h1, h2⟩
    by_cases h7 : p < 7
    · interval_cases p <;> simp_all (config := {decide := true})
    · have hq : Qualifies p := (qualifies_iff_aux p).2
        ⟨hp, by omega, h2.trans (by norm_num)⟩
      have hmem := (qualifies_iff p).1 hq
      have key : ∀ q ∈ qualifyingPrimes, (q ^ 2 % 360 = 1 ∧ (q - 1) ∣ 7200) →
          q ∈ ({19, 181, 1801} : Finset ℕ) := by decide
      exact key p hmem ⟨h1, h2⟩
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl <;> decide

/-- BG-031: the `p + 1` channel is not symmetric with the `p - 1` channel: `13 - 1 = 12` divides
every layer, while `13 + 1 = 14` divides none. -/
theorem asymmetry_13 : hits 12 = 6 ∧ hits 14 = 0 := by unfold hits layers; decide

/-! ### Kissing primes (`p^2 ≡ 1 (mod 360)`) -/

/-- `p² ≡ 1` and `(p+2)² ≡ 1 (mod 360)` hold together exactly when `p ≡ 89 (mod 90)`
(for every natural number `p`, prime or not). -/
theorem twin_kissing_iff (p : ℕ) :
    (p ^ 2 % 360 = 1 ∧ (p + 2) ^ 2 % 360 = 1) ↔ p % 90 = 89 := by
  have key : ∀ r < 360, ((r ^ 2 % 360 = 1 ∧ (r + 2) ^ 2 % 360 = 1) ↔ r % 90 = 89) := by
    decide +kernel
  have h1 : p ^ 2 % 360 = (p % 360) ^ 2 % 360 := Nat.pow_mod p 2 360
  have h2 : (p + 2) ^ 2 % 360 = ((p % 360) + 2) ^ 2 % 360 := by
    rw [Nat.pow_mod, Nat.add_mod]
    conv_rhs => rw [Nat.pow_mod, Nat.add_mod, Nat.mod_mod]
  have h3 : p % 90 = (p % 360) % 90 := by omega
  rw [h1, h2, h3]
  exact key _ (Nat.mod_lt _ (by norm_num))

/-- XP-SQ-026: the 14 primes below 500 with `p² ≡ 1 (mod 360)`. -/
theorem kissing_census_500 :
    (Finset.range 500).filter (fun p => p.Prime ∧ p ^ 2 % 360 = 1) =
      {19, 71, 89, 109, 179, 181, 199, 251, 269, 271, 359, 379, 431, 449} := by
  decide +kernel

/-- XP-SQ-027: below 500 the twin kissing pairs are exactly `(179, 181)` and `(269, 271)`. -/
theorem twin_kissing_500 :
    (Finset.range 500).filter (fun p => p.Prime ∧ (p + 2).Prime ∧ p ^ 2 % 360 = 1 ∧
      (p + 2) ^ 2 % 360 = 1) = {179, 269} := by
  decide +kernel

end TemporalLattice

end
