module

public import Mathlib
public import RequestProject.TemporalLattice
public import RequestProject.RodsPrinciple

/-!
# p, q, n, m, G, k and Q in one frame

Reading of the letters (see `PQ_NMGKQ.md`):

* `p`, `q` — primes; `n = p·q` (the explorer's product mode);
* `m` — a product of distinct primes, as in the thesis's `m = ∏_{p ∈ S} p`;
* `G` — the group of invertible residues `(ZMod m)ˣ` on the dial of size `m`;
* `k` — an exponent: how many times a step is repeated;
* `Q` — the qualifying-prime set `TemporalLattice.qualifyingPrimes` (primes `≥ 7` with
  `p − 1 ∣ 144000`).

Main results:

* `units_pow_eq_one_iff` — on a prime dial `p`, *every* step returns after `k` repeats exactly
  when `p − 1 ∣ k`.
* `mem_Q_iff_clock` — so `Q` is exactly the set of primes `p ≥ 7` whose whole unit group closes
  on the `144000` clock.
* `korselt` — on a dial of size `m`, `x^(k+1) = x` for every residue `x` iff `m` is
  squarefree and `p − 1 ∣ k` for every prime `p ∣ m` (Korselt's criterion, for any `k ≥ 1` and every `m`).
* `clock_closure` / `exponent_dvd_144000` — for every product `m` of distinct primes of
  `Q ∪ {2, 3, 5}`, `x^144001 = x` for all `x` mod `m`, and `G = (ZMod m)ˣ` has exponent dividing
  `144000`.
* `universal_modulus` — the dials with this property are exactly the divisors of
  `M⋆ = ∏ (Q ∪ {2,3,5})`.
* `pq_exponent_iff` — for distinct primes `p, q` and `n = p q`: `x^j = x` for all `x` mod `n`
  iff `lcm(p−1, q−1) ∣ j − 1`.
* `carmichael_1729`, `carmichael_41041` — two Carmichael numbers built only from `Q`.
* `not_clock_144001` — `144001 = 11·13·19·53` is *not* such a dial, because `53 ∉ Q`.
* `exponent_prod_primes`, `exponent_universal` — `G = (ZMod ∏S)ˣ` has longest turn
  `lcm {p − 1 : p ∈ S}`; for `M⋆` this is exactly `144000`, i.e. `λ(M⋆) = M₀`.
* `universal_k_iff` — on `M⋆`, `x^(k+1) = x` for all `x` iff `144000 ∣ k`.
* `carmichael_of_clock_product`, `carmichael_1601_14401_16001` — every product of distinct clock
  primes that is `≡ 1 (mod 144000)` is a Carmichael-type modulus.
* `orders_in_G144000`, `exponent_G144000` — on the 144000 dial, `λ(144000) = 2400`; `11 ∈ Q`
  attains it, `19` has order `800`, `16001` has order `2`.
* `pq_ellipse_pythagorean`, `nineteen_ellipse`, `pythagorean_pq_closure`,
  `nineteen_181_closure`, `pythagorean_pairs_in_clock`, `kissing_pythagorean_pair_unique` — the
  PQ ellipse with `q = (p² + 1)/2` has `4b = p² − 1`; for `(19, 181)` this is `360`; then
  `x^q = x` mod `n = p q`; inside the clock primes the pairs are `(3,5), (5,13), (11,61),
  (19,181)`, and only `19` also kisses 360.
* `kissing_not_on_own_dial` — `p² ≡ 1 (mod n)` is impossible when `p ≥ 2` divides `n`; in the
  explorer's product mode `n = p q` the kissing condition never holds.
-/

@[expose] public section

namespace KeyExponent

open TemporalLattice RodsPrinciple

/-! ## Prime dials -/

/-- On a prime dial every step returns after `k` repeats exactly when `p − 1 ∣ k`. -/
theorem units_pow_eq_one_iff (p : ℕ) [hp : Fact p.Prime] (k : ℕ) :
    (∀ u : (ZMod p)ˣ, u ^ k = 1) ↔ (p - 1) ∣ k := by
  rw [← Monoid.exponent_dvd_iff_forall_pow_eq_one, IsCyclic.exponent_eq_card,
    Nat.card_eq_fintype_card, ZMod.card_units]

/-- Residue form: `x^(k+1) = x` for every `x : ZMod p` iff `p − 1 ∣ k`. -/
theorem prime_pow_succ_eq_self_iff (p : ℕ) [hp : Fact p.Prime] (k : ℕ) :
    (∀ x : ZMod p, x ^ (k + 1) = x) ↔ (p - 1) ∣ k := by
  rw [← units_pow_eq_one_iff]
  constructor
  · intro h u
    have h1 := h (u : ZMod p)
    rw [pow_succ] at h1
    have h2 : (u : ZMod p) ^ k = 1 := mul_right_cancel₀ u.ne_zero (h1.trans (one_mul _).symm)
    ext
    simpa using h2
  · intro h x
    by_cases hx : x = 0
    · subst hx; simp
    · have h2 : x ^ k = 1 := by simpa using congrArg Units.val (h (Units.mk0 x hx))
      rw [pow_succ, h2, one_mul]

/-- **`Q` is the set of primes whose whole unit group closes on the 144000 clock.** -/
theorem mem_Q_iff_clock (p : ℕ) :
    p ∈ qualifyingPrimes ↔
      ∃ _ : p.Prime, 7 ≤ p ∧ ∀ u : (ZMod p)ˣ, u ^ 144000 = 1 := by
  rw [← qualifies_iff, qualifies_iff_aux]
  constructor
  · rintro ⟨hp, h7, hd⟩
    haveI := Fact.mk hp
    exact ⟨hp, h7, (units_pow_eq_one_iff p 144000).2 hd⟩
  · rintro ⟨hp, h7, hu⟩
    haveI := Fact.mk hp
    exact ⟨hp, h7, (units_pow_eq_one_iff p 144000).1 hu⟩

/-! ## Products of distinct primes -/

/-- For a finite set `S` of primes with `p − 1 ∣ k` for all `p ∈ S`, every residue modulo
`m = ∏ S` satisfies `x^(k+1) = x`. -/
theorem prod_pow_succ_eq_self (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (k : ℕ)
    (hk : ∀ p ∈ S, (p - 1) ∣ k) : ∀ x : ZMod (∏ p ∈ S, p), x ^ (k + 1) = x := by
  intro x
  obtain ⟨y, rfl⟩ := ZMod.intCast_surjective x
  have hdiv : ((∏ p ∈ S, p : ℕ) : ℤ) ∣ y ^ (k + 1) - y := by
    rw [Int.natCast_dvd]
    apply Finset.prod_primes_dvd
    · intro p hp; exact (hS p hp).prime
    · intro p hp
      haveI := Fact.mk (hS p hp)
      rw [← Int.natCast_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [(prime_pow_succ_eq_self_iff p k).2 (hk p hp), sub_self]
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdiv
  push_cast at this
  exact sub_eq_zero.1 this

/-- **Korselt's criterion, for any exponent.** -/
theorem korselt (m k : ℕ) (hk : 1 ≤ k) :
    (∀ x : ZMod m, x ^ (k + 1) = x) ↔
      Squarefree m ∧ ∀ p : ℕ, p.Prime → p ∣ m → (p - 1) ∣ k := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [Nat.squarefree_iff_prime_squarefree]
      intro p hp hpp
      have h1 := congrArg (ZMod.castHom hpp (ZMod (p * p))) (h (p : ZMod m))
      simp only [map_pow, map_natCast] at h1
      have h2 : ((p : ZMod (p * p))) ^ (k + 1) = 0 := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [show j + 1 + 1 = 2 + j by ring, pow_add, sq, ← Nat.cast_mul, ZMod.natCast_self,
          zero_mul]
      rw [h2] at h1
      have h3 := (ZMod.natCast_eq_zero_iff p (p * p)).1 h1.symm
      have := Nat.le_of_dvd hp.pos h3
      have := hp.two_le
      nlinarith
    · intro p hp hpm
      haveI := Fact.mk hp
      rw [← prime_pow_succ_eq_self_iff]
      intro y
      obtain ⟨x, rfl⟩ := ZMod.ringHom_surjective (ZMod.castHom hpm (ZMod p)) y
      rw [← map_pow, h x]
  · rintro ⟨hsq, hp⟩
    have := prod_pow_succ_eq_self m.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp) k
      (fun p hp' => hp p (Nat.prime_of_mem_primeFactors hp') (Nat.dvd_of_mem_primeFactors hp'))
    rwa [Nat.prod_primeFactors_of_squarefree hsq] at this

/-- The extended qualifying set `Q ∪ {2, 3, 5}`: all primes with `p − 1 ∣ 144000`. -/
def clockPrimes : Finset ℕ := insert 2 (insert 3 (insert 5 qualifyingPrimes))

theorem mem_clockPrimes_iff (p : ℕ) : p ∈ clockPrimes ↔ p.Prime ∧ (p - 1) ∣ 144000 := by
  unfold clockPrimes
  simp only [Finset.mem_insert]
  constructor
  · rintro (rfl | rfl | rfl | h)
    · norm_num
    · norm_num
    · norm_num
    · exact ⟨(qualifyingPrimes_spec p h).1, (qualifyingPrimes_spec p h).2.2⟩
  · rintro ⟨hp, hd⟩
    by_cases h7 : 7 ≤ p
    · exact Or.inr (Or.inr (Or.inr ((qualifies_iff p).1 ((qualifies_iff_aux p).2 ⟨hp, h7, hd⟩))))
    · have := hp.two_le
      interval_cases p
      · simp
      · simp
      · norm_num at hp
      · simp
      · norm_num at hp

/-- **Clock closure.** For every set `S` of primes from `Q ∪ {2,3,5}` and `m = ∏ S`,
every residue satisfies `x^144001 = x (mod m)`. -/
theorem clock_closure (S : Finset ℕ) (hS : S ⊆ clockPrimes) :
    ∀ x : ZMod (∏ p ∈ S, p), x ^ 144001 = x := by
  exact prod_pow_succ_eq_self S (fun p hp => ((mem_clockPrimes_iff p).1 (hS hp)).1) 144000
    (fun p hp => ((mem_clockPrimes_iff p).1 (hS hp)).2)

/-- **`G` lives on the 144000 clock.** For such `m`, the exponent of `G = (ZMod m)ˣ` divides
`144000`. -/
theorem exponent_dvd_144000 (S : Finset ℕ) (hS : S ⊆ clockPrimes) :
    Monoid.exponent (ZMod (∏ p ∈ S, p))ˣ ∣ 144000 := by
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro u
  have h : u ^ 144001 = u := Units.ext (by push_cast; exact clock_closure S hS u)
  rw [pow_succ] at h
  exact mul_eq_right.1 h

/-- The universal modulus `M⋆ = ∏ (Q ∪ {2,3,5})`. -/
def universalModulus : ℕ := ∏ p ∈ clockPrimes, p

/-- **The universal modulus.** A dial `m ≥ 1` satisfies `x^144001 = x` for every residue
exactly when `m ∣ M⋆`. -/
theorem universal_modulus (m : ℕ) (hm : 1 ≤ m) :
    (∀ x : ZMod m, x ^ 144001 = x) ↔ m ∣ universalModulus := by
  constructor
  · intro h
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · rw [show m = 1 by omega]; exact one_dvd _
    obtain ⟨hsq, hp⟩ := (korselt m 144000 (by norm_num)).1 h
    rw [← Nat.prod_primeFactors_of_squarefree hsq]
    apply Finset.prod_dvd_prod_of_subset
    intro p hpm
    exact (mem_clockPrimes_iff p).2 ⟨Nat.prime_of_mem_primeFactors hpm,
      hp p (Nat.prime_of_mem_primeFactors hpm) (Nat.dvd_of_mem_primeFactors hpm)⟩
  · intro hdvd y
    obtain ⟨x, rfl⟩ := ZMod.ringHom_surjective (ZMod.castHom hdvd (ZMod m)) y
    rw [← map_pow, clock_closure clockPrimes subset_rfl x]

/-! ## `n = p q` -/

/-- **Two-prime dials.** For distinct primes `p, q` and `j ≥ 2`, every residue mod `n = p q`
satisfies `x^j = x` iff `lcm(p − 1, q − 1) ∣ j − 1`. -/
theorem pq_exponent_iff (p q j : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hj : 2 ≤ j) :
    (∀ x : ZMod (p * q), x ^ j = x) ↔ Nat.lcm (p - 1) (q - 1) ∣ j - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [korselt (p * q) k (by omega), Nat.add_sub_cancel, Nat.lcm_dvd_iff]
  have hsq : Squarefree (p * q) :=
    Nat.squarefree_mul_iff.2 ⟨(Nat.coprime_primes hp hq).2 hpq, hp.prime.squarefree,
      hq.prime.squarefree⟩
  constructor
  · rintro ⟨-, h⟩
    exact ⟨h p hp (dvd_mul_right p q), h q hq (dvd_mul_left q p)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨hsq, fun r hr hrpq => ?_⟩
    rcases (Nat.Prime.dvd_mul hr).1 hrpq with h | h
    · rwa [(Nat.prime_dvd_prime_iff_eq hr hp).1 h]
    · rwa [(Nat.prime_dvd_prime_iff_eq hr hq).1 h]

/-! ## Carmichael numbers from `Q`, and 144001 -/

theorem carmichael_1729 : 1729 = 7 * 13 * 19 ∧ (∀ x : ZMod 1729, x ^ 1729 = x) := by
  refine ⟨by norm_num, ?_⟩
  have := prod_pow_succ_eq_self {7, 13, 19} (by decide) 1728 (by decide)
  exact this

theorem carmichael_41041 : 41041 = 7 * 11 * 13 * 41 ∧ (∀ x : ZMod 41041, x ^ 41041 = x) := by
  refine ⟨by norm_num, ?_⟩
  have := prod_pow_succ_eq_self {7, 11, 13, 41} (by decide) 41040 (by decide)
  exact this

/-- `144001 = 11·13·19·53` does not close on the clock: some residue has `x^144001 ≠ x`. -/
theorem not_clock_144001 : 144001 = 11 * 13 * 19 * 53 ∧ 53 ∉ qualifyingPrimes ∧
    ∃ x : ZMod 144001, x ^ 144001 ≠ x := by
  refine ⟨by norm_num, by decide, ?_⟩
  by_contra h
  push_neg at h
  have := ((korselt 144001 144000 (by norm_num)).1 h).2 53 (by norm_num) (by norm_num)
  norm_num at this

/-! ## The kissing condition and the dial -/

/-- The kissing condition `p² ≡ 1 (mod n)` fails whenever `p ≥ 2` divides the dial. -/
theorem kissing_not_on_own_dial (p n : ℕ) (hp : 2 ≤ p) (hpn : p ∣ n) : p ^ 2 % n ≠ 1 := by
  intro h
  have h1 : p ∣ p ^ 2 % n := (Nat.dvd_mod_iff hpn).2 (dvd_pow_self p two_ne_zero)
  rw [h] at h1
  have := Nat.le_of_dvd one_pos h1
  omega

/-! ## The exponent of `G` on a product of primes, and `M₀ = λ(M⋆)` -/

/-- **The longest turn of `G = (ZMod m)ˣ` for `m = ∏ S`** is `lcm {p − 1 : p ∈ S}`. -/
theorem exponent_prod_primes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Monoid.exponent (ZMod (∏ p ∈ S, p))ˣ = S.lcm (fun p => p - 1) := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.lcm_empty]
    exact Monoid.exp_eq_one_iff.2 inferInstance
  | insert a s ha ih =>
    have hpa : a.Prime := hS a (Finset.mem_insert_self a s)
    have hs : ∀ p ∈ s, p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hcop : Nat.Coprime a (∏ p ∈ s, p) := Nat.Coprime.prod_right fun p hp =>
      (Nat.coprime_primes hpa (hs p hp)).2 (fun h => ha (h ▸ hp))
    haveI := Fact.mk hpa
    rw [Finset.prod_insert ha, exponent_units_rods hcop, ih hs, Finset.lcm_insert,
      IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units]
    rfl

/-- **The base modulus is recovered from `Q`.** The longest turn of `G = (ZMod M⋆)ˣ` is exactly
`144000`: `λ(M⋆) = M₀`. -/
theorem exponent_universal : Monoid.exponent (ZMod universalModulus)ˣ = 144000 := by
  rw [universalModulus, exponent_prod_primes clockPrimes
    (fun p hp => ((mem_clockPrimes_iff p).1 hp).1)]
  decide

/-- **`k` on the universal dial.** `x^(k+1) = x` for every residue mod `M⋆` exactly when
`144000 ∣ k`; so `k = 144000` is the least positive such exponent. -/
theorem universal_k_iff (k : ℕ) :
    (∀ x : ZMod universalModulus, x ^ (k + 1) = x) ↔ 144000 ∣ k := by
  constructor
  · intro h
    rw [← exponent_universal]
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro u
    have h1 : u ^ (k + 1) = u := Units.ext (by push_cast; exact h u)
    rw [pow_succ] at h1
    exact mul_eq_right.1 h1
  · intro hk
    exact prod_pow_succ_eq_self clockPrimes (fun p hp => ((mem_clockPrimes_iff p).1 hp).1) k
      (fun p hp => ((mem_clockPrimes_iff p).1 hp).2.trans hk)

/-- **Carmichael numbers from `Q`.** Any product `m` of distinct primes of `Q ∪ {2,3,5}` with
`m ≡ 1 (mod 144000)` satisfies `x^m = x` for every residue `x` mod `m`. -/
theorem carmichael_of_clock_product (S : Finset ℕ) (hS : S ⊆ clockPrimes)
    (h1 : (∏ p ∈ S, p) % 144000 = 1) : ∀ x : ZMod (∏ p ∈ S, p), x ^ (∏ p ∈ S, p) = x := by
  have hpos : 1 ≤ ∏ p ∈ S, p := by
    rcases Nat.eq_zero_or_pos (∏ p ∈ S, p) with h | h
    · rw [h] at h1; norm_num at h1
    · exact h
  have hk : 144000 ∣ (∏ p ∈ S, p) - 1 := by
    have := Nat.div_add_mod (∏ p ∈ S, p) 144000
    rw [h1] at this
    exact ⟨(∏ p ∈ S, p) / 144000, by omega⟩
  have := prod_pow_succ_eq_self S (fun p hp => ((mem_clockPrimes_iff p).1 (hS hp)).1)
    ((∏ p ∈ S, p) - 1) (fun p hp => ((mem_clockPrimes_iff p).1 (hS hp)).2.trans hk)
  rwa [Nat.sub_add_cancel hpos] at this

/-- The three-prime instance `1601 · 14401 · 16001 ≡ 1 (mod 144000)`. -/
theorem carmichael_1601_14401_16001 : 1601 * 14401 * 16001 = 368919072001 ∧
    368919072001 % 144000 = 1 ∧ ∀ x : ZMod 368919072001, x ^ 368919072001 = x :=
  ⟨by norm_num, by norm_num,
    carmichael_of_clock_product {1601, 14401, 16001} (by decide) (by decide)⟩

/-! ## Orders in `G = (ZMod 144000)ˣ` -/

lemma zmod_pow_eq_one_of_mod (a k N : ℕ) (h : a ^ k % N = 1 % N) : (a : ZMod N) ^ k = 1 := by
  rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff']
  exact h

lemma zmod_pow_ne_one_of_mod (a k N : ℕ) (h : a ^ k % N ≠ 1 % N) : (a : ZMod N) ^ k ≠ 1 := by
  rw [← Nat.cast_pow, ← Nat.cast_one, Ne, ZMod.natCast_eq_natCast_iff']
  exact h

lemma units_pow_of_nat (N k : ℕ) [NeZero N]
    (h : ∀ a < N, Nat.Coprime a N → a ^ k % N = 1 % N) : ∀ u : (ZMod N)ˣ, u ^ k = 1 := by
  intro u
  ext
  push_cast
  rw [← ZMod.natCast_zmod_val (u : ZMod N)]
  exact zmod_pow_eq_one_of_mod _ _ _ (h _ (ZMod.val_lt _) (ZMod.val_coe_unit_coprime u))

lemma primeFactors_2400 : Nat.primeFactors 2400 = {2, 3, 5} := by
  rw [show (2400 : ℕ) = 2 ^ 5 * 3 * 5 ^ 2 by norm_num,
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_five,
    Nat.Prime.primeFactors Nat.prime_three]
  decide

lemma primeFactors_800 : Nat.primeFactors 800 = {2, 5} := by
  rw [show (800 : ℕ) = 2 ^ 5 * 5 ^ 2 by norm_num,
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_five]
  decide

set_option exponentiation.threshold 5000 in
/-- **Orders of qualifying primes on the 144000 dial.** `11` has order `2400`, the anchor `19`
has order `800 = 2400/3`, and `16001` has order `2`. -/
theorem orders_in_G144000 :
    orderOf (11 : ZMod 144000) = 2400 ∧ orderOf (19 : ZMod 144000) = 800 ∧
      orderOf (16001 : ZMod 144000) = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · have e : (11 : ZMod 144000) = ((11 : ℕ) : ZMod 144000) := rfl
    rw [e]
    apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
    · exact zmod_pow_eq_one_of_mod _ _ _ (by decide +kernel)
    · intro p hp hpd
      have : p ∈ Nat.primeFactors 2400 := Nat.mem_primeFactors.2 ⟨hp, hpd, by norm_num⟩
      rw [primeFactors_2400] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl | rfl <;> exact zmod_pow_ne_one_of_mod _ _ _ (by decide +kernel)
  · have e : (19 : ZMod 144000) = ((19 : ℕ) : ZMod 144000) := rfl
    rw [e]
    apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
    · exact zmod_pow_eq_one_of_mod _ _ _ (by decide +kernel)
    · intro p hp hpd
      have : p ∈ Nat.primeFactors 800 := Nat.mem_primeFactors.2 ⟨hp, hpd, by norm_num⟩
      rw [primeFactors_800] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl <;> exact zmod_pow_ne_one_of_mod _ _ _ (by decide +kernel)
  · rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, fun m hm hm0 => ?_⟩
    interval_cases m
    decide

set_option exponentiation.threshold 5000 in
/-- **The longest turn on the 144000 dial is 2400** (`λ(144000) = lcm(32, 6, 100)`), and the
qualifying prime `11` attains it. -/
theorem exponent_G144000 : Monoid.exponent (ZMod 144000)ˣ = 2400 := by
  have h128 : Monoid.exponent (ZMod 128)ˣ ∣ 32 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one (units_pow_of_nat 128 32 (by decide +kernel))
  have h9 : Monoid.exponent (ZMod 9)ˣ ∣ 6 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one (units_pow_of_nat 9 6 (by decide +kernel))
  have h125 : Monoid.exponent (ZMod 125)ˣ ∣ 100 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one (units_pow_of_nat 125 100 (by decide +kernel))
  apply Nat.dvd_antisymm
  · rw [show (144000 : ℕ) = 128 * 1125 from rfl, exponent_units_rods (by norm_num),
      show (1125 : ℕ) = 9 * 125 from rfl, exponent_units_rods (by norm_num)]
    exact Nat.lcm_dvd (h128.trans (by norm_num))
      (Nat.lcm_dvd (h9.trans (by norm_num)) (h125.trans (by norm_num)))
  · have h := Monoid.order_dvd_exponent (ZMod.unitOfCoprime 11 (by norm_num) : (ZMod 144000)ˣ)
    rwa [← orderOf_units, ZMod.coe_unitOfCoprime, Nat.cast_ofNat, orders_in_G144000.1] at h

/-! ## The PQ ellipse, `q = (p² + 1)/2`, and the kissing condition -/

/-- **Pythagorean PQ ellipse.** With `a = q/2`, `c = p/2` (so eccentricity `p/q`) and
`2q = p² + 1`, the semi-minor axis `b = √((q² − p²)/4)` is exactly `(p² − 1)/4`. Hence
`4b = p² − 1`, and `p² ≡ 1 (mod 360)` says exactly that `4b` is a whole number of turns. -/
theorem pq_ellipse_pythagorean (p q : ℝ) (hp : 1 ≤ p) (h : 2 * q = p ^ 2 + 1) :
    Real.sqrt ((q ^ 2 - p ^ 2) / 4) = (p ^ 2 - 1) / 4 := by
  have hq : q = (p ^ 2 + 1) / 2 := by linarith
  rw [show (q ^ 2 - p ^ 2) / 4 = ((p ^ 2 - 1) / 4) ^ 2 by rw [hq]; ring]
  exact Real.sqrt_sq (by nlinarith)

/-- For `p = 19`, `q = 181 = (19² + 1)/2`: the semi-minor axis is `90`, so `4b = 360`. -/
theorem nineteen_ellipse : Real.sqrt (((181 : ℝ) ^ 2 - 19 ^ 2) / 4) = 90 := by
  rw [pq_ellipse_pythagorean 19 181 (by norm_num) (by norm_num)]; norm_num

/-- **`n = p q` with `q = (p² + 1)/2`.** If both are prime (`p` odd), then `λ(pq) = q − 1`, so
every residue mod `n = p q` satisfies `x^q = x`. -/
theorem pythagorean_pq_closure (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hodd : p ≠ 2)
    (h : 2 * q = p ^ 2 + 1) : ∀ x : ZMod (p * q), x ^ q = x := by
  obtain ⟨t, rfl⟩ : ∃ t, p = 2 * t + 1 := by
    rcases hp.eq_two_or_odd' with h2 | ⟨t, ht⟩
    · exact absurd h2 hodd
    · exact ⟨t, ht⟩
  have ht : 1 ≤ t := by have := hp.two_le; omega
  have hq' : q = 2 * t ^ 2 + 2 * t + 1 := by nlinarith
  have hne : 2 * t + 1 ≠ q := by rw [hq']; nlinarith
  rw [pq_exponent_iff _ _ _ hp hq hne hq.two_le]
  apply Nat.lcm_dvd
  · exact ⟨t + 1, by rw [hq', Nat.add_sub_cancel, Nat.add_sub_cancel]; ring⟩
  · exact dvd_refl _

/-- The instance `p = 19`, `q = 181`, `n = 3439`: `x^181 = x` for every residue mod `3439`. -/
theorem nineteen_181_closure : ∀ x : ZMod 3439, x ^ 181 = x :=
  pythagorean_pq_closure 19 181 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Pythagorean pairs inside the clock primes.** For odd `p ∈ Q ∪ {2,3,5}`, the number
`(p² + 1)/2` is again in `Q ∪ {2,3,5}` exactly for `p = 3, 5, 11, 19`. -/
theorem pythagorean_pairs_in_clock :
    ∀ p ∈ clockPrimes, p ≠ 2 →
      ((p ^ 2 + 1) / 2 ∈ clockPrimes ↔ p ∈ ({3, 5, 11, 19} : Finset ℕ)) := by
  decide

/-- …and `19` is the only one of them that also satisfies the kissing condition mod 360. -/
theorem kissing_pythagorean_pair_unique :
    ∀ p ∈ clockPrimes, p ≠ 2 →
      ((p ^ 2 + 1) / 2 ∈ clockPrimes ∧ p ^ 2 % 360 = 1 ↔ p = 19) := by
  decide

end KeyExponent

end
