module

public import Mathlib
public import LatticeCalc.Verified.OrderSplit
public import RequestProject.KeyExponent

/-!
# Q to k: at least half of all bases split `n = p q`

The library's order splitting (`LatticeCalc.Verified.OrderSplit.splitWith`) factors `n = p q`
from a base `a` and any multiple `E` of `k = lcm(p − 1, q − 1)`; it succeeds **exactly** when the
orders of `a` modulo `p` and modulo `q` differ (`splitWith_isSome_iff`).  Here we count how many
bases do that.

* `bad_units_card` — among the `(p − 1)(q − 1)` unit pairs, those with equal orders number at most
  `g²`, `g = gcd(p − 1, q − 1)`, and `2 g² ≤ (p − 1)(q − 1)`.
* `half_bases_split` — for distinct primes `p, q`, any nonzero multiple `E` of `k` and any list
  `rs` containing the primes of `E`: at least `(p − 1)(q − 1) / 2` of the bases `a ∈ [0, p q)` make
  the routine return a factor.  So a base drawn at random from `[0, pq)` succeeds with probability
  at least `(p − 1)(q − 1) / (2 p q)`, which is close to `1/2`.
* `clock_half_bases_split`, `Q_half_bases_split` — on the 144000 clock (every pair of primes with
  `p − 1, q − 1 ∣ 144000`, in particular every pair from the qualifying set `Q`) the fixed exponent
  `E = 144000` and `rs = [2, 3, 5]` work, with the same guarantee.
-/

@[expose] public section

namespace BaseDensity

open Finset LatticeCalc.Verified.OrderSplit

lemma two_gcd_sq_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    2 * (Nat.gcd (p - 1) (q - 1) * Nat.gcd (p - 1) (q - 1)) ≤ (p - 1) * (q - 1) := by
  set g := Nat.gcd (p - 1) (q - 1)
  obtain ⟨u, hu⟩ : g ∣ p - 1 := Nat.gcd_dvd_left (p - 1) (q - 1)
  obtain ⟨v, hv⟩ : g ∣ q - 1 := Nat.gcd_dvd_right (p - 1) (q - 1)
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu; omega
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv; omega
  have huv : u ≠ v := by rintro rfl; apply hpq; omega
  have h2 : 2 ≤ u * v := by
    rcases Nat.lt_or_gt_of_ne huv with h | h
    · nlinarith [Nat.pos_of_ne_zero hu0]
    · nlinarith [Nat.pos_of_ne_zero hv0]
  rw [hu, hv]
  calc 2 * (g * g) ≤ (u * v) * (g * g) := Nat.mul_le_mul_right _ h2
    _ = g * u * (g * v) := by ring

/-- Unit pairs whose orders agree are few: at most `g²`, and twice that is at most the number of
unit pairs. -/
theorem bad_units_card {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q) :
    2 * (univ.filter (fun u : (ZMod p)ˣ × (ZMod q)ˣ => orderOf u.1 = orderOf u.2)).card ≤
      (p - 1) * (q - 1) := by
  set g := Nat.gcd (p - 1) (q - 1)
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (by have := hp.out.two_le; omega)
  have hsub : univ.filter (fun u : (ZMod p)ˣ × (ZMod q)ˣ => orderOf u.1 = orderOf u.2) ⊆
      (univ.filter (fun x : (ZMod p)ˣ => x ^ g = 1)) ×ˢ
        (univ.filter (fun y : (ZMod q)ˣ => y ^ g = 1)) := by
    rintro ⟨x, y⟩ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at h ⊢
    have hx : orderOf x ∣ p - 1 := by
      have := orderOf_dvd_card (x := x)
      rwa [ZMod.card_units] at this
    have hy : orderOf y ∣ q - 1 := by
      have := orderOf_dvd_card (x := y)
      rwa [ZMod.card_units] at this
    have hxg : orderOf x ∣ g := Nat.dvd_gcd hx (h ▸ hy)
    exact ⟨orderOf_dvd_iff_pow_eq_one.1 hxg,
      orderOf_dvd_iff_pow_eq_one.1 (h ▸ hxg)⟩
  have h1 := IsCyclic.card_pow_eq_one_le (α := (ZMod p)ˣ) hg
  have h2 := IsCyclic.card_pow_eq_one_le (α := (ZMod q)ˣ) hg
  have hc := Finset.card_le_card hsub
  rw [Finset.card_product] at hc
  have := two_gcd_sq_le hp.out hq.out hpq
  calc 2 * _ ≤ 2 * (g * g) := Nat.mul_le_mul_left _ (hc.trans (Nat.mul_le_mul h1 h2))
    _ ≤ _ := this

lemma cast_chineseRemainder_left {p q : ℕ} [NeZero p] (h : p.Coprime q) (x : ZMod p)
    (y : ZMod q) : ((Nat.chineseRemainder h x.val y.val : ℕ) : ZMod p) = x := by
  have := (Nat.chineseRemainder h x.val y.val).prop.1
  rw [← ZMod.natCast_eq_natCast_iff] at this
  rw [this, ZMod.natCast_zmod_val]

lemma cast_chineseRemainder_right {p q : ℕ} [NeZero q] (h : p.Coprime q) (x : ZMod p)
    (y : ZMod q) : ((Nat.chineseRemainder h x.val y.val : ℕ) : ZMod q) = y := by
  have := (Nat.chineseRemainder h x.val y.val).prop.2
  rw [← ZMod.natCast_eq_natCast_iff] at this
  rw [this, ZMod.natCast_zmod_val]

/-- **At least half of the unit bases split `n = p q`**, for any nonzero multiple `E` of
`k = lcm(p − 1, q − 1)`. -/
theorem half_bases_split {p q E : ℕ} (rs : List ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hE : E ≠ 0) (hk : Nat.lcm (p - 1) (q - 1) ∣ E) (hrs : ∀ r, r.Prime → r ∣ E → r ∈ rs) :
    (p - 1) * (q - 1) ≤
      2 * ((range (p * q)).filter (fun a => (splitWith (p * q) a E rs).isSome)).card := by
  haveI := Fact.mk hp
  haveI := Fact.mk hq
  have hcop : p.Coprime q := (Nat.coprime_primes hp hq).2 hpq
  set good := univ.filter (fun u : (ZMod p)ˣ × (ZMod q)ˣ => ¬ orderOf u.1 = orderOf u.2)
  set bad := univ.filter (fun u : (ZMod p)ˣ × (ZMod q)ˣ => orderOf u.1 = orderOf u.2)
  have htot : good.card + bad.card = (p - 1) * (q - 1) := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset ((ZMod p)ˣ × (ZMod q)ˣ)))
      (fun u => orderOf u.1 = orderOf u.2)
    rw [Finset.card_univ, Fintype.card_prod, ZMod.card_units, ZMod.card_units] at this
    rw [add_comm]; exact this
  have hbad : 2 * bad.card ≤ (p - 1) * (q - 1) := bad_units_card (p := p) (q := q) hpq
  have hpE : p - 1 ∣ E := (Nat.dvd_lcm_left _ _).trans hk
  have hqE : q - 1 ∣ E := (Nat.dvd_lcm_right _ _).trans hk
  let f : (ZMod p)ˣ × (ZMod q)ˣ → ℕ :=
    fun u => Nat.chineseRemainder hcop (u.1 : ZMod p).val (u.2 : ZMod q).val
  have hinj : Set.InjOn f good := by
    rintro ⟨x, y⟩ _ ⟨x', y'⟩ _ h
    have h1 := cast_chineseRemainder_left hcop (x : ZMod p) (y : ZMod q)
    have h2 := cast_chineseRemainder_right hcop (x : ZMod p) (y : ZMod q)
    have h1' := cast_chineseRemainder_left hcop (x' : ZMod p) (y' : ZMod q)
    have h2' := cast_chineseRemainder_right hcop (x' : ZMod p) (y' : ZMod q)
    simp only [f] at h
    rw [h] at h1 h2
    exact Prod.ext (Units.ext (h1.symm.trans h1')) (Units.ext (h2.symm.trans h2'))
  have hmaps : ∀ u ∈ good, f u ∈ (range (p * q)).filter
      (fun a => (splitWith (p * q) a E rs).isSome) := by
    rintro ⟨x, y⟩ hu
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    simp only [Finset.mem_filter, Finset.mem_range, f]
    have hxa := cast_chineseRemainder_left hcop (x : ZMod p) (y : ZMod q)
    have hya := cast_chineseRemainder_right hcop (x : ZMod p) (y : ZMod q)
    refine ⟨Nat.chineseRemainder_lt_mul _ _ _ hp.ne_zero hq.ne_zero, ?_⟩
    set a := Nat.chineseRemainder hcop (x : ZMod p).val (y : ZMod q).val
    have hxE : (x : ZMod p) ^ E = 1 := by
      obtain ⟨c, hc⟩ := hpE
      rw [hc, pow_mul, ZMod.pow_card_sub_one_eq_one x.ne_zero, one_pow]
    have hyE : (y : ZMod q) ^ E = 1 := by
      obtain ⟨c, hc⟩ := hqE
      rw [hc, pow_mul, ZMod.pow_card_sub_one_eq_one y.ne_zero, one_pow]
    rw [splitWith_isSome_iff rs hp hq hpq hE (by rw [hxa]; exact hxE) (by rw [hya]; exact hyE) hrs,
      hxa, hya, orderOf_units, orderOf_units]
    exact hu
  have := Finset.card_le_card_of_injOn f (fun u hu => Finset.mem_coe.2 (hmaps u (Finset.mem_coe.1 hu))) hinj
  omega

lemma primes_of_144000 : ∀ r, r.Prime → r ∣ 144000 → r ∈ [2, 3, 5] := by
  intro r hr hd
  have h : (144000 : ℕ) = 2 ^ 7 * 3 ^ 2 * 5 ^ 3 := by norm_num
  rw [h] at hd
  rcases (Nat.Prime.dvd_mul hr).1 hd with hd | hd
  · rcases (Nat.Prime.dvd_mul hr).1 hd with hd | hd
    · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hd); simp [this]
    · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 (hr.dvd_of_dvd_pow hd); simp [this]
  · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).1 (hr.dvd_of_dvd_pow hd); simp [this]

/-- **The clock case is completely solved.**  For distinct primes with `p − 1` and `q − 1` dividing
`144000`, the fixed exponent `144000` with `rs = [2, 3, 5]` splits `p q` for at least half of the
unit bases.  No knowledge of `p` or `q` is used by the routine. -/
theorem clock_half_bases_split {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp1 : p - 1 ∣ 144000) (hq1 : q - 1 ∣ 144000) :
    (p - 1) * (q - 1) ≤
      2 * ((range (p * q)).filter (fun a => (splitWith (p * q) a 144000 [2, 3, 5]).isSome)).card :=
  half_bases_split [2, 3, 5] hp hq hpq (by norm_num) (Nat.lcm_dvd hp1 hq1) primes_of_144000

/-- The same for every pair of distinct primes from the qualifying set `Q`. -/
theorem Q_half_bases_split {p q : ℕ} (hp : p ∈ TemporalLattice.qualifyingPrimes)
    (hq : q ∈ TemporalLattice.qualifyingPrimes) (hpq : p ≠ q) :
    (p - 1) * (q - 1) ≤
      2 * ((range (p * q)).filter (fun a => (splitWith (p * q) a 144000 [2, 3, 5]).isSome)).card := by
  obtain ⟨hpp, -, hpu⟩ := (KeyExponent.mem_Q_iff_clock p).1 hp
  obtain ⟨hqp, -, hqu⟩ := (KeyExponent.mem_Q_iff_clock q).1 hq
  haveI := Fact.mk hpp
  haveI := Fact.mk hqp
  exact clock_half_bases_split hpp hqp hpq ((KeyExponent.units_pow_eq_one_iff p _).1 hpu)
    ((KeyExponent.units_pow_eq_one_iff q _).1 hqu)

end BaseDensity
