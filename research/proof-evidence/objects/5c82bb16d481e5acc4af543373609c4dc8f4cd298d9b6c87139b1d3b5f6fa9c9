module

public import Mathlib
public import RequestProject.RodOrders

/-!
# The rods principle, and what follows from it

`RodOrders.orderOf_eq_lcm_rods` says: on a dial `ZMod (m·n)` with `m, n` coprime, the
multiplicative order of a step is the lcm of its orders mod `m` and mod `n`. This file collects
the consequences of that principle that bear on the research documents.

* **Both readings of "step".** The research uses "step" both for "add `s`" (stepping by 7 walks
  all 360 bearings) and for "multiply by `a`" (doubling on the abacus rods). The principle holds
  for both: `addOrderOf_eq_lcm_rods`, `orderOf_eq_lcm_rods`. It also holds for the length of the
  cycle through any bead under repeated multiplication (`period_mul_eq_lcm_rods`), which is
  what the abacus pictures actually draw.
* **Coprimality cannot be dropped** (`rods_need_coprime`).
* **Units and zero orders are decided rod by rod** (`isUnit_iff_rods`, `orderOf_eq_zero_iff_rods`).
* **Coprime rod orders multiply** (`orderOf_eq_mul_rods`).
* **The longest turn on the dial** (the exponent of the unit group) is the lcm of the rods'
  longest turns (`exponent_units_rods`); for 360 it is `lcm(2, 6, 4) = 12`
  (`exponent_units_360`). The dial 65520 has the same longest turn 12 (`exponent_units_65520`).
* **No single generating turn on a split dial** (`not_isCyclic_units_of_coprime`): if
  `m, n > 2` are coprime, the unit group of `ZMod (m·n)` is not cyclic. This is why the abacus
  has one doubling cycle through all units on 9 and 11 beads, but only short cycles on 15 beads
  (`fifteen_no_single_cycle`), and why 360 has no primitive root while `GF(361)` has one.
* **Counting solutions is multiplicative** (`card_pow_eq_one_rods`): the number of `x` with
  `x^k = 1` on the dial is the product of the counts on the rods. For `k = 2` the count on the
  360 dial is `4 · 2 · 2 = 16` (`card_sq_eq_one_360`), and the same 16 appears for every shell
  `2^a · 3² · 5^b` with `a ≥ 3`, e.g. 7200 and 144000 (`card_sq_eq_one_7200`,
  `card_sq_eq_one_144000`).
* **Two wheels that are not coprime** (the 12- and 9-bead wheels of `Lattice vs Abacus`):
  stepped together they return after `lcm(12, 9) = 36` steps and visit only 36 of the 108 joint
  positions (`wheels_12_9_period`); their bead boundaries coincide exactly at beads `0, 3, 6` of
  the nine-wheel, the 3-6-9 axis (`wheels_12_9_common_boundaries`).
-/

@[expose] public section

namespace RodsPrinciple

open RodOrders

/-- Conjugating a map by a bijection does not change the length of the cycle through a point. -/
lemma minimalPeriod_conj {α β : Type*} (e : α ≃ β) (f : α → α) (g : β → β)
    (h : Function.Semiconj e f g) (x : α) :
    Function.minimalPeriod g (e x) = Function.minimalPeriod f x := by
  rw [Function.minimalPeriod_eq_minimalPeriod_iff]
  intro n
  simp only [Function.IsPeriodicPt, Function.IsFixedPt]
  rw [← (h.iterate_right n) x]
  exact e.injective.eq_iff

/-! ## Both readings of "step" -/

/-- **Rods principle for additive steps.** On a dial `ZMod (m·n)` with `m, n` coprime, the number
of steps of size `s` needed to return to the start is the lcm of the numbers needed on the two
rods. -/
theorem addOrderOf_eq_lcm_rods {m n : ℕ} (h : Nat.Coprime m n) (s : ZMod (m * n)) :
    addOrderOf s = Nat.lcm (addOrderOf (ZMod.castHom (dvd_mul_right m n) (ZMod m) s))
      (addOrderOf (ZMod.castHom (dvd_mul_left n m) (ZMod n) s)) := by
  rw [← AddEquiv.addOrderOf_eq (ZMod.chineseRemainder h).toAddEquiv s, Prod.addOrderOf]
  have h1 : (RingHom.fst (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h).toRingHom =
      ZMod.castHom (dvd_mul_right m n) (ZMod m) := Subsingleton.elim _ _
  have h2 : (RingHom.snd (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h).toRingHom =
      ZMod.castHom (dvd_mul_left n m) (ZMod n) := Subsingleton.elim _ _
  rw [← h1, ← h2]
  rfl

/-- **Rods principle for cycles.** Under repeated multiplication by `a` on the dial `ZMod (m·n)`
(`m, n` coprime), the cycle through a bead `x` has length equal to the lcm of the lengths of the
cycles through its images on the two rods. (For `x = 1` this is the order of `a`.) -/
theorem period_mul_eq_lcm_rods {m n : ℕ} (h : Nat.Coprime m n) (a x : ZMod (m * n)) :
    Function.minimalPeriod (a * ·) x =
      Nat.lcm (Function.minimalPeriod (ZMod.castHom (dvd_mul_right m n) (ZMod m) a * ·)
          (ZMod.castHom (dvd_mul_right m n) (ZMod m) x))
        (Function.minimalPeriod (ZMod.castHom (dvd_mul_left n m) (ZMod n) a * ·)
          (ZMod.castHom (dvd_mul_left n m) (ZMod n) x)) := by
  have h1 : (RingHom.fst (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h).toRingHom =
      ZMod.castHom (dvd_mul_right m n) (ZMod m) := Subsingleton.elim _ _
  have h2 : (RingHom.snd (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h).toRingHom =
      ZMod.castHom (dvd_mul_left n m) (ZMod n) := Subsingleton.elim _ _
  rw [← h1, ← h2]
  set e := ZMod.chineseRemainder h
  rw [← minimalPeriod_conj e.toEquiv (a * ·) (Prod.map ((e a).1 * ·) ((e a).2 * ·)) (fun y => by
    simp [map_mul]; rfl) x, Function.minimalPeriod_prodMap]
  rfl

/-- **Coprimality is needed.** On the dial `ZMod 4 = ZMod (2·2)`, the step `3` has order 2, but
its images on both "rods" `ZMod 2` are `1`, of order 1. -/
theorem rods_need_coprime :
    orderOf (3 : ZMod (2 * 2)) = 2 ∧
    orderOf (ZMod.castHom (dvd_mul_right 2 2) (ZMod 2) 3) = 1 := by
  constructor
  · rw [orderOf_eq_iff (by norm_num)]; decide
  · rw [orderOf_eq_one_iff]; decide

/-! ## Units, zero orders, coprime orders -/

/-- A position of a split dial is a unit (an open spoke) exactly when it is a unit on each rod. -/
theorem isUnit_iff_rods {m n : ℕ} (h : Nat.Coprime m n) (x : ZMod (m * n)) :
    IsUnit x ↔ IsUnit (ZMod.castHom (dvd_mul_right m n) (ZMod m) x) ∧
      IsUnit (ZMod.castHom (dvd_mul_left n m) (ZMod n) x) := by
  have h1 : (RingHom.fst (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h).toRingHom =
      ZMod.castHom (dvd_mul_right m n) (ZMod m) := Subsingleton.elim _ _
  have h2 : (RingHom.snd (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h).toRingHom =
      ZMod.castHom (dvd_mul_left n m) (ZMod n) := Subsingleton.elim _ _
  rw [← h1, ← h2, ← isUnit_map_iff (ZMod.chineseRemainder h) x, Prod.isUnit_iff]
  rfl

/-- The order is `0` (the step never returns to `1`) exactly when it is `0` on some rod. -/
theorem orderOf_eq_zero_iff_rods {m n : ℕ} (h : Nat.Coprime m n) (x : ZMod (m * n)) :
    orderOf x = 0 ↔ orderOf (ZMod.castHom (dvd_mul_right m n) (ZMod m) x) = 0 ∨
      orderOf (ZMod.castHom (dvd_mul_left n m) (ZMod n) x) = 0 := by
  rw [orderOf_eq_lcm_rods h x, Nat.lcm_eq_zero_iff]

/-- If the orders on the two rods have no common factor, the order on the dial is their
product. -/
theorem orderOf_eq_mul_rods {m n : ℕ} (h : Nat.Coprime m n) (x : ZMod (m * n))
    (hc : Nat.Coprime (orderOf (ZMod.castHom (dvd_mul_right m n) (ZMod m) x))
      (orderOf (ZMod.castHom (dvd_mul_left n m) (ZMod n) x))) :
    orderOf x = orderOf (ZMod.castHom (dvd_mul_right m n) (ZMod m) x) *
      orderOf (ZMod.castHom (dvd_mul_left n m) (ZMod n) x) := by
  rw [orderOf_eq_lcm_rods h x, hc.lcm_eq_mul]

/-! ## The longest turn -/

/-- **Longest turn of a split dial.** The exponent of the unit group of `ZMod (m·n)` (the least
`e > 0` with `u^e = 1` for every unit, Carmichael's `λ`) is the lcm of the exponents on the
rods. -/
theorem exponent_units_rods {m n : ℕ} (h : Nat.Coprime m n) :
    Monoid.exponent (ZMod (m * n))ˣ =
      Nat.lcm (Monoid.exponent (ZMod m)ˣ) (Monoid.exponent (ZMod n)ˣ) := by
  rw [Monoid.exponent_eq_of_mulEquiv ((Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans
    MulEquiv.prodUnits), Monoid.exponent_prod]
  rfl

/-- The three rods of 360 have longest turns 2, 6 and 4, and the 360 dial has longest turn
`lcm(2, 6, 4) = 12`. -/
theorem exponent_units_360 :
    Monoid.exponent (ZMod 8)ˣ = 2 ∧ Monoid.exponent (ZMod 9)ˣ = 6 ∧
    Monoid.exponent (ZMod 5)ˣ = 4 ∧ Monoid.exponent (ZMod 360)ˣ = 12 := by
  have e8 : Monoid.exponent (ZMod 8)ˣ = 2 := by
    apply Nat.dvd_antisymm
    · exact Monoid.exponent_dvd_of_forall_pow_eq_one (by decide)
    · have : orderOf (ZMod.unitOfCoprime 3 (by norm_num) : (ZMod 8)ˣ) = 2 := by
        rw [← orderOf_units, orderOf_eq_iff (by norm_num)]; decide
      exact this ▸ Monoid.order_dvd_exponent _
  have e9 : Monoid.exponent (ZMod 9)ˣ = 6 := by
    apply Nat.dvd_antisymm
    · exact Monoid.exponent_dvd_of_forall_pow_eq_one (by decide)
    · have : orderOf (ZMod.unitOfCoprime 2 (by norm_num) : (ZMod 9)ˣ) = 6 := by
        rw [← orderOf_units, orderOf_eq_iff (by norm_num)]; decide
      exact this ▸ Monoid.order_dvd_exponent _
  have e5 : Monoid.exponent (ZMod 5)ˣ = 4 := by
    apply Nat.dvd_antisymm
    · exact Monoid.exponent_dvd_of_forall_pow_eq_one (by decide)
    · have : orderOf (ZMod.unitOfCoprime 2 (by norm_num) : (ZMod 5)ˣ) = 4 := by
        rw [← orderOf_units, orderOf_eq_iff (by norm_num)]; decide
      exact this ▸ Monoid.order_dvd_exponent _
  refine ⟨e8, e9, e5, ?_⟩
  rw [show (360 : ℕ) = 72 * 5 from rfl, exponent_units_rods (by norm_num),
    show (72 : ℕ) = 8 * 9 from rfl, exponent_units_rods (by norm_num), e8, e9, e5]
  rfl

/-- A helper: the exponent of `(ZMod N)ˣ` is `e` once every unit satisfies `u^e = 1` and some
unit has order `e`. -/
lemma exponent_eq_of (N e : ℕ) (hall : ∀ u : (ZMod N)ˣ, u ^ e = 1) (u : (ZMod N)ˣ)
    (hu : orderOf u = e) : Monoid.exponent (ZMod N)ˣ = e :=
  Nat.dvd_antisymm (Monoid.exponent_dvd_of_forall_pow_eq_one hall)
    (hu ▸ Monoid.order_dvd_exponent u)

/-- **The dial 65520 has the same longest turn as 360.** Its rods `16, 9, 5, 7, 13` have longest
turns `4, 6, 4, 6, 12`, whose lcm is 12. (This is why `p¹² ≡ 1 (mod 65520)` for every prime
`p ∉ {2, 3, 5, 7, 13}`, proved earlier.) -/
theorem exponent_units_65520 : Monoid.exponent (ZMod 65520)ˣ = 12 := by
  have e16 : Monoid.exponent (ZMod 16)ˣ = 4 := exponent_eq_of 16 4 (by decide)
    (ZMod.unitOfCoprime 3 (by norm_num))
    (by rw [← orderOf_units, orderOf_eq_iff (by norm_num)]; decide)
  have e9 : Monoid.exponent (ZMod 9)ˣ = 6 := exponent_eq_of 9 6 (by decide)
    (ZMod.unitOfCoprime 2 (by norm_num))
    (by rw [← orderOf_units, orderOf_eq_iff (by norm_num)]; decide)
  have e5 : Monoid.exponent (ZMod 5)ˣ = 4 := exponent_eq_of 5 4 (by decide)
    (ZMod.unitOfCoprime 2 (by norm_num))
    (by rw [← orderOf_units, orderOf_eq_iff (by norm_num)]; decide)
  have e7 : Monoid.exponent (ZMod 7)ˣ = 6 := exponent_eq_of 7 6 (by decide)
    (ZMod.unitOfCoprime 3 (by norm_num))
    (by rw [← orderOf_units, orderOf_eq_iff (by norm_num)]; decide)
  have e13 : Monoid.exponent (ZMod 13)ˣ = 12 := exponent_eq_of 13 12 (by decide)
    (ZMod.unitOfCoprime 2 (by norm_num))
    (by rw [← orderOf_units, orderOf_eq_iff (by norm_num)]; decide)
  rw [show (65520 : ℕ) = 5040 * 13 from rfl, exponent_units_rods (by norm_num),
    show (5040 : ℕ) = 720 * 7 from rfl, exponent_units_rods (by norm_num),
    show (720 : ℕ) = 144 * 5 from rfl, exponent_units_rods (by norm_num),
    show (144 : ℕ) = 16 * 9 from rfl, exponent_units_rods (by norm_num), e16, e9, e5, e7, e13]
  rfl

/-- **No single generating turn on a split dial.** If `m, n > 2` are coprime, no unit of
`ZMod (m·n)` has order `φ(m·n)`: the unit group is not cyclic. -/
theorem not_isCyclic_units_of_coprime {m n : ℕ} (h : Nat.Coprime m n) (hm : 2 < m) (hn : 2 < n) :
    ¬ IsCyclic (ZMod (m * n))ˣ := by
  intro hc
  haveI : NeZero m := ⟨by omega⟩
  haveI : NeZero n := ⟨by omega⟩
  haveI : NeZero (m * n) := ⟨by positivity⟩
  have hcard := IsCyclic.exponent_eq_card (α := (ZMod (m * n))ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_mul h,
    exponent_units_rods h] at hcard
  have em : Monoid.exponent (ZMod m)ˣ ∣ m.totient := by
    rw [← ZMod.card_units_eq_totient]; exact Group.exponent_dvd_card
  have en : Monoid.exponent (ZMod n)ˣ ∣ n.totient := by
    rw [← ZMod.card_units_eq_totient]; exact Group.exponent_dvd_card
  have hl : Nat.lcm (Monoid.exponent (ZMod m)ˣ) (Monoid.exponent (ZMod n)ˣ) ∣
      Nat.lcm m.totient n.totient :=
    Nat.lcm_dvd (em.trans (Nat.dvd_lcm_left _ _)) (en.trans (Nat.dvd_lcm_right _ _))
  have pm : 0 < m.totient := Nat.totient_pos.mpr (by omega)
  have pn : 0 < n.totient := Nat.totient_pos.mpr (by omega)
  obtain ⟨a, ha⟩ := Nat.totient_even hm
  obtain ⟨b, hb⟩ := Nat.totient_even hn
  have hg : 2 ∣ Nat.gcd m.totient n.totient := Nat.dvd_gcd ⟨a, by omega⟩ ⟨b, by omega⟩
  have hgl := Nat.gcd_mul_lcm m.totient n.totient
  have hle := Nat.le_of_dvd (Nat.lcm_pos pm pn) hl
  rw [hcard] at hle
  have hg2 : 2 ≤ Nat.gcd m.totient n.totient := Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ pm) hg
  nlinarith [Nat.mul_pos pm pn]

/-- **The abacus pictures explained.** On nine beads and on eleven beads, doubling runs through
all units in one cycle (order `φ = 6`, resp. `10`); on fifteen beads (`15 = 3·5`) there is no
unit whose powers reach all `φ(15) = 8` units, and every unit returns after at most 4 steps. -/
theorem fifteen_no_single_cycle :
    orderOf (2 : ZMod 9) = Nat.totient 9 ∧ orderOf (2 : ZMod 11) = Nat.totient 11 ∧
    ¬ IsCyclic (ZMod 15)ˣ ∧ (∀ u : (ZMod 15)ˣ, u ^ 4 = 1) := by
  refine ⟨?_, ?_, not_isCyclic_units_of_coprime (m := 3) (n := 5) (by norm_num) (by norm_num)
    (by norm_num), by decide⟩
  · rw [show Nat.totient 9 = 6 by decide, orderOf_eq_iff (by norm_num)]; decide
  · rw [show Nat.totient 11 = 10 by decide, orderOf_eq_iff (by norm_num)]; decide

/-! ## Counting solutions -/

/-- **Counting is multiplicative over rods.** The number of positions `x` of `ZMod (m·n)` with
`x^k = 1` is the product of the corresponding counts on the two rods. -/
theorem card_pow_eq_one_rods {m n : ℕ} [NeZero m] [NeZero n] (h : Nat.Coprime m n) (k : ℕ) :
    Fintype.card {x : ZMod (m * n) // x ^ k = 1} =
      Fintype.card {x : ZMod m // x ^ k = 1} * Fintype.card {x : ZMod n // x ^ k = 1} := by
  rw [← Fintype.card_prod]
  refine Fintype.card_congr (((ZMod.chineseRemainder h).toEquiv.subtypeEquiv
    (q := fun p : ZMod m × ZMod n => p.1 ^ k = 1 ∧ p.2 ^ k = 1) ?_).trans
    (Equiv.subtypeProdEquivProd (p := fun a : ZMod m => a ^ k = 1)
      (q := fun b : ZMod n => b ^ k = 1)))
  intro x
  show x ^ k = 1 ↔ ((ZMod.chineseRemainder h) x).1 ^ k = 1 ∧
    ((ZMod.chineseRemainder h) x).2 ^ k = 1
  have : x ^ k = 1 ↔ (ZMod.chineseRemainder h) x ^ k = 1 := by
    rw [← map_pow, ← (ZMod.chineseRemainder h).map_one, (ZMod.chineseRemainder h).injective.eq_iff]
  rw [this, Prod.ext_iff]
  rfl

/-- On the 360 dial exactly 16 positions square to 1: 4 on the rod 8, 2 on the rod 9 and 2 on
the rod 5. -/
theorem card_sq_eq_one_360 :
    Fintype.card {x : ZMod 8 // x ^ 2 = 1} = 4 ∧ Fintype.card {x : ZMod 9 // x ^ 2 = 1} = 2 ∧
    Fintype.card {x : ZMod 5 // x ^ 2 = 1} = 2 ∧ Fintype.card {x : ZMod 360 // x ^ 2 = 1} = 16 := by
  have h8 : Fintype.card {x : ZMod 8 // x ^ 2 = 1} = 4 := by decide
  have h9 : Fintype.card {x : ZMod 9 // x ^ 2 = 1} = 2 := by decide
  have h5 : Fintype.card {x : ZMod 5 // x ^ 2 = 1} = 2 := by decide
  refine ⟨h8, h9, h5, ?_⟩
  have e := card_pow_eq_one_rods (m := 72) (n := 5) (by norm_num) 2
  have e2 := card_pow_eq_one_rods (m := 8) (n := 9) (by norm_num) 2
  exact e.trans (by rw [e2, h8, h9, h5])

/-- The base layer 7200 also has exactly 16 square roots of 1 (`4 · 2 · 2` on the rods
`32, 9, 25`). -/
theorem card_sq_eq_one_7200 : Fintype.card {x : ZMod 7200 // x ^ 2 = 1} = 16 := by
  have h8 : Fintype.card {x : ZMod 32 // x ^ 2 = 1} = 4 := by decide
  have h9 : Fintype.card {x : ZMod 9 // x ^ 2 = 1} = 2 := by decide
  have h5 : Fintype.card {x : ZMod 25 // x ^ 2 = 1} = 2 := by decide
  have e := card_pow_eq_one_rods (m := 288) (n := 25) (by norm_num) 2
  have e2 := card_pow_eq_one_rods (m := 32) (n := 9) (by norm_num) 2
  exact e.trans (by rw [e2, h8, h9, h5])

/-- The base modulus 144000 also has exactly 16 square roots of 1 (`4 · 2 · 2` on the rods
`128, 9, 125`). -/
theorem card_sq_eq_one_144000 : Fintype.card {x : ZMod 144000 // x ^ 2 = 1} = 16 := by
  have h8 : Fintype.card {x : ZMod 128 // x ^ 2 = 1} = 4 := by decide
  have h9 : Fintype.card {x : ZMod 9 // x ^ 2 = 1} = 2 := by decide
  have h5 : Fintype.card {x : ZMod 125 // x ^ 2 = 1} = 2 := by decide
  have e := card_pow_eq_one_rods (m := 1152) (n := 125) (by norm_num) 2
  have e2 := card_pow_eq_one_rods (m := 128) (n := 9) (by norm_num) 2
  exact e.trans (by rw [e2, h8, h9, h5])

/-! ## Two wheels that do not share a rod structure -/

/-- The twelve-bead and nine-bead wheels, stepped together from a common start, first return
together after `lcm(12, 9) = 36` steps, so they visit only 36 of the `12 · 9 = 108` joint
positions (`gcd(12, 9) = 3` separate tracks). -/
theorem wheels_12_9_period :
    addOrderOf ((1, 1) : ZMod 12 × ZMod 9) = 36 ∧ 12 * 9 / 36 = Nat.gcd 12 9 := by
  refine ⟨?_, by norm_num⟩
  rw [Prod.addOrderOf, ZMod.addOrderOf_one, ZMod.addOrderOf_one]; rfl

/-- Both wheels span one day (1440 minutes): twelve beads of 120 minutes, nine beads of 160
minutes. A boundary of the nine-wheel coincides with a boundary of the twelve-wheel exactly at
beads `0, 3, 6` — the 3-6-9 axis of the nine-bead rod (digital roots `9, 3, 6`). -/
theorem wheels_12_9_common_boundaries :
    ∀ k < 9, (∃ j < 12, 160 * k = 120 * j) ↔ k ∈ ({0, 3, 6} : Finset ℕ) := by
  decide

end RodsPrinciple
