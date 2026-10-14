module

public import Mathlib

/-!
# The rods principle for turn orders

The synthesis uses, but never stated as one theorem, the rule that on a dial split into
independent rods by the Chinese remainder theorem, the turn order of a step is the least common
multiple of its turn orders on the rods. This file states and proves it.

* `orderOf_eq_lcm_rods` : for coprime `m, n` and any `x` on the dial `ZMod (m·n)`,
  `orderOf x = lcm (orderOf (x mod m)) (orderOf (x mod n))`;
* `orderOf_360_eq_lcm_rods` : the 360 dial splits into the rods `8, 9, 5`, and the order of any
  `x` on it is the lcm of its orders mod `8`, mod `9` and mod `5`.

Here `orderOf` is the multiplicative order (the number of repeated multiplications by `x` before
returning to `1`; it is `0` when `x` never returns, e.g. for non-units).
-/

@[expose] public section

namespace RodOrders

/-- **Rods principle.** On a dial `ZMod (m·n)` with `m, n` coprime, the turn order of `x` is the
lcm of its turn orders on the two rods `ZMod m` and `ZMod n`. -/
theorem orderOf_eq_lcm_rods {m n : ℕ} (h : Nat.Coprime m n) (x : ZMod (m * n)) :
    orderOf x = Nat.lcm (orderOf (ZMod.castHom (dvd_mul_right m n) (ZMod m) x))
      (orderOf (ZMod.castHom (dvd_mul_left n m) (ZMod n) x)) := by
  rw [← MulEquiv.orderOf_eq (ZMod.chineseRemainder h).toMulEquiv x, Prod.orderOf]
  have h1 : (RingHom.fst (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h).toRingHom =
      ZMod.castHom (dvd_mul_right m n) (ZMod m) := Subsingleton.elim _ _
  have h2 : (RingHom.snd (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h).toRingHom =
      ZMod.castHom (dvd_mul_left n m) (ZMod n) := Subsingleton.elim _ _
  rw [← h1, ← h2]
  rfl

/-- **The 360 dial as three rods.** For every `x` on the 360 dial, its turn order is the lcm of
its turn orders mod `8`, mod `9` and mod `5`. -/
theorem orderOf_360_eq_lcm_rods (x : ZMod 360) :
    orderOf x = Nat.lcm (Nat.lcm (orderOf (ZMod.castHom (by norm_num : 8 ∣ 360) (ZMod 8) x))
      (orderOf (ZMod.castHom (by norm_num : 9 ∣ 360) (ZMod 9) x)))
      (orderOf (ZMod.castHom (by norm_num : 5 ∣ 360) (ZMod 5) x)) := by
  have h := orderOf_eq_lcm_rods (m := 72) (n := 5) (by norm_num) x
  have h' := orderOf_eq_lcm_rods (m := 8) (n := 9) (by norm_num)
    (ZMod.castHom (dvd_mul_right 72 5) (ZMod 72) x)
  have e8 : (ZMod.castHom (dvd_mul_right 8 9) (ZMod 8)).comp
      (ZMod.castHom (dvd_mul_right 72 5) (ZMod 72)) =
      ZMod.castHom (by norm_num : 8 ∣ 360) (ZMod 8) := Subsingleton.elim _ _
  have e9 : (ZMod.castHom (dvd_mul_left 9 8) (ZMod 9)).comp
      (ZMod.castHom (dvd_mul_right 72 5) (ZMod 72)) =
      ZMod.castHom (by norm_num : 9 ∣ 360) (ZMod 9) := Subsingleton.elim _ _
  have e5 : ZMod.castHom (dvd_mul_left 5 72) (ZMod 5) =
      ZMod.castHom (by norm_num : 5 ∣ 360) (ZMod 5) := Subsingleton.elim _ _
  rw [h, h', ← e8, ← e9, ← e5]
  rfl

end RodOrders
