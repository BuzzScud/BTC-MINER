module

public import RequestProject.RodCircles
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Scaling a rod to its square (kernel-checked instances)

In these instances, going from the rod `p` to the rod `p²` multiplies the number of points on a
circle by `p`:

* `rod_121_square`, `rod_121_hex`: `121 = 11²` carries `11·12 = 132` points on both circles
  (the rod `11` carries `12`);
* `rod_361_hex`: `361 = 19²` carries `19·18 = 342` points on the hexagonal (flower) circle
  (the rod `19` carries `18`).

These are finite checks run by the Lean kernel, not a general theorem about all `p^k`.

REPAIR CONTRACT: this module MUST retain the three historical theorem statements and MUST
use only kernel-checked proof terms.  It MAY reorganize finite enumeration into rows so that
checking the `361` rod does not construct one filtered set of `130321` ordered pairs.  The
generic bridge below proves that the row computation is the original mathematical count;
the concrete proof steps SHALL remain kernel decisions.  The parent project proof gate MUST
audit the resulting theorem assumptions before treating these instances as accepted evidence.
-/

@[expose] public section

namespace RodCircles

/-- Count a quadratic-form solution set one row at a time.  This identity supplies the semantic
bridge from bounded finite computations back to the exact historical `formPts` statements. -/
theorem formPts_card_rows (R : Type*) [CommRing R] [Fintype R] [DecidableEq R]
    (a b c : ℤ) :
    (formPts R a b c).card =
      ∑ x : R, (Finset.univ.filter fun y : R =>
        (a : R) * x ^ 2 + (b : R) * x * y + (c : R) * y ^ 2 = 1).card := by
  unfold formPts
  simp only [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]

-- Rewriting SHALL use the proved count bridge rather than unfold a concrete pair enumeration
-- while solving elaborator constraints. This local transparency setting changes no definition.
attribute [local irreducible] formPts

theorem rod_121_square :
    (formPts (ZMod 121) 1 0 1).card = 132 := by
  rw [formPts_card_rows]
  decide +kernel

theorem rod_121_hex : (formPts (ZMod 121) 1 1 1).card = 132 := by
  rw [formPts_card_rows]
  decide +kernel

/-- A row of the hexagonal conic on the 361 rod. The natural input is cast into the exact
residue ring; the finite certificate SHALL count all 361 possible second coordinates. -/
def hex361Row (x : ℕ) : ℕ :=
  (Finset.univ.filter fun y : ZMod 361 =>
    (1 : ZMod 361) * (x : ZMod 361) ^ 2 +
      (1 : ZMod 361) * (x : ZMod 361) * y + (1 : ZMod 361) * y ^ 2 = 1).card

/-- One nineteenth of the first-coordinate range. Each certificate contains 19 complete rows. -/
def hex361Block (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range 19, hex361Row (j * 19 + i)

/-- Exact finite partition; no row is omitted or counted twice. -/
theorem sum_range_blocks (k w : ℕ) (f : ℕ → ℕ) :
    (∑ i ∈ Finset.range (k * w), f i) =
      ∑ j ∈ Finset.range k, ∑ i ∈ Finset.range w, f (j * w + i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem rod361_block_00 : hex361Block 0 = 18 := by
  decide +kernel

theorem rod361_block_01 : hex361Block 1 = 18 := by
  decide +kernel

theorem rod361_block_02 : hex361Block 2 = 18 := by
  decide +kernel

theorem rod361_block_03 : hex361Block 3 = 18 := by
  decide +kernel

theorem rod361_block_04 : hex361Block 4 = 18 := by
  decide +kernel

theorem rod361_block_05 : hex361Block 5 = 18 := by
  decide +kernel

theorem rod361_block_06 : hex361Block 6 = 18 := by
  decide +kernel

theorem rod361_block_07 : hex361Block 7 = 18 := by
  decide +kernel

theorem rod361_block_08 : hex361Block 8 = 18 := by
  decide +kernel

theorem rod361_block_09 : hex361Block 9 = 18 := by
  decide +kernel

theorem rod361_block_10 : hex361Block 10 = 18 := by
  decide +kernel

theorem rod361_block_11 : hex361Block 11 = 18 := by
  decide +kernel

theorem rod361_block_12 : hex361Block 12 = 18 := by
  decide +kernel

theorem rod361_block_13 : hex361Block 13 = 18 := by
  decide +kernel

theorem rod361_block_14 : hex361Block 14 = 18 := by
  decide +kernel

theorem rod361_block_15 : hex361Block 15 = 18 := by
  decide +kernel

theorem rod361_block_16 : hex361Block 16 = 18 := by
  decide +kernel

theorem rod361_block_17 : hex361Block 17 = 18 := by
  decide +kernel

theorem rod361_block_18 : hex361Block 18 = 18 := by
  decide +kernel

/-- Expand the 19-term outer sum with an abstract function, before inserting costly row counts.
This proof is symbolic and SHALL NOT evaluate any quadratic-form enumeration. -/
theorem sum_range_nineteen (f : ℕ → ℕ) :
    (∑ i ∈ Finset.range 19, f i) =
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

-- The final assembly SHALL use established block equalities, without re-expanding their
-- finite enumerations during simplifier matching. The definitions remain fully transparent
-- to the kernel and were evaluated in the certificates above.
attribute [local irreducible] hex361Row hex361Block

theorem rod_361_hex : (formPts (ZMod 361) 1 1 1).card = 342 := by
  rw [formPts_card_rows]
  calc
    _ = ∑ i ∈ Finset.range 361, hex361Row i := by
      rw [← Fin.sum_univ_eq_sum_range]
      change (∑ x : ZMod 361, _) = ∑ x : ZMod 361, hex361Row x.val
      apply Finset.sum_congr rfl
      intro x _
      simp only [hex361Row, ZMod.natCast_zmod_val, Int.cast_one]
    _ = ∑ j ∈ Finset.range 19, hex361Block j := by
      unfold hex361Block
      exact sum_range_blocks 19 19 hex361Row
    _ = 342 := by
      rw [sum_range_nineteen, rod361_block_00, rod361_block_01, rod361_block_02, rod361_block_03, rod361_block_04, rod361_block_05, rod361_block_06, rod361_block_07, rod361_block_08, rod361_block_09, rod361_block_10, rod361_block_11, rod361_block_12, rod361_block_13, rod361_block_14, rod361_block_15, rod361_block_16, rod361_block_17, rod361_block_18]


end RodCircles
