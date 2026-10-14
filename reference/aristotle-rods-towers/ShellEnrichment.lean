module

public import Mathlib

/-!
# Do 11 and 71 enrich the larger shells?

In the plane (square grid) the primes `11` and `71` are inert and add no new lattice points.  Here
we count lattice points on spheres in 3 and 4 dimensions.

`shellCount d n` is the number of integer vectors `(x₁, …, x_d)` with `x₁² + ⋯ + x_d² = n`,
computed by peeling off the last coordinate (`x_d = 0` or `x_d = ±i` with `i² ≤ n`).

* `mod_eight_no_three_squares` — no integer of the form `8k + 7` is a sum of three squares.  Since
  `71 ≡ 7 (mod 8)`, the sphere of squared radius `71` in 3D is empty (`seventyone_empty_3d`).
* `shell_table` (kernel-checked) — counts on the circle (`d = 2`), the sphere (`d = 3`) and the
  3-sphere (`d = 4`):

  | n    | d = 2 | d = 3 | d = 4 |
  |------|-------|-------|-------|
  | 1    | 4     | 6     | 8     |
  | 11   | 0     | 24    | 96    |
  | 19   | 0     | 24    | 160   |
  | 71   | 0     | 0     | 576   |
  | 97   | 8     | 48    | 784   |
  | 109  | 8     | 72    | 880   |
  | 121  | 4     | 78    | 1064  |
  | 209  | 0     | 240   | 1920  |
  | 5041 | 4     | 438   | —     |

  In 4D every odd prime `p` gives `8 (p + 1)` points (`96 = 8·12` for `11`, `576 = 8·72` for `71`):
  the same `p + 1` that counts the circle on the rod `p` when `p` is inert.  In 3D, squaring
  multiplies the 6 axis points by `13 = 11 + 2` for `11` and by `73 = 71 + 2` for `71`.
-/

@[expose] public section

namespace ShellEnrichment

/-- Number of integers `x` with `x² = n`. -/
def sqCount (n : ℕ) : ℕ := if Nat.sqrt n * Nat.sqrt n = n then (if n = 0 then 1 else 2) else 0

/-- `shellCount d n` = number of `(x₁, …, x_d) ∈ ℤ^d` with `x₁² + ⋯ + x_d² = n`. -/
def shellCount : ℕ → ℕ → ℕ
  | 0, n => if n = 0 then 1 else 0
  | 1, n => sqCount n
  | d + 2, n => shellCount (d + 1) n +
      2 * ((List.range (Nat.sqrt n)).map (fun i => shellCount (d + 1) (n - (i + 1) ^ 2))).sum

/-- No integer `≡ 7 (mod 8)` is a sum of three squares. -/
theorem mod_eight_no_three_squares (x y z : ℤ) (n : ℕ) (hn : n % 8 = 7) :
    x ^ 2 + y ^ 2 + z ^ 2 ≠ n := by
  intro h
  have h8 : ((x ^ 2 + y ^ 2 + z ^ 2 : ℤ) : ZMod 8) = ((n : ℤ) : ZMod 8) := by rw [h]
  push_cast at h8
  have hn' : ((n : ℕ) : ZMod 8) = 7 := by
    rw [← ZMod.natCast_mod, hn]; rfl
  rw [hn'] at h8
  have key : ∀ a b c : ZMod 8, a ^ 2 + b ^ 2 + c ^ 2 ≠ 7 := by decide
  exact key _ _ _ h8

theorem seventyone_empty_3d (x y z : ℤ) : x ^ 2 + y ^ 2 + z ^ 2 ≠ 71 :=
  mod_eight_no_three_squares x y z 71 (by norm_num)

/-- The shell counts of the table above (kernel-checked). -/
theorem shell_table :
    [1, 11, 19, 71, 97, 109, 121, 209].map (fun n => (shellCount 2 n, shellCount 3 n, shellCount 4 n))
      = [(4, 6, 8), (0, 24, 96), (0, 24, 160), (0, 0, 576), (8, 48, 784), (8, 72, 880),
         (4, 78, 1064), (0, 240, 1920)] := by
  decide +kernel

theorem shell_5041 : shellCount 2 5041 = 4 ∧ shellCount 3 5041 = 438 := by
  decide +kernel

/-- In 4D each core prime `p` carries `8 (p + 1)` points. -/
theorem four_d_core :
    [11, 19, 71, 97, 109].map (fun p => shellCount 4 p) =
      [11, 19, 71, 97, 109].map (fun p => 8 * (p + 1)) := by
  decide +kernel

end ShellEnrichment
