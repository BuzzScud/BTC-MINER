module

public import Mathlib
public import LatticeCalc.Verified.FractalAbacus
public import RequestProject.SoddyCounts
public import RequestProject.FlowerFractal

/-!
# The system's structures on the fractal abacus

`LatticeCalc/Verified/FractalAbacus.lean` proves the general facts about the fractal abacus
(bases fixed, rods deepened without bound).  This file places the project's main structures on
it.

* **The dial family is one fractal abacus.**  On the bases `2, 3, 5`, the 360-dial is the level
  `(3, 2, 1)` (rods `8, 9, 5`, `dial360_moduli`), 144000 is the level `(7, 2, 3)`, and the
  base-60 zoom `360 · 60ᵏ` is the level `(3 + 2k, 2 + k, 1 + k)` (`dial_zoom`).  Every calculation
  on the 144000-dial projects exactly onto the same calculation on the 360-dial
  (`dial_144000_to_360`).
* **The core primes** `11, 19, 71, 97, 109` form a fractal abacus (`coreAbacus`).
* **The flower tower.**  On the single base `p`, the level `k` is the rod `pᵏ`, and the flower
  circle `x² + xy + y² = 1` mod `pᵏ` is exactly the set of columns on which the flower formula
  reads `1` (`flower_on_rod`).  A flower point at a deeper level projects to a flower point at
  every shallower level (`flower_proj`); `FlowerFractal.card_fiber` counts the lifts.
* **The Soddy sphere counts** as an abacus program (`soddyProg`), run at any depth `N`, read back
  exactly at every deep enough level, and equal to one fifth of the number of new spheres of
  generation `N + 1` (`soddy_on_fractal`).
* The **Descartes form** and the **dot product** (E₈, Leech inner products) as formulas, with
  every relation between them decided on the rods at all deep enough levels.
-/

@[expose] public section

namespace FractalModels

open LatticeCalc.Verified.AbacusSystem LatticeCalc.Verified.Fractal LatticeCalc.Verified.RNS

/-! ## The dial family: bases 2, 3, 5 -/

/-- The fractal abacus of the dial: bases `2, 3, 5`. -/
def dialAbacus : FractalAbacus 3 where
  base := ![2, 3, 5]
  two_le := by decide
  coprime := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> decide

/-- The 360-dial is the level `(3, 2, 1)`: rods `8, 9, 5`. -/
theorem dial360_moduli : (dialAbacus.level ![3, 2, 1]).m = ![8, 9, 5] := by
  funext i; fin_cases i <;> rfl

theorem dial360_capacity : capacity (dialAbacus.level ![3, 2, 1]).m = 360 := by
  simp [FractalAbacus.capacity_level, Fin.prod_univ_three, dialAbacus]

/-- 144000 is the level `(7, 2, 3)` of the same abacus: rods `128, 9, 125`. -/
theorem dial144000_moduli : (dialAbacus.level ![7, 2, 3]).m = ![128, 9, 125] := by
  funext i; fin_cases i <;> rfl

theorem dial144000_capacity : capacity (dialAbacus.level ![7, 2, 3]).m = 144000 := by
  simp [FractalAbacus.capacity_level, Fin.prod_univ_three, dialAbacus]

/-- **The base-60 zoom is deepening**: `360 · 60ᵏ` is the level `(3 + 2k, 2 + k, 1 + k)`. -/
theorem dial_zoom (k : ℕ) :
    capacity (dialAbacus.level ![3 + 2 * k, 2 + k, 1 + k]).m = 360 * 60 ^ k := by
  simp only [FractalAbacus.capacity_level, Fin.prod_univ_three, dialAbacus]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [show (60 : ℕ) = 2 ^ 2 * 3 * 5 by norm_num, mul_pow, mul_pow, ← pow_mul]
  ring

/-- **The 360-dial is a projection of the 144000-dial**: any formula run on the 144000-dial and
reduced is the same formula run on the 360-dial. -/
theorem dial_144000_to_360 {V : Type} (env : V → Fin 3 → ℕ) (f : Formula V) :
    dialAbacus.proj ![3, 2, 1] ((dialAbacus.level ![7, 2, 3]).run env f) =
      (dialAbacus.level ![3, 2, 1]).run (fun v => dialAbacus.proj ![3, 2, 1] (env v)) f :=
  dialAbacus.run_proj (by decide) env f

/-! ## The core primes -/

/-- The fractal abacus of the five core primes `11, 19, 71, 97, 109`. -/
def coreAbacus : FractalAbacus 5 where
  base := ![11, 19, 71, 97, 109]
  two_le := by decide
  coprime := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> decide

/-- At depth 1 the core abacus has capacity `11 · 19 · 71 · 97 · 109`. -/
theorem core_capacity_one : capacity (coreAbacus.uniform 1).m = 11 * 19 * 71 * 97 * 109 := by
  simp [FractalAbacus.uniform, FractalAbacus.capacity_level, Fin.prod_univ_five, coreAbacus]

/-! ## The flower tower on one base -/

/-- The single-base fractal abacus: level `k` is the rod `pᵏ`. -/
def tower (p : ℕ) (hp : 2 ≤ p) : FractalAbacus 1 where
  base := ![p]
  two_le := fun i => by fin_cases i; exact hp
  coprime := fun i j hij => absurd (Subsingleton.elim i j) hij

/-- The flower formula `x² + xy + y²`. -/
def flowerF : Formula (Fin 2) :=
  .add (.add (.pow (.var 0) 2) (.mul (.var 0) (.var 1))) (.pow (.var 1) 2)

theorem flowerF_eval (x : Fin 2 → ℤ) : flowerF.eval x = x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2 := rfl

/-- **The flower circle mod `q` is the solution set of the flower formula on the rod `q`.** -/
theorem flower_on_rod {q : ℕ} [NeZero q] (a b : ZMod q) :
    FlowerClock.fnorm (a, b) = 1 ↔
      flowerF.onRod q ![a.val, b.val] = (Formula.const 1 : Formula (Fin 2)).onRod q ![a.val, b.val] := by
  rw [RodFacts.onRod_eq_iff (Nat.pos_of_ne_zero (NeZero.ne q))]
  simp [flowerF, Formula.eval, FlowerClock.fnorm]

/-- **Flower points project down the tower**: a column that is a flower point on the rod
`p^{k'}` projects to a flower point on the rod `pᵏ` for every `k ≤ k'`. -/
theorem flower_proj (p : ℕ) (hp : 2 ≤ p) {k k' : ℕ} (hk : k ≤ k') (env : Fin 2 → Fin 1 → ℕ)
    (h : ((tower p hp).level ![k']).run env flowerF =
      ((tower p hp).level ![k']).run env (.const 1)) :
    ((tower p hp).level ![k]).run (fun v => (tower p hp).proj ![k] (env v)) flowerF =
      ((tower p hp).level ![k]).run (fun v => (tower p hp).proj ![k] (env v)) (.const 1) :=
  (tower p hp).solution_proj (fun i => by fin_cases i; simpa using hk) env _ _ h

/-! ## The Soddy sphere counts as an abacus program -/

open LatticeCalc.Verified.RodJump

/-- One generation step on slots `0, 1, 2` (holding `uₙ, uₙ₊₁, uₙ₊₂`), with slot 3 as scratch. -/
def soddyStep : Abacus.Program :=
  [(3, .sub (.add (.mul (.const 3) (.var 2)) (.mul (.const 3) (.var 1))) (.mul (.const 6) (.var 0))),
   (0, .var 1), (1, .var 2), (2, .var 3)]

/-- `N` generation steps. -/
def soddyProg (N : ℕ) : Abacus.Program := (List.replicate N soddyStep).flatten

lemma evalProg_append (P Q : Abacus.Program) (x : ℕ → ℤ) :
    Abacus.evalProg (P ++ Q) x = Abacus.evalProg Q (Abacus.evalProg P x) := by
  induction P generalizing x with
  | nil => rfl
  | cons s rest ih => obtain ⟨t, f⟩ := s; exact ih _

lemma evalProg_step (x : ℕ → ℤ) (m : ℕ) (h0 : x 0 = soddyU m) (h1 : x 1 = soddyU (m + 1))
    (h2 : x 2 = soddyU (m + 2)) :
    Abacus.evalProg soddyStep x 0 = soddyU (m + 1) ∧
      Abacus.evalProg soddyStep x 1 = soddyU (m + 2) ∧
      Abacus.evalProg soddyStep x 2 = soddyU (m + 3) := by
  simp only [soddyStep, Abacus.evalProg, Formula.eval, Function.update]
  simp [h0, h1, h2, soddyU]

lemma evalProg_soddy (N : ℕ) :
    ∀ x : ℕ → ℤ, ∀ m, x 0 = soddyU m → x 1 = soddyU (m + 1) → x 2 = soddyU (m + 2) →
      Abacus.evalProg (soddyProg N) x 0 = soddyU (m + N) := by
  induction N with
  | zero => intro x m h0 _ _; simpa [soddyProg] using h0
  | succ N ih =>
    intro x m h0 h1 h2
    rw [soddyProg, List.replicate_succ, List.flatten_cons, evalProg_append]
    obtain ⟨e0, e1, e2⟩ := evalProg_step x m h0 h1 h2
    rw [show m + (N + 1) = (m + 1) + N by ring]
    exact ih _ (m + 1) e0 e1 e2

/-- **The program computes the Soddy counts**: started on `u₀, u₁, u₂`, slot 0 ends with `u_N`. -/
theorem soddyProg_spec (N : ℕ) : Abacus.evalProg (soddyProg N) (fun s => soddyU s) 0 = soddyU N := by
  simpa using evalProg_soddy N (fun s => soddyU s) 0 rfl rfl rfl

/-- **The Soddy counts on the fractal abacus, at every depth**: for every generation `N`, the
program run on every deep enough level of any fractal abacus reads back `u_N`, and five times
that is the number of new spheres in generation `N + 1`. -/
theorem soddy_on_fractal {n : ℕ} [NeZero n] (F : FractalAbacus n) (N : ℕ) :
    ∃ K, ∀ k ≥ K,
      5 * (F.uniform k).readBack
        (Abacus.runProg (F.uniform k) (soddyProg N) (fun s => (F.uniform k).enc (soddyU s)) 0) =
      ((SoddyCounts.newSpheres (N + 1)).ncard : ℤ) := by
  obtain ⟨K, hK⟩ := F.prog_arbitrary_precision (soddyProg N) (fun s => soddyU s) 0
  refine ⟨K, fun k hk => ?_⟩
  rw [hK k hk, soddyProg_spec, SoddyCounts.newSpheres_ncard_succ]

/-! ## Descartes form and inner products -/

/-- The Descartes form `(a + b + c + d)² − 2(a² + b² + c² + d²)`. -/
def descartesF : Formula (Fin 4) :=
  .sub (.pow (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.var 3)) 2)
    (.mul (.const 2) (.add (.add (.add (.pow (.var 0) 2) (.pow (.var 1) 2)) (.pow (.var 2) 2))
      (.pow (.var 3) 2)))

theorem descartesF_eval (x : Fin 4 → ℤ) :
    descartesF.eval x = (x 0 + x 1 + x 2 + x 3) ^ 2 - 2 * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) :=
  rfl

/-- **Descartes relations on the fractal abacus**: whether four integer curvatures satisfy the
Descartes relation is decided rod by rod at every deep enough level. -/
theorem descartes_on_fractal {n : ℕ} [NeZero n] (F : FractalAbacus n) (x : Fin 4 → ℤ) :
    ∃ K, ∀ k ≥ K,
      ((x 0 + x 1 + x 2 + x 3) ^ 2 = 2 * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) ↔
        (F.uniform k).run (fun v => (F.uniform k).enc (x v)) descartesF =
          (F.uniform k).run (fun v => (F.uniform k).enc (x v)) (.const 0)) := by
  obtain ⟨K, hK⟩ := F.relation_eventually descartesF (.const 0) x
  refine ⟨K, fun k hk => ?_⟩
  rw [← hK k hk, descartesF_eval]
  simp only [Formula.eval]
  constructor <;> intro h <;> linarith

/-- Rename the quantities of a formula along `g`. -/
def mapVars {V W : Type} (g : V → W) : Formula V → Formula W
  | .var v => .var (g v)
  | .const c => .const c
  | .add f f' => .add (mapVars g f) (mapVars g f')
  | .sub f f' => .sub (mapVars g f) (mapVars g f')
  | .mul f f' => .mul (mapVars g f) (mapVars g f')
  | .pow f e => .pow (mapVars g f) e

lemma mapVars_eval {V W : Type} (g : V → W) (f : Formula V) (x : W → ℤ) :
    (mapVars g f).eval x = f.eval (x ∘ g) := by
  induction f with
  | var v => rfl
  | const c => rfl
  | add f f' hf hf' => simp [mapVars, Formula.eval, hf, hf']
  | sub f f' hf hf' => simp [mapVars, Formula.eval, hf, hf']
  | mul f f' hf hf' => simp [mapVars, Formula.eval, hf, hf']
  | pow f e hf => simp [mapVars, Formula.eval, hf]

/-- The dot product of two `d`-vectors: `Σ xᵢ yᵢ` (E₈ and Leech inner products for `d = 8, 24`). -/
def dotF : (d : ℕ) → Formula (Fin d ⊕ Fin d)
  | 0 => .const 0
  | d + 1 => .add (mapVars (Sum.map Fin.castSucc Fin.castSucc) (dotF d))
      (.mul (.var (.inl (Fin.last d))) (.var (.inr (Fin.last d))))

/-- **The dot product formula computes `Σ xᵢ yᵢ`.** -/
theorem dotF_eval (d : ℕ) (x : Fin d ⊕ Fin d → ℤ) :
    (dotF d).eval x = ∑ i, x (.inl i) * x (.inr i) := by
  induction d with
  | zero => simp [dotF, Formula.eval]
  | succ d ih =>
    rw [dotF, Formula.eval, mapVars_eval, ih, Fin.sum_univ_castSucc]
    rfl

/-- **Inner-product relations on the fractal abacus**: for integer vectors, whether `x · y = c`
is decided rod by rod at every deep enough level. -/
theorem dot_on_fractal {n : ℕ} [NeZero n] (F : FractalAbacus n) (d : ℕ) (x : Fin d ⊕ Fin d → ℤ)
    (c : ℤ) :
    ∃ K, ∀ k ≥ K, (∑ i, x (.inl i) * x (.inr i) = c ↔
      (F.uniform k).run (fun v => (F.uniform k).enc (x v)) (dotF d) =
        (F.uniform k).run (fun v => (F.uniform k).enc (x v)) (.const c)) := by
  obtain ⟨K, hK⟩ := F.relation_eventually (dotF d) (.const c) x
  exact ⟨K, fun k hk => by rw [← hK k hk, dotF_eval]; rfl⟩

end FractalModels
