module

public import Mathlib
public import LatticeCalc.Verified.AbacusSystem
public import LatticeCalc.Verified.SharedClaims

/-!
# The fractal abacus: arbitrary precision by deepening the rods

The shared abacus of `AbacusSystem` has a fixed frame of rods, so a fixed capacity.  The
**fractal abacus** fixes only the *bases* `b₀, …, b_{n−1}` (pairwise coprime, each `≥ 2`) and lets
every rod grow in depth: at depth `d` the rod `i` has modulus `bᵢ^{dᵢ}`.  Each rod is a tower

  `bᵢ ← bᵢ² ← bᵢ³ ← ⋯`

in which every level is `bᵢ` copies of the level below it (`card_fibre`), and every calculation
on a deeper level projects exactly onto the same calculation on a shallower level (`run_proj`).
So the abacus at every depth is a self-similar copy of the abacus at every other depth, and the
capacity is unbounded (`capacity_uniform_ge`): any exact integer calculation fits once the rods
are deep enough.

* `FractalAbacus`, `level`, `uniform` — the bases and the ordinary abacus at a given depth.
* `Formula.onRod_congr`, `Formula.onRod_dvd` — a rod's result depends only on the inputs mod that
  rod, and a deeper rod's result reduces to a shallower rod's result.
* `RodFacts.onRod_eq_iff` — an equation on one rod is the congruence of the true values.
* `enc_proj`, `run_proj`, `runProg_proj` — **self-similarity**: projecting a deep column gives the
  shallow column, for single formulas and for whole programs.
* `solution_proj` — an equation satisfied at some depth is satisfied at every shallower depth.
* `capacity_level`, `capacity_deepen`, `capacity_uniform_ge` — capacity is `∏ bᵢ^{dᵢ}`; deepening
  one rod multiplies it by that rod's base; at uniform depth `k` it is at least `2ᵏ`.
* `capacity_dvd_of_le`, `congruence_at_level` — deepening keeps every divisor of the capacity,
  and a congruence whose modulus divides the capacity is decided rod by rod for integers of any
  size.
* `le_eventually` — order needs one read-back, which is exact at every deep enough level.
* `fraction_eq_eventually` — equations between fractions, by cross-multiplication.
* `card_fibre` — on one rod, exactly `b` residues at depth `k + 1` lie over each residue at
  depth `k`.
* `arbitrary_precision`, `prog_arbitrary_precision` — for every formula (or program) and every
  input, all deep enough levels read back the exact value.
* `system_arbitrary_precision` — one depth serves a whole finite system of formulas at once.
* `relation_eventually` — every relation `f = g` is decided rod by rod at all deep enough levels.
* `Formula.exists_of_mvPolynomial` — every integer polynomial in any number of variables is a
  formula of the abacus, so every polynomial computation of the system runs on it.
-/

@[expose] public section

namespace LatticeCalc.Verified.Fractal

open Finset LatticeCalc.Verified.RNS LatticeCalc.Verified.AbacusSystem

variable {V : Type}

/-! ## Rods of different depth -/

namespace RodFacts

/-- A rod's result depends on the inputs only through their residues on that rod. -/
theorem onRod_congr {q : ℕ} {r r' : V → ℕ} (h : ∀ v, r v % q = r' v % q) (f : Formula V) :
    f.onRod q r = f.onRod q r' := by
  induction f with
  | var v => exact h v
  | const c => rfl
  | add f g hf hg => simp only [Formula.onRod, hf, hg]
  | sub f g hf hg => simp only [Formula.onRod, hf, hg]
  | mul f g hf hg => simp only [Formula.onRod, hf, hg]
  | pow f e hf => simp only [Formula.onRod, hf]

/-- The residue a rod computes is the true value of the formula on the rod's own inputs. -/
theorem onRod_cast {q : ℕ} (hq : 0 < q) (r : V → ℕ) (f : Formula V) :
    ((f.onRod q r : ℕ) : ZMod q) = (f.eval (fun v => (r v : ℤ)) : ZMod q) := by
  have h := Formula.onRod_spec hq (fun v => (r v : ℤ)) f
  rw [← h, onRod_congr (r' := fun v => (((r v : ℤ) % (q : ℤ)).toNat)) _ f]
  intro v
  have : (((r v : ℤ) % (q : ℤ)).toNat) = r v % q := by omega
  simp only [this, Nat.mod_mod]

/-- **A deeper rod reduces to a shallower rod**: if `q ∣ Q`, the result on the rod `Q`, reduced
mod `q`, is the result on the rod `q`. -/
theorem onRod_dvd {q Q : ℕ} (hq : 0 < q) (hQ : 0 < Q) (hqQ : q ∣ Q) (r : V → ℕ)
    (f : Formula V) : f.onRod Q r % q = f.onRod q r := by
  have h1 := onRod_cast hQ r f
  have h2 := onRod_cast hq r f
  have h3 := congrArg (ZMod.castHom hqQ (ZMod q)) h1
  rw [map_natCast, map_intCast, ← h2] at h3
  rw [ZMod.natCast_eq_natCast_iff'] at h3
  rw [h3, Nat.mod_eq_of_lt (Formula.onRod_lt hq r f)]

/-- **Equations on one rod**: two formulas agree on the rod `q` exactly when their true values
agree modulo `q`. -/
theorem onRod_eq_iff {q : ℕ} (hq : 0 < q) (r : V → ℕ) (f g : Formula V) :
    f.onRod q r = g.onRod q r ↔
      (f.eval (fun v => (r v : ℤ)) : ZMod q) = (g.eval (fun v => (r v : ℤ)) : ZMod q) := by
  rw [← onRod_cast hq, ← onRod_cast hq]
  constructor
  · intro h; rw [h]
  · intro h
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (Formula.onRod_lt hq r f),
      Nat.mod_eq_of_lt (Formula.onRod_lt hq r g)] at h
    exact h

end RodFacts

open RodFacts

/-! ## The fractal abacus -/

/-- A fractal abacus: pairwise coprime bases, each at least `2`.  Its rods may be taken to any
depth. -/
structure FractalAbacus (n : ℕ) where
  base : Fin n → ℕ
  two_le : ∀ i, 2 ≤ base i
  coprime : Pairwise fun i j => Nat.Coprime (base i) (base j)

variable {n : ℕ}

namespace FractalAbacus

/-- The ordinary abacus at depth `d`: rod `i` has modulus `bᵢ^{dᵢ}`. -/
def level (F : FractalAbacus n) (d : Fin n → ℕ) : Abacus n where
  m i := F.base i ^ d i
  rods := ⟨fun i => pow_pos (by linarith [F.two_le i]) _,
    fun _ _ hij => Nat.Coprime.pow _ _ (F.coprime hij)⟩

/-- All rods at the same depth `k`. -/
def uniform (F : FractalAbacus n) (k : ℕ) : Abacus n := F.level fun _ => k

/-- Projection of a column from a deeper level onto depth `d`. -/
def proj (F : FractalAbacus n) (d : Fin n → ℕ) (col : Fin n → ℕ) : Fin n → ℕ :=
  fun i => col i % F.base i ^ d i

theorem level_m (F : FractalAbacus n) (d : Fin n → ℕ) (i : Fin n) :
    (F.level d).m i = F.base i ^ d i := rfl

/-- **Self-similarity of numbers**: the column of `x` at a deeper level projects to its column
at a shallower level. -/
theorem enc_proj (F : FractalAbacus n) {d d' : Fin n → ℕ} (hd : ∀ i, d i ≤ d' i) (x : ℤ) :
    F.proj d ((F.level d').enc x) = (F.level d).enc x := by
  funext i
  simp only [proj, Abacus.enc, encode, level_m]
  have hq : (0 : ℤ) < ((F.base i ^ d i : ℕ) : ℤ) := by
    exact_mod_cast pow_pos (by linarith [F.two_le i]) _
  have hQ : (0 : ℤ) < ((F.base i ^ d' i : ℕ) : ℤ) := by
    exact_mod_cast pow_pos (by linarith [F.two_le i]) _
  have hdvd : ((F.base i ^ d i : ℕ) : ℤ) ∣ ((F.base i ^ d' i : ℕ) : ℤ) := by
    exact_mod_cast pow_dvd_pow _ (hd i)
  apply Nat.cast_injective (R := ℤ)
  rw [Int.natCast_mod, Int.toNat_of_nonneg (Int.emod_nonneg _ hQ.ne'),
    Int.toNat_of_nonneg (Int.emod_nonneg _ hq.ne'), Int.emod_emod_of_dvd _ hdvd]

/-- **Self-similarity of calculations**: a formula run at a deeper level and projected is the
same formula run at the shallower level on the projected inputs. -/
theorem run_proj (F : FractalAbacus n) {d d' : Fin n → ℕ} (hd : ∀ i, d i ≤ d' i)
    (env : V → Fin n → ℕ) (f : Formula V) :
    F.proj d ((F.level d').run env f) = (F.level d).run (fun v => F.proj d (env v)) f := by
  funext i
  have h0 : 0 < F.base i := by linarith [F.two_le i]
  simp only [proj, Abacus.run, level_m]
  rw [onRod_dvd (pow_pos h0 _) (pow_pos h0 _) (pow_dvd_pow _ (hd i))]
  exact onRod_congr (fun v => by simp) f

/-- **Self-similarity of programs**: a whole program run at a deeper level projects slot by slot
onto the same program at the shallower level. -/
theorem runProg_proj (F : FractalAbacus n) {d d' : Fin n → ℕ} (hd : ∀ i, d i ≤ d' i)
    (P : Abacus.Program) (env : ℕ → Fin n → ℕ) (s : ℕ) :
    F.proj d (Abacus.runProg (F.level d') P env s) =
      Abacus.runProg (F.level d) P (fun t => F.proj d (env t)) s := by
  induction P generalizing env with
  | nil => rfl
  | cons step rest ih =>
    obtain ⟨t, f⟩ := step
    simp only [Abacus.runProg]
    rw [ih]
    congr 1
    funext u
    by_cases hu : u = t
    · subst hu; simp [run_proj F hd]
    · simp [hu]

/-- An equation `f = g` that holds on the columns at some depth holds at every shallower
depth. -/
theorem solution_proj (F : FractalAbacus n) {d d' : Fin n → ℕ} (hd : ∀ i, d i ≤ d' i)
    (env : V → Fin n → ℕ) (f g : Formula V)
    (h : (F.level d').run env f = (F.level d').run env g) :
    (F.level d).run (fun v => F.proj d (env v)) f =
      (F.level d).run (fun v => F.proj d (env v)) g := by
  rw [← run_proj F hd, ← run_proj F hd, h]

/-! ## Capacity grows without bound -/

theorem capacity_level (F : FractalAbacus n) (d : Fin n → ℕ) :
    capacity (F.level d).m = ∏ i, F.base i ^ d i := rfl

/-- **Deepening one rod multiplies the capacity by its base.** -/
theorem capacity_deepen (F : FractalAbacus n) (d : Fin n → ℕ) (i : Fin n) :
    capacity (F.level (Function.update d i (d i + 1))).m = F.base i * capacity (F.level d).m := by
  rw [capacity_level, capacity_level]
  have h : ∀ j, F.base j ^ Function.update d i (d i + 1) j =
      F.base j ^ d j * (if j = i then F.base j else 1) := by
    intro j
    by_cases hj : j = i
    · subst hj; simp [pow_succ]
    · simp [hj]
  rw [Finset.prod_congr rfl (fun j _ => h j), Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp [mul_comm]

/-- **Unbounded capacity**: at uniform depth `k` the capacity is at least `2ᵏ`. -/
theorem capacity_uniform_ge [NeZero n] (F : FractalAbacus n) (k : ℕ) :
    2 ^ k ≤ capacity (F.uniform k).m := by
  have h1 : (2 ^ k) ^ (univ : Finset (Fin n)).card ≤ ∏ i, F.base i ^ k :=
    Finset.pow_card_le_prod _ _ _ (fun i _ => Nat.pow_le_pow_left (F.two_le i) k)
  have h2 : 2 ^ k ≤ (2 ^ k) ^ (univ : Finset (Fin n)).card := by
    apply Nat.le_self_pow
    simp [NeZero.ne n]
  exact h2.trans h1

/-- Every integer is read back exactly at every deep enough level. -/
theorem readBack_enc_eventually [NeZero n] (F : FractalAbacus n) (v : ℤ) :
    ∃ K, ∀ k ≥ K, (F.uniform k).readBack ((F.uniform k).enc v) = v := by
  refine ⟨2 * v.natAbs + 1, fun k hk => ?_⟩
  have hc := capacity_uniform_ge F k
  have hk2 := Nat.lt_two_pow_self (n := k)
  have hcap : (2 * v.natAbs + 1 : ℤ) ≤ (capacity (F.uniform k).m : ℤ) := by
    exact_mod_cast (hk.trans hk2.le).trans hc
  apply decodeSigned_encode (F.uniform k).rods
  · rcases Int.natAbs_eq v with h | h <;> omega
  · rcases Int.natAbs_eq v with h | h <;> omega

/-- **Arbitrary precision**: for every formula and every input, every deep enough level of the
fractal abacus reads back the exact value. -/
theorem arbitrary_precision [NeZero n] (F : FractalAbacus n) (f : Formula V) (x : V → ℤ) :
    ∃ K, ∀ k ≥ K, (F.uniform k).readBack ((F.uniform k).run (fun v => (F.uniform k).enc (x v)) f)
      = f.eval x := by
  obtain ⟨K, hK⟩ := readBack_enc_eventually F (f.eval x)
  exact ⟨K, fun k hk => by rw [Abacus.run_enc]; exact hK k hk⟩

/-- **Arbitrary precision for programs** (formulas that use earlier results). -/
theorem prog_arbitrary_precision [NeZero n] (F : FractalAbacus n) (P : Abacus.Program) (x : ℕ → ℤ)
    (s : ℕ) :
    ∃ K, ∀ k ≥ K, (F.uniform k).readBack
      (Abacus.runProg (F.uniform k) P (fun t => (F.uniform k).enc (x t)) s) = Abacus.evalProg P x s := by
  obtain ⟨K, hK⟩ := readBack_enc_eventually F (Abacus.evalProg P x s)
  exact ⟨K, fun k hk => by rw [Abacus.runProg_spec]; exact hK k hk⟩

/-- **A whole system at arbitrary precision**: for a finite system of formulas and any inputs,
one depth serves every formula at once, and every deeper level too. -/
theorem system_arbitrary_precision [NeZero n] {W : Type} [Fintype W] (F : FractalAbacus n)
    (S : Abacus.System V W) (x : V → ℤ) :
    ∃ K, ∀ k ≥ K, ∀ w, (F.uniform k).readBack
      ((F.uniform k).runSys (fun v => (F.uniform k).enc (x v)) S w) = (S w).eval x := by
  choose K hK using fun w => readBack_enc_eventually F ((S w).eval x)
  refine ⟨univ.sup K, fun k hk w => ?_⟩
  rw [Abacus.runSys_enc]
  exact hK w k (le_trans (Finset.le_sup (mem_univ w)) hk)

/-- **Every relation is eventually decided rod by rod.** -/
theorem relation_eventually [NeZero n] (F : FractalAbacus n) (f g : Formula V) (x : V → ℤ) :
    ∃ K, ∀ k ≥ K, (f.eval x = g.eval x ↔
      (F.uniform k).run (fun v => (F.uniform k).enc (x v)) f =
        (F.uniform k).run (fun v => (F.uniform k).enc (x v)) g) := by
  refine ⟨(f.eval x - g.eval x).natAbs, fun k hk => ?_⟩
  apply Abacus.relation_iff
  have hc := capacity_uniform_ge F k
  have hk2 := Nat.lt_two_pow_self (n := k)
  have hcap : ((f.eval x - g.eval x).natAbs : ℤ) < (capacity (F.uniform k).m : ℤ) := by
    exact_mod_cast (lt_of_le_of_lt hk hk2).trans_le hc
  rwa [Int.abs_eq_natAbs]

/-! ## Congruences and order on the fractal abacus -/

/-- Deepening never loses a divisor: the capacity at depth `d` divides the capacity at any
deeper depth. -/
theorem capacity_dvd_of_le (F : FractalAbacus n) {d d' : Fin n → ℕ} (hd : ∀ i, d i ≤ d' i) :
    capacity (F.level d).m ∣ capacity (F.level d').m :=
  Finset.prod_dvd_prod_of_dvd _ _ fun i _ => pow_dvd_pow _ (hd i)

/-- **Congruences at a depth.**  If `m` divides the capacity `∏ bᵢ^{dᵢ}` of a level, then for
every integer `x` (of any size) `m ∣ x` is decided rod by rod on that level. -/
theorem congruence_at_level (F : FractalAbacus n) (d : Fin n → ℕ) {m : ℕ}
    (hm : m ∣ capacity (F.level d).m) (x : ℤ) :
    (m : ℤ) ∣ x ↔ ∀ i, m.gcd (F.base i ^ d i) ∣ (F.level d).enc x i :=
  SharedClaims.dvd_iff_rods (F.level d).rods hm x

/-- **Order is decided by one read-back at every deep enough level**: `f ≤ g` exactly when the
signed read-back of the column of `g − f` is non-negative. -/
theorem le_eventually [NeZero n] (F : FractalAbacus n) (f g : Formula V) (x : V → ℤ) :
    ∃ K, ∀ k ≥ K, (f.eval x ≤ g.eval x ↔
      0 ≤ (F.uniform k).readBack ((F.uniform k).run (fun v => (F.uniform k).enc (x v))
        (.sub g f))) := by
  obtain ⟨K, hK⟩ := F.arbitrary_precision (.sub g f) x
  refine ⟨K, fun k hk => ?_⟩
  rw [hK k hk]
  simp only [Formula.eval]
  constructor <;> intro h <;> linarith

/-- **Fractions by cross-multiplication**: an equation `a / b = c / e` between fractions with
non-zero integer denominators is decided rod by rod, at every deep enough level, on the columns
of `a · e` and `c · b`. -/
theorem fraction_eq_eventually [NeZero n] (F : FractalAbacus n) (a b c e : ℤ) (hb : b ≠ 0)
    (he : e ≠ 0) :
    ∃ K, ∀ k ≥ K, ((a : ℚ) / b = c / e ↔ (F.uniform k).enc (a * e) = (F.uniform k).enc (c * b)) := by
  let x : Fin 4 → ℤ := ![a, b, c, e]
  obtain ⟨K, hK⟩ := F.relation_eventually (.mul (.var 0) (.var 3)) (.mul (.var 2) (.var 1)) x
  refine ⟨K, fun k hk => ?_⟩
  have h := hK k hk
  simp only [Abacus.run_enc] at h
  simp only [Formula.eval, x, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h
  rw [← h, div_eq_div_iff (by exact_mod_cast hb) (by exact_mod_cast he)]
  constructor
  · intro h'; exact_mod_cast h'
  · intro h'; exact_mod_cast h'

end FractalAbacus

/-! ## Each level has `b` copies of the level below -/

/-- **The tower of one rod**: exactly `b` residues mod `b^{k+1}` lie over each residue mod
`bᵏ`. -/
theorem card_fibre (b k s : ℕ) (hb : 0 < b) (hs : s < b ^ k) :
    ((range (b ^ (k + 1))).filter (fun r => r % b ^ k = s)).card = b := by
  have hB : 0 < b ^ k := pow_pos hb k
  have hset : (range (b ^ (k + 1))).filter (fun r => r % b ^ k = s) =
      (range b).image (fun j => s + j * b ^ k) := by
    ext r
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hr, hrs⟩
      refine ⟨r / b ^ k, ?_, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul hB]; rw [pow_succ] at hr; linarith
      · have := Nat.mod_add_div r (b ^ k); rw [hrs] at this; linarith
    · rintro ⟨j, hj, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [pow_succ]
        have : j + 1 ≤ b := hj
        nlinarith
      · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  rw [hset, card_image_of_injective _ (fun j j' hjj' => ?_), card_range]
  simp only at hjj'
  exact Nat.eq_of_mul_eq_mul_right hB (by omega)

/-! ## Every polynomial is a formula -/

/-- **Every integer polynomial is a formula of the abacus**, so every polynomial calculation of
the system can be run on the fractal abacus. -/
theorem Formula.exists_of_mvPolynomial (p : MvPolynomial V ℤ) :
    ∃ f : Formula V, ∀ x : V → ℤ, f.eval x = MvPolynomial.eval x p := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨.const a, fun x => by simp [Formula.eval]⟩
  | add p q hp hq =>
    obtain ⟨f, hf⟩ := hp; obtain ⟨g, hg⟩ := hq
    exact ⟨.add f g, fun x => by simp [Formula.eval, hf, hg]⟩
  | mul_X p v hp =>
    obtain ⟨f, hf⟩ := hp
    exact ⟨.mul f (.var v), fun x => by simp [Formula.eval, hf]⟩

end LatticeCalc.Verified.Fractal
