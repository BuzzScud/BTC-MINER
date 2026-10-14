# The fractal abacus: arbitrary precision for the whole system

This note covers the arbitrary-precision **fractal abacus** and how much of the project has been
modelled on it. The general theory is in `LatticeCalc/Verified/FractalAbacus.lean` (part of the
library), and the project's own structures are placed on it in
`RequestProject/FractalAbacusModels.lean`. Both files build with no `sorry` and use only Lean's
standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## 1. What the fractal abacus is

The shared abacus (`docs/topics/rods-and-abacus/ABACUS_SYSTEM.md`) has a fixed set of rods, so it can only hold numbers up to a
fixed size. The fractal abacus fixes only the **bases** `b₀, …, b_{n−1}`: they must be pairwise
coprime and each at least 2. Every rod can then be made as deep as needed: at depth `d` the rod `i`
has modulus `bᵢ^{dᵢ}` (`FractalAbacus.level`). Each rod is a tower

`bᵢ ← bᵢ² ← bᵢ³ ← ⋯`

| Property | Lean theorem |
|---|---|
| Each level holds exactly `b` copies of the level below it (on one rod: exactly `b` residues mod `b^{k+1}` lie over each residue mod `bᵏ`) | `card_fibre` |
| Self-similarity of numbers: reducing a deeper column gives the shallower column | `FractalAbacus.enc_proj` |
| Self-similarity of calculations: a formula run deep and then reduced is the same formula run shallow | `FractalAbacus.run_proj`, `RodFacts.onRod_dvd` |
| The same for whole programs (formulas that use earlier results) | `FractalAbacus.runProg_proj` |
| A solution at some depth is a solution at every shallower depth | `FractalAbacus.solution_proj` |
| Capacity is `∏ bᵢ^{dᵢ}`; deepening rod `i` multiplies it by `bᵢ` | `capacity_level`, `capacity_deepen` |
| At uniform depth `k`, the capacity is at least `2ᵏ`, so capacity has no upper bound | `capacity_uniform_ge` |
| Deepening keeps every divisor of the capacity | `capacity_dvd_of_le` |

**Arbitrary precision.** The following hold for every formula, program or finite system of
formulas, and for every integer input:

* `arbitrary_precision`, `prog_arbitrary_precision`: every deep enough level reads back the exact
  value.
* `system_arbitrary_precision`: a single depth serves every formula of the system at the same time.

## 2. Coverage by kind of statement

The earlier scan (`audit/SHARED_SYSTEM_SUMMARY.md`) sorted the project's 3045 theorem statements
into seven classes, according to the operations they use. For each class, the table below gives:

* the general theorem that puts that kind of statement on the fractal abacus;
* how many statements have been **re-derived from the rods one by one**. These are the `rod_model`
  proofs in `RequestProject/SharedModels/`; the counts come from the checkpoint in
  `audit/SHARED_MODEL_STATUS.md`.

| Class | Statements | General theorem on the fractal abacus | Re-derived from the rods one by one |
|---|---:|---|---:|
| `ring`: only `+ − × ^` and `=` | 481 | `Formula.exists_of_mvPolynomial` (every integer polynomial is an abacus formula), then `relation_eventually` (every `f = g` is decided rod by rod at all deep enough levels) and `arbitrary_precision` | 89 (1 of them partial) |
| `congruence`: remainders and divisibility | 358 | `congruence_at_level`: if the modulus divides `∏ bᵢ^{dᵢ}`, the congruence is decided rod by rod for integers of *any* size. `capacity_dvd_of_le`: deepening keeps that modulus. A modulus with a new prime factor needs a new base, added with `Abacus.merge`. | 24 |
| `counting`: counts over finite sets | 374 | `SharedClaims.card_zeros_eq_prod`: the number of solutions mod the capacity is the product of the per-rod counts; it applies at every level. `card_fibre` gives the growth from one level to the next. | 46 |
| `fraction`: rational numbers | 198 | `fraction_eq_eventually`: equations between fractions, decided by cross-multiplying | 0 |
| `global`: order, gcd, primality, digits, orders of elements | 1075 | `le_eventually`: order needs one read-back, and that read-back is exact at every deep enough level. `SharedClaims.no_column_sign_decider` shows that order cannot be decided without a read-back. | 57 |
| `continuum`: real/complex numbers, limits | 518 | not on the rods (see §4) | 0 |
| `structural`: no arithmetic | 41 | nothing to compute | 1 |
| **total** | **3045** | | **217** |

**How to read this table.**

* The general theorems show that every statement in the first five classes *can* be computed on
  the fractal abacus once its inputs are integers. They do not re-prove the individual statements.
* The last column counts the statements that have actually been re-proved from a rod computation.
  112 of the 217 are `modeled-eval`: some closed inputs, such as the value of a sequence term, were
  first computed from their definitions, and only the claim about those values was decided on the
  rods.
* The remaining 2828 statements are still open in that sense. `audit/SHARED_MODEL_LEDGER.tsv`
  records, for each one, the reason the automatic attempt failed. The most common reasons are:
  * the statement is an equation outside the integers: in `ZMod n`, `ℚ`, `ℝ` or matrices (514);
  * a universally quantified statement is not a congruence (290);
  * an input could not be evaluated, so it was treated as a free variable, which makes the claim
    false as stated (339).

**Repair made this session.** Nine automatic models in `RequestProject/SharedModels/Auto.lean` no
longer built with the current `rod_model` tactic. I removed them, and they are now listed as failed,
with the reason, in `audit/auto_model_attempts.tsv`. The whole project builds again:
`lake build`, 16 281 jobs.

## 3. The project's structures on the fractal abacus (`RequestProject/FractalAbacusModels.lean`)

| Structure | On the fractal abacus | Lean |
|---|---|---|
| 360-dial, 144000, base-60 zoom | One abacus with bases `2, 3, 5`:<br>• 360 is the level `(3,2,1)`, with rods `8, 9, 5`;<br>• 144000 is the level `(7,2,3)`, with rods `128, 9, 125`;<br>• `360·60ᵏ` is the level `(3+2k, 2+k, 1+k)`.<br>So the base-60 zoom is exactly a deepening. | `dial360_moduli`, `dial360_capacity`, `dial144000_moduli`, `dial144000_capacity`, `dial_zoom` |
| 360 inside 144000 | Every calculation on the 144000-dial, reduced, is the same calculation on the 360-dial | `dial_144000_to_360` |
| Core primes 11, 19, 71, 97, 109 | A fractal abacus with these five bases; at depth 1 its capacity is their product | `coreAbacus`, `core_capacity_one` |
| Flower tower `p, p², p³, …` | The flower circle `x² + xy + y² = 1` mod `q` is exactly the set of columns where the flower formula reads 1. Flower points project down the tower. The number of lifts is `FlowerFractal.card_fiber`. | `flower_on_rod`, `flower_proj` |
| Soddy sphere counts | An abacus program run for `N` generations reads back `u_N` exactly at every deep enough level, on any fractal abacus. Five times that value is the number of new spheres in generation `N + 1`. | `soddyProg`, `soddyProg_spec`, `soddy_on_fractal` |
| Descartes relation | Whether four integer curvatures satisfy it is decided rod by rod at every deep enough level | `descartesF`, `descartes_on_fractal` |
| E₈ / Leech inner products | The dot product of two `d`-vectors as a formula; `x · y = c` is decided rod by rod at every deep enough level | `dotF`, `dotF_eval`, `dot_on_fractal` |

## 4. What cannot be modelled exactly, and why

* **Real and complex numbers** (π, √3, cosines, limits, geometry in ℝⁿ): 518 statements.
  * A rod holds a remainder, so it can hold only integers, or fractions whose denominators are
    invertible on the rods. An irrational number has no exact column.
  * The workable route is a scaled integer: `⌊x·Bᵏ⌋` together with a proved error bound. That route
    already exists for √3 in `RequestProject/AbacusPrecision.lean` (certified digits, computed on
    the rods). It has not been developed for π or for the trigonometric statements.
* **Reading fractions back.** `fraction_eq_eventually` decides *equations* between fractions.
  Turning a column back into a fraction needs rational reconstruction, and that is not formalized.
* **Order, primality, gcd.** None of these is a rod-by-rod operation.
  `SharedClaims.no_column_sign_decider` and `sign_needs_every_rod` prove this. Each of them needs
  the read-back, which `le_eventually` provides for order.
