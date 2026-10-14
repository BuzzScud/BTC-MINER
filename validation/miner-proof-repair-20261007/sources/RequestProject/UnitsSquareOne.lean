module

public import Mathlib

/-!
# Which dials fold every spoke onto itself by squaring: exactly the divisors of 24

`TowerFold.units_sq_one_only_24` checked, by compiled evaluation and only for `2 ≤ n ≤ 1000`,
that a dial on which every unit squares to 1 has size dividing 24.  Here this is proved for
**every** dial size, in both directions, by the kernel alone.

* `units_sq_eq_one_iff`: every unit of `ZMod n` squares to 1 exactly when `n ∣ 24`.
* `units_sq_one_only_24_all`: the same statement in the natural-number form of the old check,
  for every `n ≥ 2`.

The argument: if 5 does not divide `n`, then 5 is a unit and `25 ≡ 1` forces `n ∣ 24`; if 5
divides `n`, the unit 2 of the 5-dial lifts to a unit of the `n`-dial, and `2² = 4 ≠ 1` on the
5-dial.
-/

@[expose] public section

namespace UnitsSquareOne

/-- **Every spoke of the `n`-dial squares to 1 exactly when `n` divides 24.** -/
theorem units_sq_eq_one_iff (n : ℕ) [NeZero n] : (∀ u : (ZMod n)ˣ, u ^ 2 = 1) ↔ n ∣ 24 := by
  constructor
  · intro h
    by_cases h5 : 5 ∣ n
    · exfalso
      obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (n := 5) h5 (ZMod.unitOfCoprime 2 (by decide))
      have h1 := congrArg (ZMod.unitsMap h5) (h u)
      rw [map_pow, hu, map_one] at h1
      exact absurd h1 (by decide)
    · have hc : Nat.Coprime 5 n := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h5
      have h1 := congrArg (fun v : (ZMod n)ˣ => (v : ZMod n)) (h (ZMod.unitOfCoprime 5 hc))
      simp only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] at h1
      have h2 : ((24 : ℕ) : ZMod n) = 0 := by
        have : ((25 : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by push_cast; rw [← h1]; norm_num
        have h3 : ((24 : ℕ) : ZMod n) + 1 = 0 + 1 := by
          rw [zero_add]; exact_mod_cast this
        exact add_right_cancel h3
      exact (ZMod.natCast_eq_zero_iff 24 n).1 h2
  · intro h u
    obtain ⟨w, rfl⟩ := ZMod.unitsMap_surjective h u
    have hw : w ^ 2 = 1 := by revert w; decide
    rw [← map_pow, hw, map_one]

/-- **The old bounded check, for every dial size**: if every residue coprime to `n` squares to
1 mod `n`, then `n ∣ 24`. -/
theorem units_sq_one_only_24_all (n : ℕ) (hn : 2 ≤ n)
    (h : ∀ u ∈ Finset.range n, Nat.Coprime u n → u ^ 2 % n = 1) : n ∣ 24 := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  refine (units_sq_eq_one_iff n).1 fun w => Units.ext ?_
  have hu := h (w : ZMod n).val (Finset.mem_range.2 (ZMod.val_lt _)) (ZMod.val_coe_unit_coprime w)
  have : ((((w : ZMod n).val ^ 2 % n : ℕ)) : ZMod n) = ((1 : ℕ) : ZMod n) := by rw [hu]
  rw [ZMod.natCast_mod, Nat.cast_pow, ZMod.natCast_zmod_val, Nat.cast_one] at this
  simpa using this

/-- Conversely every divisor of 24 has the property (so the check has no exceptions). -/
theorem units_sq_one_of_dvd_24 (n : ℕ) (hn : 2 ≤ n) (h24 : n ∣ 24) :
    ∀ u ∈ Finset.range n, Nat.Coprime u n → u ^ 2 % n = 1 := by
  haveI : NeZero n := ⟨by omega⟩
  intro u _ hu
  have h := (units_sq_eq_one_iff n).2 h24 (ZMod.unitOfCoprime u hu)
  have h1 := congrArg (fun v : (ZMod n)ˣ => (v : ZMod n)) h
  simp only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] at h1
  have : ((u ^ 2 : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by push_cast; exact h1
  rw [ZMod.natCast_eq_natCast_iff'] at this
  rw [this, Nat.one_mod_eq_one.2 (by omega)]

end UnitsSquareOne
