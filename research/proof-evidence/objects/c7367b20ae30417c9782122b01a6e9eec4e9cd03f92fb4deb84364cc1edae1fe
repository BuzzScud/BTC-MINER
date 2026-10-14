module

public import LatticeCalc.Verified.OrderSplit
public import RequestProject.RodCircles

/-!
# Towers of three coprimes: `a ^ (b ^ c)` on a dial

REPAIR CONTRACT: every historical statement and hypothesis MUST be preserved.
The shared modular-exponentiation helpers SHALL be proved before finite tower checks;
independent runtime outputs MAY corroborate these claims but MUST NOT replace proofs.
See ../../MASTER_PLAN.md and ../../run_retry.py for the source-bound acceptance gate.

A *three-coprime tower* is `a ^ (b ^ c)` with `a, b, c` pairwise coprime (for example three
distinct primes).  On a dial of size `m` its value is governed by a descending chain of exponents:

  `m  →  E  →  F  →  G → …`   where `a^E ≡ 1 (mod m)`, `b^F ≡ 1 (mod E)`, `c^G ≡ 1 (mod F)`.

* `pow_mod_period` — `a^E ≡ 1 (mod m)` makes `e ↦ a^e (mod m)` periodic with period `E`.
* `tower_collapse` — then `a^(b^c) ≡ a^(b^(c mod F)) (mod m)`: the top of the tower matters only
  modulo `F`.
* `tower4_collapse` — one level more: `a^(b^(c^d)) ≡ a^(b^(c^(d mod G))) (mod m)`.
* `dial_tower` — on the `360` dial the chain is `360 → 12 → 2`: for `a` coprime to `360` and `b`
  coprime to `12`, `a^(b^c) ≡ a^(b^(c mod 2))`, so the tower takes only the two values `a` and
  `a^b`.
* `core_tower3`, `core_tower4` — on the dial `M = 11·19·71·97·109` the chain is
  `M → 30240 → 72 → 6 → 2`: a three-level tower depends on its top only modulo `72`, a four-level
  one on its top only modulo `6`.
* `core_tower_sharp` — the period `72` is attained: the values `7^(11^c) mod M`, `c = 0, …, 71`,
  are pairwise distinct.
-/

@[expose] public section

namespace TowerCollapse

/-- `a^E ≡ 1 (mod m)` makes the powers of `a` periodic with period `E`. -/
theorem pow_mod_period {m a E : ℕ} (h : a ^ E ≡ 1 [MOD m]) (e : ℕ) :
    a ^ e ≡ a ^ (e % E) [MOD m] := by
  conv_lhs => rw [← Nat.div_add_mod e E, pow_add, pow_mul]
  calc (a ^ E) ^ (e / E) * a ^ (e % E) ≡ 1 ^ (e / E) * a ^ (e % E) [MOD m] :=
        (h.pow _).mul_right _
    _ = a ^ (e % E) := by simp

/-- **Tower collapse.**  If `a^E ≡ 1 (mod m)` and `b^F ≡ 1 (mod E)`, the tower `a^(b^c)` depends
on `c` only modulo `F`. -/
theorem tower_collapse {m a b E F : ℕ} (hA : a ^ E ≡ 1 [MOD m]) (hB : b ^ F ≡ 1 [MOD E])
    (c : ℕ) : a ^ (b ^ c) ≡ a ^ (b ^ (c % F)) [MOD m] := by
  have h3 : b ^ c % E = b ^ (c % F) % E := pow_mod_period hB c
  calc a ^ (b ^ c) ≡ a ^ (b ^ c % E) [MOD m] := pow_mod_period hA _
    _ = a ^ (b ^ (c % F) % E) := by rw [h3]
    _ ≡ a ^ (b ^ (c % F)) [MOD m] := (pow_mod_period hA _).symm

/-- One more level: `a^(b^(c^d))` depends on `d` only modulo `G` when `c^G ≡ 1 (mod F)`. -/
theorem tower4_collapse {m a b c E F G : ℕ} (hA : a ^ E ≡ 1 [MOD m]) (hB : b ^ F ≡ 1 [MOD E])
    (hC : c ^ G ≡ 1 [MOD F]) (d : ℕ) :
    a ^ (b ^ (c ^ d)) ≡ a ^ (b ^ (c ^ (d % G))) [MOD m] := by
  have h3 : c ^ d % F = c ^ (d % G) % F := pow_mod_period hC d
  calc a ^ (b ^ (c ^ d)) ≡ a ^ (b ^ (c ^ d % F)) [MOD m] := tower_collapse hA hB _
    _ = a ^ (b ^ (c ^ (d % G) % F)) := by rw [h3]
    _ ≡ a ^ (b ^ (c ^ (d % G))) [MOD m] := (tower_collapse hA hB _).symm

/-- A residue check lifts to every number coprime to the modulus. -/
lemma of_residues {m E b : ℕ} (hm : 1 < m) (key : ∀ r < m, Nat.Coprime r m → r ^ E % m = 1)
    (hb : b.Coprime m) : b ^ E ≡ 1 [MOD m] := by
  have hc : Nat.Coprime (b % m) m := by
    rw [Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_comm]; exact hb
  unfold Nat.ModEq
  rw [Nat.pow_mod, key _ (Nat.mod_lt _ (by omega)) hc, Nat.one_mod_eq_one.2 (by omega)]

/-! ## The 360 dial -/

theorem dial_units (a : ℕ) (ha : a.Coprime 360) : a ^ 12 ≡ 1 [MOD 360] :=
  of_residues (by norm_num) (by decide +kernel) ha

theorem twelve_units (b : ℕ) (hb : b.Coprime 12) : b ^ 2 ≡ 1 [MOD 12] :=
  of_residues (by norm_num) (by decide +kernel) hb

/-- **Towers collapse on the 360 dial.**  For `a` coprime to `360` and `b` coprime to `12`,
`a^(b^c) ≡ a^(b^(c mod 2)) (mod 360)`: the tower is `a` for even `c` and `a^b` for odd `c`. -/
theorem dial_tower (a b c : ℕ) (ha : a.Coprime 360) (hb : b.Coprime 12) :
    a ^ (b ^ c) ≡ a ^ (b ^ (c % 2)) [MOD 360] :=
  tower_collapse (dial_units a ha) (twelve_units b hb) c

theorem dial_tower_two_values (a b c : ℕ) (ha : a.Coprime 360) (hb : b.Coprime 12) :
    a ^ (b ^ c) ≡ a [MOD 360] ∨ a ^ (b ^ c) ≡ a ^ b [MOD 360] := by
  have h := dial_tower a b c ha hb
  rcases Nat.mod_two_eq_zero_or_one c with h2 | h2
  · left; simpa [h2] using h
  · right; simpa [h2] using h

/-! ## The core dial `M = 11·19·71·97·109` -/

open RodCircles

lemma fermat_dvd {p a E : ℕ} (hp : p.Prime) (hd : p - 1 ∣ E) (ha : ¬ p ∣ a) :
    a ^ E ≡ 1 [MOD p] := by
  have hcop : a.Coprime p := ((Nat.Prime.coprime_iff_not_dvd hp).2 ha).symm
  have h := Nat.ModEq.pow_totient hcop
  rw [Nat.totient_prime hp] at h
  obtain ⟨t, rfl⟩ := hd
  rw [pow_mul]
  simpa using h.pow t

lemma not_dvd_of_coprime {p a M : ℕ} (hp : p.Prime) (hpM : p ∣ M) (ha : a.Coprime M) :
    ¬ p ∣ a := fun h => hp.one_lt.ne' (Nat.dvd_one.1 (by
    rw [← ha.gcd_eq_one]; exact Nat.dvd_gcd h hpM))

/-- Every unit of the core dial returns after `30240 = lcm(10, 18, 70, 96, 108)` steps. -/
theorem core_units (a : ℕ) (ha : a.Coprime coreModulus) : a ^ 30240 ≡ 1 [MOD coreModulus] := by
  unfold coreModulus at ha ⊢
  have f : ∀ p, p.Prime → p ∣ 11 * 19 * 71 * 97 * 109 → p - 1 ∣ 30240 →
      a ^ 30240 ≡ 1 [MOD p] := fun p hp hpM hd =>
    fermat_dvd hp hd (not_dvd_of_coprime hp hpM ha)
  have h11 := f 11 (by norm_num) (by norm_num) (by norm_num)
  have h19 := f 19 (by norm_num) (by norm_num) (by norm_num)
  have h71 := f 71 (by norm_num) (by norm_num) (by norm_num)
  have h97 := f 97 (by norm_num) (by norm_num) (by norm_num)
  have h109 := f 109 (by norm_num) (by norm_num) (by norm_num)
  have e1 := (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 11 19)).1 ⟨h11, h19⟩
  have e2 := (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime (11 * 19) 71)).1
    ⟨e1, h71⟩
  have e3 := (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime (11 * 19 * 71) 97)).1
    ⟨e2, h97⟩
  exact (Nat.modEq_and_modEq_iff_modEq_mul
    (by norm_num : Nat.Coprime (11 * 19 * 71 * 97) 109)).1 ⟨e3, h109⟩

/-- `λ(30240) = 72`: every number coprime to `30240` returns after `72` steps. -/
theorem units_30240 (b : ℕ) (hb : b.Coprime 30240) : b ^ 72 ≡ 1 [MOD 30240] := by
  have h32 : b ^ 72 ≡ 1 [MOD 32] :=
    of_residues (by norm_num) (by decide +kernel) (hb.coprime_dvd_right (by norm_num))
  have h27 : b ^ 72 ≡ 1 [MOD 27] :=
    of_residues (by norm_num) (by decide +kernel) (hb.coprime_dvd_right (by norm_num))
  have h5 : b ^ 72 ≡ 1 [MOD 5] :=
    of_residues (by norm_num) (by decide +kernel) (hb.coprime_dvd_right (by norm_num))
  have h7 : b ^ 72 ≡ 1 [MOD 7] :=
    of_residues (by norm_num) (by decide +kernel) (hb.coprime_dvd_right (by norm_num))
  have e1 := (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 32 27)).1 ⟨h32, h27⟩
  have e2 := (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime (32 * 27) 5)).1
    ⟨e1, h5⟩
  exact (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime (32 * 27 * 5) 7)).1
    ⟨e2, h7⟩

theorem units_72 (c : ℕ) (hc : c.Coprime 72) : c ^ 6 ≡ 1 [MOD 72] :=
  of_residues (by norm_num) (by decide +kernel) hc

/-- **Three-coprime towers on the core dial.**  For `a` coprime to `M` and `b` coprime to
`30240` (equivalently to `2·3·5·7`), `a^(b^c) mod M` depends on `c` only modulo `72`. -/
theorem core_tower3 (a b c : ℕ) (ha : a.Coprime coreModulus) (hb : b.Coprime 30240) :
    a ^ (b ^ c) ≡ a ^ (b ^ (c % 72)) [MOD coreModulus] :=
  tower_collapse (core_units a ha) (units_30240 b hb) c

/-- Four levels: with `c` coprime to `72` as well, `a^(b^(c^d)) mod M` depends on `d` only modulo
`6`. -/
theorem core_tower4 (a b c d : ℕ) (ha : a.Coprime coreModulus) (hb : b.Coprime 30240)
    (hc : c.Coprime 72) :
    a ^ (b ^ (c ^ d)) ≡ a ^ (b ^ (c ^ (d % 6))) [MOD coreModulus] :=
  tower4_collapse (core_units a ha) (units_30240 b hb) (units_72 c hc) d

open LatticeCalc.Verified.OrderSplit in
/-- **The period 72 is attained.**  The 72 tower values `7^(11^c) mod M` for `c < 72` are pairwise
distinct (kernel-checked, through the collapse `7^(11^c) ≡ 7^(11^c mod 30240)`). -/
theorem core_tower_sharp :
    ((List.range 72).map (fun c => 7 ^ (11 ^ c) % coreModulus)).Nodup := by
  have h : ∀ c, 7 ^ (11 ^ c) % coreModulus = powmodK 7 (11 ^ c % 30240) coreModulus := by
    intro c
    rw [powmodK_eq]
    exact pow_mod_period (core_units 7 (by unfold coreModulus; norm_num)) _
  simp only [h]
  unfold coreModulus
  decide +kernel

end TowerCollapse
