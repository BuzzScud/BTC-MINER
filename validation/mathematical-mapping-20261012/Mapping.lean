import Std.Tactic

/- Mathematical contracts for the current miner mapping. Source-program
   correspondence is a separate obligation, checked by finite tests here. -/
namespace MinerMapping

def pack (c r : Nat) := 360 * c + r
def shift (a x : Nat) := (a + x) % 144000
def unshift (a x : Nat) := (x + 144000 - a) % 144000

theorem pack_range (c r : Nat) (hc : c < 400) (hr : r < 360) :
    pack c r < 144000 := by unfold pack; omega

theorem pack_inverse (c r : Nat) (hr : r < 360) :
    pack c r / 360 = c ∧ pack c r % 360 = r := by unfold pack; omega

theorem pack_injective (c r d s : Nat) (hr : r < 360) (hs : s < 360)
    (h : pack c r = pack d s) : c = d ∧ r = s := by unfold pack at h; omega

theorem pack_surjective (x : Nat) (hx : x < 144000) :
    x / 360 < 400 ∧ x % 360 < 360 ∧ pack (x / 360) (x % 360) = x := by
  unfold pack; omega

theorem shift_range (a x : Nat) : shift a x < 144000 := by unfold shift; omega

theorem unshift_shift (a x : Nat) (ha : a < 144000) (hx : x < 144000) :
    unshift a (shift a x) = x := by unfold unshift shift; omega

theorem shift_unshift (a x : Nat) (ha : a < 144000) (hx : x < 144000) :
    shift a (unshift a x) = x := by unfold unshift shift; omega

theorem shift_injective (a x y : Nat) (ha : a < 144000)
    (hx : x < 144000) (hy : y < 144000) (h : shift a x = shift a y) : x = y := by
  have h1 := unshift_shift a x ha hx
  have h2 := unshift_shift a y ha hy
  rw [h] at h1
  exact h1.symm.trans h2

theorem offset_injective (C R : Nat → Nat) (a i j k l : Nat)
    (ha : a < 144000) (hi : i < 400) (hj : j < 400) (hk : k < 360) (hl : l < 360)
    (crange : ∀ v, v < 400 → C v < 400) (rrange : ∀ v, v < 360 → R v < 360)
    (cinj : ∀ u v, u < 400 → v < 400 → C u = C v → u = v)
    (rinj : ∀ u v, u < 360 → v < 360 → R u = R v → u = v)
    (h : shift a (pack (C i) (R k)) = shift a (pack (C j) (R l))) :
    i = j ∧ k = l := by
  have hp := shift_injective a _ _ ha (pack_range _ _ (crange i hi) (rrange k hk))
    (pack_range _ _ (crange j hj) (rrange l hl)) h
  have he := pack_injective _ _ _ _ (rrange k hk) (rrange l hl) hp
  exact ⟨cinj i j hi hj he.1, rinj k l hk hl he.2⟩

theorem offset_surjective (C R : Nat → Nat) (a x : Nat)
    (ha : a < 144000) (hx : x < 144000)
    (csur : ∀ c, c < 400 → ∃ i, i < 400 ∧ C i = c)
    (rsur : ∀ r, r < 360 → ∃ k, k < 360 ∧ R k = r) :
    ∃ i, i < 400 ∧ ∃ k, k < 360 ∧ shift a (pack (C i) (R k)) = x := by
  have hu : unshift a x < 144000 := by unfold unshift; omega
  have hp := pack_surjective (unshift a x) hu
  obtain ⟨i, hi, hci⟩ := csur _ hp.1
  obtain ⟨k, hk, hrk⟩ := rsur _ hp.2.1
  refine ⟨i, hi, k, hk, ?_⟩
  rw [hci, hrk, hp.2.2]
  exact shift_unshift a x ha hx

theorem tile_inverse (t0 t : Nat) (h0 : t0 < 29827) (ht : t < 29827) :
    (t0 + (t + 29827 - t0) % 29827) % 29827 = t := by omega

theorem nonce_decomposition (n : Nat) (hn : n < 4294967296) :
    n / 144000 < 29827 ∧ n % 144000 < 144000 ∧
    (n / 144000) * 144000 + n % 144000 = n := by omega

theorem nonce_pair_unique (t u o v : Nat) (ho : o < 144000) (hv : v < 144000)
    (h : t * 144000 + o = u * 144000 + v) : t = u ∧ o = v := by omega

theorem nonce_coverage (offset : Nat → Nat)
    (cover : ∀ o, o < 144000 → ∃ j, j < 144000 ∧ offset j = o)
    (n : Nat) (hn : n < 4294967296) :
    ∃ t, t < 29827 ∧ ∃ j, j < 144000 ∧ t * 144000 + offset j = n := by
  have hd := nonce_decomposition n hn
  obtain ⟨j, hj, he⟩ := cover (n % 144000) hd.2.1
  exact ⟨n / 144000, hd.1, j, hj, he.symm ▸ hd.2.2⟩

theorem last_tile_width : 4294967296 - 29826 * 144000 = 23296 := by decide

theorem partial_tile_filter (o : Nat) :
    29826 * 144000 + o < 4294967296 ↔ o < 23296 := by omega

theorem unwrapped_bound (c a r : Nat) (hc : c < 400) (ha : a < 144000)
    (hr : r < 360) : 360 * c + a + r ≤ 287998 := by omega

theorem deep_projection (u : Nat) : (u % 256) % 128 = u % 128 := by omega

theorem cell_crt (x : Nat) : (225 * (x % 16) + 176 * (x % 25)) % 400 = x % 400 := by
  omega

theorem offset_crt (x : Nat) :
    (122625 * (x % 128) + 64000 * (x % 9) + 101376 * (x % 125)) % 144000 =
    x % 144000 := by omega

theorem bounded_readback_unique (x y lo hi : Int) (M : Nat) (_hm : 0 < M)
    (hx : lo ≤ x ∧ x ≤ hi) (hy : lo ≤ y ∧ y ≤ hi)
    (hw : hi - lo < M) (he : x % (M : Int) = y % (M : Int)) : x = y := by
  by_cases h : x ≤ y
  · have h0 := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp he.symm
    rw [Int.emod_eq_of_lt (by omega) (by omega)] at h0
    omega
  · have h0 := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp he
    rw [Int.emod_eq_of_lt (by omega) (by omega)] at h0
    omega

theorem prefix_necessary (h t : Nat) (ok : h ≤ t) :
    h / 6277101735386680763835789423207666416102355444464034512896 ≤
    t / 6277101735386680763835789423207666416102355444464034512896 := by omega

inductive Expr where
  | lit : Int → Expr
  | var : Nat → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr

def eval (env : Nat → Int) : Expr → Int
  | .lit n => n
  | .var i => env i
  | .add a b => eval env a + eval env b
  | .sub a b => eval env a - eval env b
  | .mul a b => eval env a * eval env b

def rod (env : Nat → Int) (m : Int) : Expr → Int
  | .lit n => n % m
  | .var i => env i % m
  | .add a b => (rod env m a + rod env m b) % m
  | .sub a b => (rod env m a - rod env m b) % m
  | .mul a b => (rod env m a * rod env m b) % m

theorem polynomial_residue (e : Expr) (env : Nat → Int) (m : Int) :
    rod env m e = eval env e % m := by
  induction e with
  | lit n => rfl
  | var i => rfl
  | add a b ha hb =>
    simp only [rod, eval, ha, hb]
    exact (Int.add_emod _ _ _).symm
  | sub a b ha hb =>
    simp only [rod, eval, ha, hb]
    exact (Int.sub_emod _ _ _).symm
  | mul a b ha hb =>
    simp only [rod, eval, ha, hb]
    exact (Int.mul_emod _ _ _).symm

theorem safe_filter (H : Nat → Nat) (T n : Nat) (removed : Nat → Prop)
    (sound : ∀ m, removed m → T < H m) (valid : H n ≤ T) : ¬ removed n := by
  intro hr
  have hf := sound n hr
  omega

theorem zero_observed_scope (valid checked : Nat → Prop)
    (zero : ∀ n, checked n → ¬ valid n) (n : Nat) (hc : checked n) : ¬ valid n :=
  zero n hc

end MinerMapping

#print axioms MinerMapping.pack_range
#print axioms MinerMapping.pack_inverse
#print axioms MinerMapping.pack_injective
#print axioms MinerMapping.pack_surjective
#print axioms MinerMapping.shift_range
#print axioms MinerMapping.unshift_shift
#print axioms MinerMapping.shift_unshift
#print axioms MinerMapping.shift_injective
#print axioms MinerMapping.offset_injective
#print axioms MinerMapping.offset_surjective
#print axioms MinerMapping.tile_inverse
#print axioms MinerMapping.nonce_decomposition
#print axioms MinerMapping.nonce_pair_unique
#print axioms MinerMapping.nonce_coverage
#print axioms MinerMapping.last_tile_width
#print axioms MinerMapping.partial_tile_filter
#print axioms MinerMapping.unwrapped_bound
#print axioms MinerMapping.deep_projection
#print axioms MinerMapping.cell_crt
#print axioms MinerMapping.offset_crt
#print axioms MinerMapping.bounded_readback_unique
#print axioms MinerMapping.prefix_necessary
#print axioms MinerMapping.polynomial_residue
#print axioms MinerMapping.safe_filter
#print axioms MinerMapping.zero_observed_scope
