module

public import Mathlib

/-!
# The Eisenstein integers `ℤ[ω]` as a Euclidean domain

The flower lattice (`FlowerOfLife`, `LatticePatterns.rHex`) is the ring `ℤ[ω]`, `ω² = −1 − ω`,
with norm `N(a + bω) = a² − ab + b²`.  Mathlib has the Gaussian integers but not this ring, so it
is built here:

* `EisInt`: pairs `a + bω` with the product `(a + bω)(c + dω) = (ac − bd) + (ad + bc − bd)ω`,
  a commutative ring (`instCommRing`);
* `star`: the mirror `a + bω ↦ a + bω̄ = (a − b) − bω`, with `z · z̄ = N(z)` (`natCast_norm`);
* `norm_mul`: the norm is multiplicative;
* **`instEuclideanDomain`**: division with remainder, rounding `z · w̄ / N(w)` coordinate-wise,
  leaves a remainder of smaller norm (`norm_mod_lt`).  Hence `ℤ[ω]` is a principal ideal domain
  and a unique factorisation domain, and an element whose norm is a prime number is a prime
  element (`prime_of_norm_prime`).
-/

@[expose] public section

/-- Eisenstein integers `re + im · ω`, with `ω² = −1 − ω`. -/
@[ext]
structure EisInt where
  re : ℤ
  im : ℤ
  deriving DecidableEq

namespace EisInt

instance : Zero EisInt := ⟨⟨0, 0⟩⟩
instance : One EisInt := ⟨⟨1, 0⟩⟩
instance : Add EisInt := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Neg EisInt := ⟨fun z => ⟨-z.re, -z.im⟩⟩
instance : Sub EisInt := ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩
instance : Mul EisInt :=
  ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re - z.im * w.im⟩⟩

@[simp] lemma zero_re : (0 : EisInt).re = 0 := rfl
@[simp] lemma zero_im : (0 : EisInt).im = 0 := rfl
@[simp] lemma one_re : (1 : EisInt).re = 1 := rfl
@[simp] lemma one_im : (1 : EisInt).im = 0 := rfl
@[simp] lemma add_re (z w : EisInt) : (z + w).re = z.re + w.re := rfl
@[simp] lemma add_im (z w : EisInt) : (z + w).im = z.im + w.im := rfl
@[simp] lemma neg_re (z : EisInt) : (-z).re = -z.re := rfl
@[simp] lemma neg_im (z : EisInt) : (-z).im = -z.im := rfl
@[simp] lemma sub_re (z w : EisInt) : (z - w).re = z.re - w.re := rfl
@[simp] lemma sub_im (z w : EisInt) : (z - w).im = z.im - w.im := rfl
@[simp] lemma mul_re (z w : EisInt) : (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] lemma mul_im (z w : EisInt) : (z * w).im = z.re * w.im + z.im * w.re - z.im * w.im := rfl

instance : NatCast EisInt := ⟨fun n => ⟨n, 0⟩⟩
instance : IntCast EisInt := ⟨fun n => ⟨n, 0⟩⟩
@[simp] lemma natCast_re (n : ℕ) : (n : EisInt).re = n := rfl
@[simp] lemma natCast_im (n : ℕ) : (n : EisInt).im = 0 := rfl
@[simp] lemma intCast_re (n : ℤ) : (n : EisInt).re = n := rfl
@[simp] lemma intCast_im (n : ℤ) : (n : EisInt).im = 0 := rfl

instance : SMul ℕ EisInt := ⟨fun n z => ⟨n * z.re, n * z.im⟩⟩
instance : SMul ℤ EisInt := ⟨fun n z => ⟨n * z.re, n * z.im⟩⟩
@[simp] lemma nsmul_re (n : ℕ) (z : EisInt) : (n • z).re = n * z.re := rfl
@[simp] lemma nsmul_im (n : ℕ) (z : EisInt) : (n • z).im = n * z.im := rfl
@[simp] lemma zsmul_re (n : ℤ) (z : EisInt) : (n • z).re = n * z.re := rfl
@[simp] lemma zsmul_im (n : ℤ) (z : EisInt) : (n • z).im = n * z.im := rfl

instance instCommRing : CommRing EisInt where
  zero := 0
  one := 1
  add := (· + ·)
  neg := Neg.neg
  sub := Sub.sub
  mul := (· * ·)
  nsmul := (· • ·)
  zsmul := (· • ·)
  npow := @npowRec EisInt ⟨1⟩ ⟨(· * ·)⟩
  natCast := fun n => (n : EisInt)
  intCast := fun n => (n : EisInt)
  add_assoc := by intros; ext <;> simp <;> ring
  zero_add := by intros; ext <;> simp
  add_zero := by intros; ext <;> simp
  add_comm := by intros; ext <;> simp <;> ring
  nsmul_zero := by intros; ext <;> simp
  nsmul_succ := by intros; ext <;> simp <;> ring
  zsmul_zero' := by intros; ext <;> simp
  zsmul_succ' := by intros; ext <;> simp <;> ring
  zsmul_neg' := by intros; ext <;> simp [Int.negSucc_eq] <;> ring
  neg_add_cancel := by intros; ext <;> simp
  sub_eq_add_neg := by intros; ext <;> simp <;> ring
  mul_assoc := by intros; ext <;> simp <;> ring
  one_mul := by intros; ext <;> simp
  mul_one := by intros; ext <;> simp
  left_distrib := by intros; ext <;> simp <;> ring
  right_distrib := by intros; ext <;> simp <;> ring
  zero_mul := by intros; ext <;> simp
  mul_zero := by intros; ext <;> simp
  mul_comm := by intros; ext <;> simp <;> ring
  natCast_zero := by ext <;> simp
  natCast_succ := by intros; ext <;> simp
  intCast_ofNat := by intros; ext <;> simp
  intCast_negSucc := by intros; ext <;> simp [Int.negSucc_eq]
  npow_zero := by intros; rfl
  npow_succ := by intros; rfl

/-- The mirror `a + bω ↦ a + bω̄ = (a − b) − bω`. -/
instance : Star EisInt := ⟨fun z => ⟨z.re - z.im, -z.im⟩⟩
@[simp] lemma star_re (z : EisInt) : (star z).re = z.re - z.im := rfl
@[simp] lemma star_im (z : EisInt) : (star z).im = -z.im := rfl

lemma star_star' (z : EisInt) : star (star z) = z := by ext <;> simp

lemma star_mul' (z w : EisInt) : star (z * w) = star z * star w := by ext <;> simp <;> ring

/-- The norm `N(a + bω) = a² − ab + b²`. -/
def norm (z : EisInt) : ℤ := z.re ^ 2 - z.re * z.im + z.im ^ 2

lemma norm_nonneg (z : EisInt) : 0 ≤ z.norm := by
  unfold norm; nlinarith [sq_nonneg (z.re - z.im), sq_nonneg z.re, sq_nonneg z.im]

lemma norm_mul (z w : EisInt) : (z * w).norm = z.norm * w.norm := by
  simp only [norm, mul_re, mul_im]; ring

lemma norm_star (z : EisInt) : (star z).norm = z.norm := by
  simp only [norm, star_re, star_im]; ring

lemma mul_star (z : EisInt) : z * star z = ⟨z.norm, 0⟩ := by
  ext <;> simp [norm] <;> ring

lemma norm_eq_zero {z : EisInt} : z.norm = 0 ↔ z = 0 := by
  constructor
  · intro h
    unfold norm at h
    have h1 : z.im = 0 := by nlinarith [sq_nonneg (2 * z.re - z.im), sq_nonneg z.im]
    have h2 : z.re = 0 := by rw [h1] at h; nlinarith
    ext <;> simp [h1, h2]
  · rintro rfl; simp [norm]

instance : Nontrivial EisInt := ⟨⟨0, 1, by intro h; have := congrArg EisInt.re h; simp at this⟩⟩

/-! ## Division with remainder -/

/-- Rounded quotient `≈ a / n` for `n > 0`: `⌊(2a + n) / 2n⌋`. -/
def rnd (a n : ℤ) : ℤ := (2 * a + n) / (2 * n)

lemma rnd_spec (a : ℤ) {n : ℤ} (hn : 0 < n) :
    -n ≤ 2 * (a - n * rnd a n) ∧ 2 * (a - n * rnd a n) < n := by
  have h1 := Int.emod_add_mul_ediv (2 * a + n) (2 * n)
  have h2 := Int.emod_nonneg (2 * a + n) (show (2 * n) ≠ 0 by omega)
  have h3 := Int.emod_lt_of_pos (2 * a + n) (show 0 < 2 * n by omega)
  unfold rnd
  constructor <;> nlinarith

/-- The Euclidean quotient: round `x · ȳ / N(y)` coordinate-wise. -/
def quo (x y : EisInt) : EisInt :=
  ⟨rnd (x * star y).re y.norm, rnd (x * star y).im y.norm⟩

/-- The Euclidean remainder. -/
def rem (x y : EisInt) : EisInt := x - y * quo x y

lemma norm_rem_lt (x : EisInt) {y : EisInt} (hy : y ≠ 0) : (rem x y).norm < y.norm := by
  have hn : 0 < y.norm := lt_of_le_of_ne (norm_nonneg y) (fun h => hy (norm_eq_zero.1 h.symm))
  set n := y.norm
  set u := x * star y
  obtain ⟨h1, h2⟩ := rnd_spec u.re hn
  obtain ⟨h3, h4⟩ := rnd_spec u.im hn
  set s : EisInt := ⟨u.re - n * rnd u.re n, u.im - n * rnd u.im n⟩
  have hs : s = star y * rem x y := by
    have e : star y * rem x y = u - (y * star y) * quo x y := by
      simp only [rem, u]; ring
    rw [e, mul_star]
    ext <;> simp [s, quo, u, n]
  have hns : s.norm = n * (rem x y).norm := by
    rw [hs, norm_mul, norm_star]
  have hsb : 4 * s.norm < 4 * n * n := by
    simp only [norm, s]
    nlinarith
  have : n * (rem x y).norm < n * n := by nlinarith
  exact lt_of_mul_lt_mul_left this hn.le

lemma natAbs_norm_rem_lt (x : EisInt) {y : EisInt} (hy : y ≠ 0) :
    (rem x y).norm.natAbs < y.norm.natAbs := by
  have := norm_rem_lt x hy
  have h0 := norm_nonneg (rem x y)
  omega

lemma norm_le_norm_mul_left (x : EisInt) {y : EisInt} (hy : y ≠ 0) :
    x.norm.natAbs ≤ (x * y).norm.natAbs := by
  rw [norm_mul, Int.natAbs_mul]
  have : 1 ≤ y.norm.natAbs := by
    have h := norm_nonneg y
    have h' : y.norm ≠ 0 := fun h0 => hy (norm_eq_zero.1 h0)
    omega
  exact Nat.le_mul_of_pos_right _ this

instance instEuclideanDomain : EuclideanDomain EisInt :=
  { EisInt.instCommRing, EisInt.instNontrivial with
    quotient := quo
    remainder := rem
    quotient_zero := fun a => by ext <;> simp [quo, rnd, norm]
    quotient_mul_add_remainder_eq := fun a b => by simp [rem]
    r := _
    r_wellFounded := (measure (Int.natAbs ∘ norm)).wf
    remainder_lt := fun a _ hb => natAbs_norm_rem_lt a hb
    mul_left_not_lt := fun a _ hb => not_lt_of_ge (norm_le_norm_mul_left a hb) }

/-! ## Units and primes -/

lemma isUnit_of_norm_one {z : EisInt} (h : z.norm = 1) : IsUnit z :=
  IsUnit.of_mul_eq_one (b := star z) (by rw [mul_star, h]; ext <;> rfl)

lemma norm_one_of_isUnit {z : EisInt} (h : IsUnit z) : z.norm = 1 := by
  obtain ⟨w, hw⟩ := h.exists_right_inv
  have := congrArg norm hw
  rw [norm_mul] at this
  have h1 : norm 1 = 1 := by simp [norm]
  rw [h1] at this
  have := Int.eq_one_or_neg_one_of_mul_eq_one this
  rcases this with h | h
  · exact h
  · have := norm_nonneg z; omega

lemma isUnit_iff_norm_one {z : EisInt} : IsUnit z ↔ z.norm = 1 :=
  ⟨norm_one_of_isUnit, isUnit_of_norm_one⟩

/-- An element whose norm is a prime number is a prime element. -/
theorem prime_of_norm_prime {π : EisInt} {p : ℕ} (hp : p.Prime) (hπ : π.norm = p) : Prime π := by
  apply Irreducible.prime
  refine ⟨?_, ?_⟩
  · rw [isUnit_iff_norm_one, hπ]; exact_mod_cast hp.one_lt.ne'
  · intro x y hxy
    have hn := congrArg norm hxy
    rw [norm_mul, hπ] at hn
    have hx0 := norm_nonneg x
    have hy0 := norm_nonneg y
    have hn' : x.norm.natAbs * y.norm.natAbs = p := by
      have := congrArg Int.natAbs hn
      rw [Int.natAbs_mul] at this; simpa using this.symm
    rw [isUnit_iff_norm_one, isUnit_iff_norm_one]
    rcases (Nat.prime_mul_iff.1 (hn' ▸ hp)) with ⟨_, h1⟩ | ⟨_, h1⟩
    · right; omega
    · left; omega

end EisInt
