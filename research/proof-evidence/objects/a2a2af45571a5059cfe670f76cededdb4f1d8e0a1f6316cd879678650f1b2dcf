module

public import Mathlib

/-!
# The rod abacus (residue number system)

This is the "kissing abacus" of the documents, made into a calculator.  A number is copied onto
several rods; rod `m` stores the remainder mod `m`.  Addition and multiplication are done on each
rod separately, with no carries between rods.  When the rods are pairwise coprime the readings
determine the number modulo the product of the rods (Chinese remainder theorem), so the answer
can be read back.

Everything here is computable: `#eval` runs the calculator, and the theorems say that the
calculator is exact.
-/

@[expose] public section

namespace LatticeCalc

/-- A rod abacus is a list of rod sizes (moduli). -/
structure Abacus where
  rods : List ℕ
deriving Repr, DecidableEq

namespace Abacus

variable (A : Abacus)

/-- The capacity of the abacus: the product of its rod sizes. -/
def capacity : ℕ := A.rods.prod

/-- Copy a number onto every rod. -/
def encode (n : ℕ) : List ℕ := A.rods.map (n % ·)

/-- Rod-by-rod addition, with no carries between rods. -/
def add (x y : List ℕ) : List ℕ := List.zipWith3 (fun m a b => (a + b) % m) A.rods x y

/-- Rod-by-rod multiplication, with no carries between rods. -/
def mul (x y : List ℕ) : List ℕ := List.zipWith3 (fun m a b => (a * b) % m) A.rods x y

/-- Read a number back: the least `n` below the capacity with the given readings (`0` if none). -/
def decode (x : List ℕ) : ℕ := ((List.range A.capacity).find? (fun n => A.encode n == x)).getD 0

lemma zipWith3_map_add (l : List ℕ) (a b : ℕ) :
    List.zipWith3 (fun m x y => (x + y) % m) l (l.map (a % ·)) (l.map (b % ·)) =
      l.map ((a + b) % ·) := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    simp only [List.map_cons, List.zipWith3, ih, ← Nat.add_mod]

lemma zipWith3_map_mul (l : List ℕ) (a b : ℕ) :
    List.zipWith3 (fun m x y => (x * y) % m) l (l.map (a % ·)) (l.map (b % ·)) =
      l.map ((a * b) % ·) := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    simp only [List.map_cons, List.zipWith3, ih, ← Nat.mul_mod]

/-- Rod-by-rod addition is exact: it gives the readings of the sum. -/
theorem add_encode (a b : ℕ) : A.add (A.encode a) (A.encode b) = A.encode (a + b) :=
  zipWith3_map_add A.rods a b

/-- Rod-by-rod multiplication is exact: it gives the readings of the product. -/
theorem mul_encode (a b : ℕ) : A.mul (A.encode a) (A.encode b) = A.encode (a * b) :=
  zipWith3_map_mul A.rods a b

/-- Two numbers have the same readings exactly when they agree modulo every rod. -/
theorem encode_eq_iff (a b : ℕ) : A.encode a = A.encode b ↔ ∀ m ∈ A.rods, a % m = b % m := by
  unfold encode
  induction A.rods with
  | nil => simp
  | cons m l ih => simp [ih]

/-- **Chinese remainder theorem for the abacus.**  With pairwise coprime rods, two numbers have
the same readings exactly when they agree modulo the capacity. -/
theorem encode_eq_iff_modEq (h : A.rods.Pairwise Nat.Coprime) (a b : ℕ) :
    A.encode a = A.encode b ↔ a ≡ b [MOD A.capacity] := by
  rw [encode_eq_iff, capacity, Nat.modEq_list_prod_iff h]
  constructor
  · intro H i
    exact H _ (List.get_mem _ _)
  · intro H m hm
    obtain ⟨i, rfl⟩ := List.get_of_mem hm
    exact H i

/-- **The abacus reads back exactly.**  With pairwise coprime rods of positive size, decoding the
readings of `n` returns `n mod capacity`. -/
theorem decode_encode (h : A.rods.Pairwise Nat.Coprime) (hpos : 0 < A.capacity) (n : ℕ) :
    A.decode (A.encode n) = n % A.capacity := by
  unfold decode
  set N := A.capacity
  have key : ∀ k < N, (A.encode k == A.encode n) = true ↔ k = n % N := by
    intro k hk
    rw [beq_iff_eq, encode_eq_iff_modEq A h]
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt hk]
  have hsome : (List.range N).find? (fun k => A.encode k == A.encode n) = some (n % N) := by
    rw [List.find?_range_eq_some]
    refine ⟨(key _ (Nat.mod_lt _ hpos)).2 rfl, List.mem_range.2 (Nat.mod_lt _ hpos), ?_⟩
    intro j hj
    have hc : ¬ (A.encode j == A.encode n) = true := fun hc =>
      absurd ((key j (lt_trans hj (Nat.mod_lt _ hpos))).1 hc) (by omega)
    simpa using hc
  rw [hsome]
  rfl

/-- The abacus of the documents: rods 8, 9, 5 with capacity 360. -/
def dial360 : Abacus := ⟨[8, 9, 5]⟩

/-- A larger abacus with rods 7, 8, 9, 5, 11, 13 and capacity 360360. -/
def big : Abacus := ⟨[7, 8, 9, 5, 11, 13]⟩

theorem dial360_capacity : dial360.capacity = 360 := rfl
theorem dial360_coprime : dial360.rods.Pairwise Nat.Coprime := by decide
theorem big_capacity : big.capacity = 360360 := rfl
theorem big_coprime : big.rods.Pairwise Nat.Coprime := by decide

/-- Worked example: 19 · 19 on the 360 abacus.  The rods read `(1, 1, 1)`, i.e. `361 ≡ 1`. -/
theorem nineteen_sq_on_rods : dial360.mul (dial360.encode 19) (dial360.encode 19) = [1, 1, 1] := by
  decide

/-- Rods that are not coprime lose information: on rods `[4, 6]` the numbers 0 and 12 read the
same although the product of the rods is 24. -/
theorem noncoprime_collision : (Abacus.mk [4, 6]).encode 0 = (Abacus.mk [4, 6]).encode 12 ∧
    ¬ (0 ≡ 12 [MOD (Abacus.mk [4, 6]).capacity]) := by
  decide

end Abacus

end LatticeCalc
