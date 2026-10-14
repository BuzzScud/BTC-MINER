import Std.Tactic

/- Abstract contracts. Python, SQL, HTTP and native correspondence is tested,
   not established by these lemmas. Traversal bijection is a separate premise. -/
namespace FractalDistribution

def member (lo hi x : Nat) : Prop := lo ≤ x ∧ x < hi

theorem split_cover (lo mid hi x : Nat) (a : lo ≤ mid) (b : mid ≤ hi) :
    member lo hi x ↔ member lo mid x ∨ member mid hi x := by
  unfold member; omega

theorem split_disjoint (lo mid hi x : Nat) :
    ¬ (member lo mid x ∧ member mid hi x) := by
  unfold member; omega

theorem split_cardinality (lo mid hi : Nat) (a : lo ≤ mid) (b : mid ≤ hi) :
    (mid-lo)+(hi-mid) = hi-lo := by omega

theorem progress_cover (lo cursor hi x : Nat) (a : lo ≤ cursor) (b : cursor ≤ hi) :
    member lo hi x ↔ member lo cursor x ∨ member cursor hi x :=
  split_cover lo cursor hi x a b

theorem recovered_suffix_excludes_prefix (lo cursor hi x : Nat) :
    member lo cursor x → ¬ member cursor hi x := by unfold member; omega

theorem mapped_children_disjoint (f : Nat → Nat)
    (injective : ∀ a b, f a = f b → a = b) (lo mid hi a b : Nat)
    (left : member lo mid a) (right : member mid hi b) : f a ≠ f b := by
  intro h
  have eq := injective a b h
  unfold member at left right
  omega

theorem clipping_preserves_valid (x : Nat) (h : x < 4294967296) :
    ¬ (4294967296 ≤ x) := by omega

theorem nonce_domain_partition : 29826*144000+23296 = 4294967296 := by decide
theorem raw_padding_count : 29827*144000-4294967296 = 120704 := by decide
theorem cell_radices : 2^4*5^2 = 400 := by decide
theorem label_radices : 2^3*3^2*5 = 360 := by decide

theorem winner_cannot_be_excluded (hash target : Nat) (winner : hash ≤ target) :
    ¬ (target < hash) := by omega

theorem transfer_fences_epoch (epoch : Nat) : epoch ≠ epoch+1 := by omega

theorem cumulative_ack_monotone (old reported : Nat) : old ≤ max old reported := by omega

theorem slot_address_bounded (slot offset : Nat) (s : slot < 16) (o : offset < 4096) :
    4096*slot+offset < 65536 := by omega

theorem buffer_fits_rod_capacity : 65536 < 128*9*125 := by decide

theorem duplex_directions_distinct (a b : Nat) (different : a ≠ b) :
    (a,b) ≠ (b,a) := by
  intro h
  have eq := congrArg Prod.fst h
  exact different eq

end FractalDistribution
