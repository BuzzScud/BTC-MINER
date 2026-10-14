import Std.Tactic
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace SHAProduction

def B : Nat := 4294967296
def M : Nat := 30065229824
def mask : Nat := 4294967295

def reconstruct (a b c : Nat) : Nat :=
  (12885164033*a + 21475098624*b + 25770196992*c) % M

theorem crt_readback (x : Nat) :
    reconstruct (x % 65536) (x % 65537) (x % 7) = x % M := by
  unfold reconstruct M
  omega

theorem crt_exact (x : Nat) (hx : x < M) :
    reconstruct (x % 65536) (x % 65537) (x % 7) = x := by
  rw [crt_readback, Nat.mod_eq_of_lt hx]

theorem five_sum_fits (a b c d e : Nat)
    (ha : a < B) (hb : b < B) (hc : c < B) (hd : d < B) (he : e < B) :
    a+b+c+d+e < M := by
  unfold B at *; unfold M; omega

theorem five_sum_carry (a b c d e : Nat)
    (ha : a < B) (hb : b < B) (hc : c < B) (hd : d < B) (he : e < B) :
    (a+b+c+d+e) / B < 5 ∧
    (a+b+c+d+e) % B + B*((a+b+c+d+e)/B) = a+b+c+d+e := by
  unfold B at *; omega

def rawRodSum (a b c d e : Nat) : Nat :=
  reconstruct ((a%65536+b%65536+c%65536+d%65536+e%65536)%65536)
              ((a%65537+b%65537+c%65537+d%65537+e%65537)%65537)
              ((a%7+b%7+c%7+d%7+e%7)%7)

theorem raw_rod_sum_exact (a b c d e : Nat)
    (ha : a < B) (hb : b < B) (hc : c < B) (hd : d < B) (he : e < B) :
    rawRodSum a b c d e = a+b+c+d+e := by
  simpa only [rawRodSum, Nat.add_mod, Nat.mod_mod] using
    crt_exact (a+b+c+d+e) (five_sum_fits a b c d e ha hb hc hd he)

def carryCorrected (raw : Nat) : Nat := raw - raw / B * B

theorem carry_corrected_word (raw : Nat) : carryCorrected raw = raw % B := by
  unfold carryCorrected B; omega

theorem carry_corrected_residue (raw : Nat) (r : Int) :
    (((raw : Int) % r - ((raw / B : Nat) : Int) * ((B : Int) % r)) % r) =
      (((raw % B : Nat) : Int) % r) := by
  have decomposition : raw % B + (raw / B) * B = raw := by unfold B; omega
  have d := congrArg Int.ofNat decomposition
  have h : (raw : Int) - ((raw / B : Nat) : Int) * (B : Int) = ((raw % B : Nat) : Int) := by omega
  calc
    _ = ((raw : Int) - ((raw / B : Nat) : Int) * (B : Int)) % r := by
      simp only [Int.sub_emod, Int.mul_emod, Int.emod_emod]
    _ = _ := congrArg (fun x : Int => x % r) h

def correctedResidue (raw r : Nat) : Nat :=
  Int.toNat (((raw : Int) % r - ((raw / B : Nat) : Int) * ((B : Int) % r)) % r)

theorem corrected_residue_eq (raw r : Nat) : correctedResidue raw r = (raw % B) % r := by
  unfold correctedResidue
  rw [carry_corrected_residue]
  rfl

def secondReadback (raw : Nat) :=
  reconstruct (correctedResidue raw 65536) (correctedResidue raw 65537) (correctedResidue raw 7)

theorem second_readback_eq_word (raw : Nat) : secondReadback raw = raw % B := by
  unfold secondReadback
  rw [corrected_residue_eq, corrected_residue_eq, corrected_residue_eq]
  apply crt_exact
  unfold B M
  omega

theorem replay_add5_eq_word (a b c d e : Nat)
    (ha : a < B) (hb : b < B) (hc : c < B) (hd : d < B) (he : e < B) :
    secondReadback (rawRodSum a b c d e) = (a+b+c+d+e) % B := by
  rw [raw_rod_sum_exact a b c d e ha hb hc hd he, second_readback_eq_word]

-- Concrete product-tree topology and inverses computed by ProductTreeCRT for
-- exactly the three rods used by replay_on_rods (no hypothetical decoder).
def treeCRT (a b c : Int) : Int :=
  let left := a % 65536 + 65536 * (((b % 65537 - a % 65536) * 65536) % 65537)
  left + 4295032832 * (((c % 7 - left) * 6) % 7)

theorem product_tree_readback (x : Int) : treeCRT x x x = x % 30065229824 := by
  unfold treeCRT
  dsimp only
  omega

theorem product_tree_matches_basis (a b c : Nat) :
    treeCRT a b c = (reconstruct a b c : Int) := by
  unfold treeCRT reconstruct M
  dsimp only
  omega

theorem mersenne_power_inverse (n : Nat) (hn : n ≤ 32) :
    (2^n * 2^(32-n)) % mask = 1 := by
  rw [← Nat.pow_add]
  have h : n+(32-n)=32 := by omega
  rw [h]
  decide

theorem untagged_all_ones_loses_word : mask % mask = 0 ∧ mask ≠ 0 := by decide


def rotateSplit (x n : Nat) := x / 2^n + (x % 2^n) * 2^(32-n)
def rotateRod (x n : Nat) :=
  if x = mask then mask else (x * 2^(32-n)) % mask

theorem rotate_2 (x : Nat) (hx : x < B) : rotateSplit x 2 = rotateRod x 2 := by
  unfold rotateSplit rotateRod mask B at *
  change x / 4 + x % 4 * 1073741824 = if x = 4294967295 then 4294967295 else x * 1073741824 % 4294967295
  split <;> omega

theorem rotate_6 (x : Nat) (hx : x < B) : rotateSplit x 6 = rotateRod x 6 := by
  unfold rotateSplit rotateRod mask B at *
  change x / 64 + x % 64 * 67108864 = if x = 4294967295 then 4294967295 else x * 67108864 % 4294967295
  split <;> omega

theorem rotate_7 (x : Nat) (hx : x < B) : rotateSplit x 7 = rotateRod x 7 := by
  unfold rotateSplit rotateRod mask B at *
  change x / 128 + x % 128 * 33554432 = if x = 4294967295 then 4294967295 else x * 33554432 % 4294967295
  split <;> omega

theorem rotate_11 (x : Nat) (hx : x < B) : rotateSplit x 11 = rotateRod x 11 := by
  unfold rotateSplit rotateRod mask B at *
  change x / 2048 + x % 2048 * 2097152 = if x = 4294967295 then 4294967295 else x * 2097152 % 4294967295
  split <;> omega

theorem rotate_13 (x : Nat) (hx : x < B) : rotateSplit x 13 = rotateRod x 13 := by
  unfold rotateSplit rotateRod mask B at *
  change x / 8192 + x % 8192 * 524288 = if x = 4294967295 then 4294967295 else x * 524288 % 4294967295
  split <;> omega

theorem rotate_17 (x : Nat) (hx : x < B) : rotateSplit x 17 = rotateRod x 17 := by
  unfold rotateSplit rotateRod mask B at *
  change x / 131072 + x % 131072 * 32768 = if x = 4294967295 then 4294967295 else x * 32768 % 4294967295
  split <;> omega

theorem rotate_18 (x : Nat) (hx : x < B) : rotateSplit x 18 = rotateRod x 18 := by
  unfold rotateSplit rotateRod mask B at *
  change x / 262144 + x % 262144 * 16384 = if x = 4294967295 then 4294967295 else x * 16384 % 4294967295
  split <;> omega

theorem rotate_19 (x : Nat) (hx : x < B) : rotateSplit x 19 = rotateRod x 19 := by
  unfold rotateSplit rotateRod mask B at *
  change x / 524288 + x % 524288 * 8192 = if x = 4294967295 then 4294967295 else x * 8192 % 4294967295
  split <;> omega

theorem rotate_22 (x : Nat) (hx : x < B) : rotateSplit x 22 = rotateRod x 22 := by
  unfold rotateSplit rotateRod mask B at *
  change x / 4194304 + x % 4194304 * 1024 = if x = 4294967295 then 4294967295 else x * 1024 % 4294967295
  split <;> omega

theorem rotate_25 (x : Nat) (hx : x < B) : rotateSplit x 25 = rotateRod x 25 := by
  unfold rotateSplit rotateRod mask B at *
  change x / 33554432 + x % 33554432 * 128 = if x = 4294967295 then 4294967295 else x * 128 % 4294967295
  split <;> omega



def rodAdd5 (a b c d e : BitVec 32) : BitVec 32 :=
  BitVec.ofNat 32 (secondReadback (rawRodSum a.toNat b.toNat c.toNat d.toNat e.toNat))

theorem rod_add5_eq_word_add (a b c d e : BitVec 32) : rodAdd5 a b c d e = a+b+c+d+e := by
  apply BitVec.eq_of_toNat_eq
  unfold rodAdd5
  rw [replay_add5_eq_word _ _ _ _ _ a.isLt b.isLt c.isLt d.isLt e.isLt]
  simp only [BitVec.toNat_ofNat, BitVec.toNat_add, B, Nat.mod_mod]
  omega

def rodAdd2 (a b : BitVec 32) := rodAdd5 a b 0 0 0

theorem rod_add2_eq_word_add (a b : BitVec 32) : rodAdd2 a b = a+b := by
  simp [rodAdd2, rod_add5_eq_word_add]

def cRotate (x : BitVec 32) (n : Nat) := (x >>> n) ||| (x <<< (32-n))
def rodRotate (x : BitVec 32) (n : Nat) := BitVec.ofNat 32 (rotateRod x.toNat n)

theorem rotate_shift_parts_disjoint (x : BitVec 32) (n : Nat) (hn : n ≤ 32) :
    (x >>> n) &&& (x <<< (32-n)) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and,BitVec.getLsbD_ushiftRight,BitVec.getLsbD_shiftLeft ]
  by_cases h : i < 32-n
  · simp [h]
  · have hge : 32 ≤ n+i := by omega
    rw [BitVec.getLsbD_of_ge x (n+i) hge]
    simp

theorem c_rotate_split_2 (x : BitVec 32) : (cRotate x 2).toNat = rotateSplit x.toNat 2 := by
  have hor : (x >>> 2) ||| (x <<< 30) = (x >>> 2) + (x <<< 30) :=
    (BitVec.add_eq_or_of_and_eq_zero _ _ (rotate_shift_parts_disjoint x 2 (by decide))).symm
  change (((x >>> 2) ||| (x <<< 30))).toNat = _
  rw [hor]
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
             Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hx := x.isLt
  unfold rotateSplit
  omega

theorem rod_rotate_eq_c_2 (x : BitVec 32) : rodRotate x 2 = cRotate x 2 := by
  apply BitVec.eq_of_toNat_eq
  unfold rodRotate
  rw [BitVec.toNat_ofNat, c_rotate_split_2, ← rotate_2 x.toNat x.isLt]
  have hc := (cRotate x 2).isLt
  rw [c_rotate_split_2] at hc
  exact Nat.mod_eq_of_lt hc

theorem c_rotate_split_6 (x : BitVec 32) : (cRotate x 6).toNat = rotateSplit x.toNat 6 := by
  have hor : (x >>> 6) ||| (x <<< 26) = (x >>> 6) + (x <<< 26) :=
    (BitVec.add_eq_or_of_and_eq_zero _ _ (rotate_shift_parts_disjoint x 6 (by decide))).symm
  change (((x >>> 6) ||| (x <<< 26))).toNat = _
  rw [hor]
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
             Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hx := x.isLt
  unfold rotateSplit
  omega

theorem rod_rotate_eq_c_6 (x : BitVec 32) : rodRotate x 6 = cRotate x 6 := by
  apply BitVec.eq_of_toNat_eq
  unfold rodRotate
  rw [BitVec.toNat_ofNat, c_rotate_split_6, ← rotate_6 x.toNat x.isLt]
  have hc := (cRotate x 6).isLt
  rw [c_rotate_split_6] at hc
  exact Nat.mod_eq_of_lt hc

theorem c_rotate_split_7 (x : BitVec 32) : (cRotate x 7).toNat = rotateSplit x.toNat 7 := by
  have hor : (x >>> 7) ||| (x <<< 25) = (x >>> 7) + (x <<< 25) :=
    (BitVec.add_eq_or_of_and_eq_zero _ _ (rotate_shift_parts_disjoint x 7 (by decide))).symm
  change (((x >>> 7) ||| (x <<< 25))).toNat = _
  rw [hor]
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
             Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hx := x.isLt
  unfold rotateSplit
  omega

theorem rod_rotate_eq_c_7 (x : BitVec 32) : rodRotate x 7 = cRotate x 7 := by
  apply BitVec.eq_of_toNat_eq
  unfold rodRotate
  rw [BitVec.toNat_ofNat, c_rotate_split_7, ← rotate_7 x.toNat x.isLt]
  have hc := (cRotate x 7).isLt
  rw [c_rotate_split_7] at hc
  exact Nat.mod_eq_of_lt hc

theorem c_rotate_split_11 (x : BitVec 32) : (cRotate x 11).toNat = rotateSplit x.toNat 11 := by
  have hor : (x >>> 11) ||| (x <<< 21) = (x >>> 11) + (x <<< 21) :=
    (BitVec.add_eq_or_of_and_eq_zero _ _ (rotate_shift_parts_disjoint x 11 (by decide))).symm
  change (((x >>> 11) ||| (x <<< 21))).toNat = _
  rw [hor]
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
             Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hx := x.isLt
  unfold rotateSplit
  omega

theorem rod_rotate_eq_c_11 (x : BitVec 32) : rodRotate x 11 = cRotate x 11 := by
  apply BitVec.eq_of_toNat_eq
  unfold rodRotate
  rw [BitVec.toNat_ofNat, c_rotate_split_11, ← rotate_11 x.toNat x.isLt]
  have hc := (cRotate x 11).isLt
  rw [c_rotate_split_11] at hc
  exact Nat.mod_eq_of_lt hc

theorem c_rotate_split_13 (x : BitVec 32) : (cRotate x 13).toNat = rotateSplit x.toNat 13 := by
  have hor : (x >>> 13) ||| (x <<< 19) = (x >>> 13) + (x <<< 19) :=
    (BitVec.add_eq_or_of_and_eq_zero _ _ (rotate_shift_parts_disjoint x 13 (by decide))).symm
  change (((x >>> 13) ||| (x <<< 19))).toNat = _
  rw [hor]
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
             Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hx := x.isLt
  unfold rotateSplit
  omega

theorem rod_rotate_eq_c_13 (x : BitVec 32) : rodRotate x 13 = cRotate x 13 := by
  apply BitVec.eq_of_toNat_eq
  unfold rodRotate
  rw [BitVec.toNat_ofNat, c_rotate_split_13, ← rotate_13 x.toNat x.isLt]
  have hc := (cRotate x 13).isLt
  rw [c_rotate_split_13] at hc
  exact Nat.mod_eq_of_lt hc

theorem c_rotate_split_17 (x : BitVec 32) : (cRotate x 17).toNat = rotateSplit x.toNat 17 := by
  have hor : (x >>> 17) ||| (x <<< 15) = (x >>> 17) + (x <<< 15) :=
    (BitVec.add_eq_or_of_and_eq_zero _ _ (rotate_shift_parts_disjoint x 17 (by decide))).symm
  change (((x >>> 17) ||| (x <<< 15))).toNat = _
  rw [hor]
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
             Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hx := x.isLt
  unfold rotateSplit
  omega

theorem rod_rotate_eq_c_17 (x : BitVec 32) : rodRotate x 17 = cRotate x 17 := by
  apply BitVec.eq_of_toNat_eq
  unfold rodRotate
  rw [BitVec.toNat_ofNat, c_rotate_split_17, ← rotate_17 x.toNat x.isLt]
  have hc := (cRotate x 17).isLt
  rw [c_rotate_split_17] at hc
  exact Nat.mod_eq_of_lt hc

theorem c_rotate_split_18 (x : BitVec 32) : (cRotate x 18).toNat = rotateSplit x.toNat 18 := by
  have hor : (x >>> 18) ||| (x <<< 14) = (x >>> 18) + (x <<< 14) :=
    (BitVec.add_eq_or_of_and_eq_zero _ _ (rotate_shift_parts_disjoint x 18 (by decide))).symm
  change (((x >>> 18) ||| (x <<< 14))).toNat = _
  rw [hor]
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
             Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hx := x.isLt
  unfold rotateSplit
  omega

theorem rod_rotate_eq_c_18 (x : BitVec 32) : rodRotate x 18 = cRotate x 18 := by
  apply BitVec.eq_of_toNat_eq
  unfold rodRotate
  rw [BitVec.toNat_ofNat, c_rotate_split_18, ← rotate_18 x.toNat x.isLt]
  have hc := (cRotate x 18).isLt
  rw [c_rotate_split_18] at hc
  exact Nat.mod_eq_of_lt hc

theorem c_rotate_split_19 (x : BitVec 32) : (cRotate x 19).toNat = rotateSplit x.toNat 19 := by
  have hor : (x >>> 19) ||| (x <<< 13) = (x >>> 19) + (x <<< 13) :=
    (BitVec.add_eq_or_of_and_eq_zero _ _ (rotate_shift_parts_disjoint x 19 (by decide))).symm
  change (((x >>> 19) ||| (x <<< 13))).toNat = _
  rw [hor]
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
             Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hx := x.isLt
  unfold rotateSplit
  omega

theorem rod_rotate_eq_c_19 (x : BitVec 32) : rodRotate x 19 = cRotate x 19 := by
  apply BitVec.eq_of_toNat_eq
  unfold rodRotate
  rw [BitVec.toNat_ofNat, c_rotate_split_19, ← rotate_19 x.toNat x.isLt]
  have hc := (cRotate x 19).isLt
  rw [c_rotate_split_19] at hc
  exact Nat.mod_eq_of_lt hc

theorem c_rotate_split_22 (x : BitVec 32) : (cRotate x 22).toNat = rotateSplit x.toNat 22 := by
  have hor : (x >>> 22) ||| (x <<< 10) = (x >>> 22) + (x <<< 10) :=
    (BitVec.add_eq_or_of_and_eq_zero _ _ (rotate_shift_parts_disjoint x 22 (by decide))).symm
  change (((x >>> 22) ||| (x <<< 10))).toNat = _
  rw [hor]
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
             Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hx := x.isLt
  unfold rotateSplit
  omega

theorem rod_rotate_eq_c_22 (x : BitVec 32) : rodRotate x 22 = cRotate x 22 := by
  apply BitVec.eq_of_toNat_eq
  unfold rodRotate
  rw [BitVec.toNat_ofNat, c_rotate_split_22, ← rotate_22 x.toNat x.isLt]
  have hc := (cRotate x 22).isLt
  rw [c_rotate_split_22] at hc
  exact Nat.mod_eq_of_lt hc

theorem c_rotate_split_25 (x : BitVec 32) : (cRotate x 25).toNat = rotateSplit x.toNat 25 := by
  have hor : (x >>> 25) ||| (x <<< 7) = (x >>> 25) + (x <<< 7) :=
    (BitVec.add_eq_or_of_and_eq_zero _ _ (rotate_shift_parts_disjoint x 25 (by decide))).symm
  change (((x >>> 25) ||| (x <<< 7))).toNat = _
  rw [hor]
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
             Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hx := x.isLt
  unfold rotateSplit
  omega

theorem rod_rotate_eq_c_25 (x : BitVec 32) : rodRotate x 25 = cRotate x 25 := by
  apply BitVec.eq_of_toNat_eq
  unfold rodRotate
  rw [BitVec.toNat_ofNat, c_rotate_split_25, ← rotate_25 x.toNat x.isLt]
  have hc := (cRotate x 25).isLt
  rw [c_rotate_split_25] at hc
  exact Nat.mod_eq_of_lt hc


abbrev Word := BitVec 32

def cs0 (x : Word) := cRotate x 7 ^^^ cRotate x 18 ^^^ (x >>> 3)
def cs1 (x : Word) := cRotate x 17 ^^^ cRotate x 19 ^^^ (x >>> 10)
def cS0 (x : Word) := cRotate x 2 ^^^ cRotate x 13 ^^^ cRotate x 22
def cS1 (x : Word) := cRotate x 6 ^^^ cRotate x 11 ^^^ cRotate x 25
def rs0 (x : Word) := rodRotate x 7 ^^^ rodRotate x 18 ^^^ (x >>> 3)
def rs1 (x : Word) := rodRotate x 17 ^^^ rodRotate x 19 ^^^ (x >>> 10)
def rS0 (x : Word) := rodRotate x 2 ^^^ rodRotate x 13 ^^^ rodRotate x 22
def rS1 (x : Word) := rodRotate x 6 ^^^ rodRotate x 11 ^^^ rodRotate x 25

theorem small_sigma0_eq (x : Word) : rs0 x = cs0 x := by
  simp [rs0,cs0,rod_rotate_eq_c_7,rod_rotate_eq_c_18]
theorem small_sigma1_eq (x : Word) : rs1 x = cs1 x := by
  simp [rs1,cs1,rod_rotate_eq_c_17,rod_rotate_eq_c_19]
theorem big_sigma0_eq (x : Word) : rS0 x = cS0 x := by
  simp [rS0,cS0,rod_rotate_eq_c_2,rod_rotate_eq_c_13,rod_rotate_eq_c_22]
theorem big_sigma1_eq (x : Word) : rS1 x = cS1 x := by
  simp [rS1,cS1,rod_rotate_eq_c_6,rod_rotate_eq_c_11,rod_rotate_eq_c_25]

def choice (x y z : Word) := (x &&& y) ^^^ (~~~x &&& z)
def majority (x y z : Word) := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

theorem xor_bit_arithmetic (x y : Word) (i : Nat) :
    ((x ^^^ y).getLsbD i).toNat = ((x.getLsbD i).toNat + (y.getLsbD i).toNat) % 2 := by
  rw [BitVec.getLsbD_xor]
  cases x.getLsbD i <;> cases y.getLsbD i <;> decide

theorem and_bit_arithmetic (x y : Word) (i : Nat) :
    ((x &&& y).getLsbD i).toNat = (x.getLsbD i).toNat * (y.getLsbD i).toNat := by
  rw [BitVec.getLsbD_and]
  cases x.getLsbD i <;> cases y.getLsbD i <;> decide

theorem not_word_subtraction (x : Word) : (BitVec.allOnes 32)-x = ~~~x :=
  BitVec.allOnes_sub_eq_not x

theorem choice_has_disjoint_terms (x y z : Word) : choice x y z = (x &&& y) ||| (~~~x &&& z) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [choice,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not]
  simp only [hi,decide_true,Bool.true_and]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> decide

theorem majority_is_bit_majority (x y z : Word) : majority x y z =
    (x &&& y) ||| (x &&& z) ||| (y &&& z) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [majority,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_or]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> decide

def scheduleC (a b c d : Word) := a + cs0 b + c + cs1 d
def scheduleR (a b c d : Word) := rodAdd5 a (rs0 b) c (rs1 d) 0

theorem schedule_step_equiv (a b c d : Word) : scheduleR a b c d = scheduleC a b c d := by
  simp [scheduleR,scheduleC,rod_add5_eq_word_add,small_sigma0_eq,small_sigma1_eq]

structure State where
  a : Word
  b : Word
  c : Word
  d : Word
  e : Word
  f : Word
  g : Word
  h : Word
  deriving DecidableEq

def roundC (s : State) (k w : Word) : State :=
  let t1 := s.h + cS1 s.e + choice s.e s.f s.g + k + w
  let t2 := cS0 s.a + majority s.a s.b s.c
  ⟨t1+t2,s.a,s.b,s.c,s.d+t1,s.e,s.f,s.g⟩

def roundR (s : State) (k w : Word) : State :=
  let t1 := rodAdd5 s.h (rS1 s.e) (choice s.e s.f s.g) k w
  let t2 := rodAdd2 (rS0 s.a) (majority s.a s.b s.c)
  ⟨rodAdd2 t1 t2,s.a,s.b,s.c,rodAdd2 s.d t1,s.e,s.f,s.g⟩

theorem round_equiv (s : State) (k w : Word) : roundR s k w = roundC s k w := by
  simp [roundR,roundC,rod_add5_eq_word_add,rod_add2_eq_word_add,big_sigma0_eq,big_sigma1_eq]

attribute [irreducible] roundR roundC

-- Same concrete indexing as the expansion loop: t-16,t-15,t-7,t-2.
def expandC : Nat → List Word → List Word
  | 0, words => words
  | n+1, words =>
    let t := words.length
    expandC n (words ++ [scheduleC (words[t-16]?.getD 0) (words[t-15]?.getD 0)
                                    (words[t-7]?.getD 0) (words[t-2]?.getD 0)])
def expandR : Nat → List Word → List Word
  | 0, words => words
  | n+1, words =>
    let t := words.length
    expandR n (words ++ [scheduleR (words[t-16]?.getD 0) (words[t-15]?.getD 0)
                                    (words[t-7]?.getD 0) (words[t-2]?.getD 0)])

theorem schedule_induction (n : Nat) (words : List Word) : expandR n words = expandC n words := by
  induction n generalizing words with
  | zero => rfl
  | succ n ih => simp only [expandR,expandC,schedule_step_equiv,ih]

theorem expansion_length (n : Nat) (words : List Word) : (expandC n words).length = words.length+n := by
  induction n generalizing words with
  | zero => simp [expandC]
  | succ n ih => simp only [expandC,ih,List.length_append,List.length_cons,List.length_nil]; omega

theorem schedule64 (words : List Word) (h : words.length=16) :
    expandR 48 words = expandC 48 words ∧ (expandR 48 words).length=64 := by
  rw [schedule_induction]
  exact ⟨rfl,by rw [expansion_length,h]⟩

theorem fold_induction {S I : Type} (f g : S → I → S)
    (step : ∀ s i, f s i = g s i) (input : List I) (s : S) :
    input.foldl f s = input.foldl g s := by
  induction input generalizing s with
  | nil => rfl
  | cons item xs ih =>
    change xs.foldl f (f s item) = xs.foldl g (g s item)
    rw [step]
    exact ih _

def roundsC (input : List (Word × Word)) (s : State) :=
  input.foldl (fun state item => roundC state item.1 item.2) s
def roundsR (input : List (Word × Word)) (s : State) :=
  input.foldl (fun state item => roundR state item.1 item.2) s

theorem round_induction (input : List (Word × Word)) (s : State) : roundsR input s = roundsC input s := by
  exact @fold_induction State (Word × Word)
    (fun state item => roundR state item.1 item.2)
    (fun state item => roundC state item.1 item.2)
    (fun state item => round_equiv state item.1 item.2) input s

def feedC (a b : State) : State :=
  ⟨a.a+b.a,a.b+b.b,a.c+b.c,a.d+b.d,a.e+b.e,a.f+b.f,a.g+b.g,a.h+b.h⟩
def feedR (a b : State) : State :=
  ⟨rodAdd2 a.a b.a,rodAdd2 a.b b.b,rodAdd2 a.c b.c,rodAdd2 a.d b.d,
   rodAdd2 a.e b.e,rodAdd2 a.f b.f,rodAdd2 a.g b.g,rodAdd2 a.h b.h⟩

theorem feedforward_equiv (a b : State) : feedR a b = feedC a b := by
  simp [feedR,feedC,rod_add2_eq_word_add]

def compressionC (words constants : List Word) (initial : State) :=
  feedC initial (roundsC (constants.zip (expandC 48 words)) initial)
def compressionR (words constants : List Word) (initial : State) :=
  feedR initial (roundsR (constants.zip (expandR 48 words)) initial)

theorem compression_equiv (words constants : List Word) (initial : State) :
    compressionR words constants initial = compressionC words constants initial := by
  simp only [compressionR,compressionC,feedforward_equiv,round_induction,schedule_induction]

-- Sequential three-block composition is proved from the concrete compression
-- models. It does not assume entire C/Python equivalence as a premise.
def blocksC (blocks : List (List Word)) (constants : List Word) (initial : State) :=
  blocks.foldl (fun state block => compressionC block constants state) initial
def blocksR (blocks : List (List Word)) (constants : List Word) (initial : State) :=
  blocks.foldl (fun state block => compressionR block constants state) initial

theorem blocks_equiv (blocks : List (List Word)) (constants : List Word) (initial : State) :
    blocksR blocks constants initial = blocksC blocks constants initial := by
  simp [blocksR,blocksC,compression_equiv]


def stateWords (s : State) : List Word := [s.a,s.b,s.c,s.d,s.e,s.f,s.g,s.h]
def tailWords (header : List Word) : List Word :=
  header.drop 16 ++ [0x80000000] ++ List.replicate 10 0 ++ [640]
def outerWords (s : State) : List Word :=
  stateWords s ++ [0x80000000] ++ List.replicate 6 0 ++ [256]

theorem padded_tail_length (header : List Word) (h : header.length=20) : (tailWords header).length=16 := by
  simp [tailWords,h]
theorem padded_outer_length (s : State) : (outerWords s).length=16 := by
  simp [outerWords,stateWords]

def doubleC (header constants : List Word) (iv : State) :=
  let mid := compressionC (header.take 16) constants iv
  let inner := compressionC (tailWords header) constants mid
  compressionC (outerWords inner) constants iv

def doubleR (header constants : List Word) (iv : State) :=
  let mid := compressionR (header.take 16) constants iv
  let inner := compressionR (tailWords header) constants mid
  compressionR (outerWords inner) constants iv

theorem three_block_double_sha_equiv (header constants : List Word) (iv : State) :
    doubleR header constants iv = doubleC header constants iv := by
  simp only [doubleR,doubleC,compression_equiv]


-- Constants transcribed automatically from the source-bound C arrays.
def sourceK : List Word := [0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2]
def sourceIV : State := ⟨0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19⟩

theorem source_constants_length : sourceK.length=64 := by decide

theorem sixty_four_rounds (words : List Word) (h : words.length=16) :
    (sourceK.zip (expandC 48 words)).length=64 := by
  simp [List.length_zip,expansion_length,h,source_constants_length]

theorem source_header_blocks (header : List Word) (h : header.length=20) :
    (header.take 16).length=16 ∧ (tailWords header).length=16 := by
  exact ⟨by simp [h],padded_tail_length header h⟩

theorem production_constants_double_sha (header : List Word) :
    doubleR header sourceK sourceIV = doubleC header sourceK sourceIV :=
  three_block_double_sha_equiv header sourceK sourceIV



theorem logical_shift3 (x : Word) : (x >>> 3).toNat = x.toNat / 8 := by
  simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
theorem logical_shift10 (x : Word) : (x >>> 10).toNat = x.toNat / 1024 := by
  simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
theorem complement_integer (x : Word) : (~~~x).toNat = mask - x.toNat := by
  simp only [BitVec.toNat_not,mask]

end SHAProduction

#print axioms SHAProduction.crt_readback
#print axioms SHAProduction.crt_exact
#print axioms SHAProduction.five_sum_fits
#print axioms SHAProduction.five_sum_carry
#print axioms SHAProduction.raw_rod_sum_exact
#print axioms SHAProduction.carry_corrected_word
#print axioms SHAProduction.carry_corrected_residue
#print axioms SHAProduction.corrected_residue_eq
#print axioms SHAProduction.second_readback_eq_word
#print axioms SHAProduction.replay_add5_eq_word
#print axioms SHAProduction.product_tree_readback
#print axioms SHAProduction.product_tree_matches_basis
#print axioms SHAProduction.mersenne_power_inverse
#print axioms SHAProduction.untagged_all_ones_loses_word
#print axioms SHAProduction.rotate_2
#print axioms SHAProduction.rotate_6
#print axioms SHAProduction.rotate_7
#print axioms SHAProduction.rotate_11
#print axioms SHAProduction.rotate_13
#print axioms SHAProduction.rotate_17
#print axioms SHAProduction.rotate_18
#print axioms SHAProduction.rotate_19
#print axioms SHAProduction.rotate_22
#print axioms SHAProduction.rotate_25
#print axioms SHAProduction.rod_add5_eq_word_add
#print axioms SHAProduction.rod_add2_eq_word_add
#print axioms SHAProduction.rotate_shift_parts_disjoint
#print axioms SHAProduction.c_rotate_split_2
#print axioms SHAProduction.rod_rotate_eq_c_2
#print axioms SHAProduction.c_rotate_split_6
#print axioms SHAProduction.rod_rotate_eq_c_6
#print axioms SHAProduction.c_rotate_split_7
#print axioms SHAProduction.rod_rotate_eq_c_7
#print axioms SHAProduction.c_rotate_split_11
#print axioms SHAProduction.rod_rotate_eq_c_11
#print axioms SHAProduction.c_rotate_split_13
#print axioms SHAProduction.rod_rotate_eq_c_13
#print axioms SHAProduction.c_rotate_split_17
#print axioms SHAProduction.rod_rotate_eq_c_17
#print axioms SHAProduction.c_rotate_split_18
#print axioms SHAProduction.rod_rotate_eq_c_18
#print axioms SHAProduction.c_rotate_split_19
#print axioms SHAProduction.rod_rotate_eq_c_19
#print axioms SHAProduction.c_rotate_split_22
#print axioms SHAProduction.rod_rotate_eq_c_22
#print axioms SHAProduction.c_rotate_split_25
#print axioms SHAProduction.rod_rotate_eq_c_25
#print axioms SHAProduction.small_sigma0_eq
#print axioms SHAProduction.small_sigma1_eq
#print axioms SHAProduction.big_sigma0_eq
#print axioms SHAProduction.big_sigma1_eq
#print axioms SHAProduction.xor_bit_arithmetic
#print axioms SHAProduction.and_bit_arithmetic
#print axioms SHAProduction.not_word_subtraction
#print axioms SHAProduction.choice_has_disjoint_terms
#print axioms SHAProduction.majority_is_bit_majority
#print axioms SHAProduction.schedule_step_equiv
#print axioms SHAProduction.round_equiv
#print axioms SHAProduction.schedule_induction
#print axioms SHAProduction.expansion_length
#print axioms SHAProduction.schedule64
#print axioms SHAProduction.fold_induction
#print axioms SHAProduction.round_induction
#print axioms SHAProduction.feedforward_equiv
#print axioms SHAProduction.compression_equiv
#print axioms SHAProduction.blocks_equiv
#print axioms SHAProduction.padded_tail_length
#print axioms SHAProduction.padded_outer_length
#print axioms SHAProduction.three_block_double_sha_equiv
#print axioms SHAProduction.source_constants_length
#print axioms SHAProduction.sixty_four_rounds
#print axioms SHAProduction.source_header_blocks
#print axioms SHAProduction.production_constants_double_sha
#print axioms SHAProduction.logical_shift3
#print axioms SHAProduction.logical_shift10
#print axioms SHAProduction.complement_integer
