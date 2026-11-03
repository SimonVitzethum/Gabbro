/- Kernel-checked bit-vector obligations from contracts and kernel idioms.
   These standalone probes use bit extensionality, modular arithmetic and
   small finite kernel computations. Every theorem prints its dependencies. -/
module
public import Init.Data.BitVec.Bitblast
@[expose] public section

namespace Gabbro.Grammatik.BitVecProben

/-- A1 -- OR of disjoint status bits is their sum. -/
theorem a1_virtio_or_sum (s : BitVec 8) :
    s &&& (3 : BitVec 8) = 0 → s + 3 = s ||| 3 := by
  exact BitVec.add_eq_or_of_and_eq_zero s 3

/-- A2 -- clearing then setting a status bit sets it. -/
theorem a2_reset_sets (v : BitVec 8) :
    ((v &&& ~~~(1 : BitVec 8)) ||| 1) &&& 1 = 1 := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
    hi, decide_true, Bool.true_and]
  cases v.getLsbD i <;> cases (1 : BitVec 8).getLsbD i <;> decide

/-- A3 -- low 12 bits plus the shifted high part reconstruct the frame. -/
theorem a3_frame_split (va : BitVec 64) :
    ((va >>> 12) <<< 12) ||| (va &&& (0xFFF : BitVec 64)) = va := by
  change ((va >>> 12) <<< 12) |||
    (va &&& BitVec.ofNat 64 (2 ^ 12 - 1)) = va
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one]
  by_cases low : i < 12
  · simp [hi, low]
  · simp [hi, low, show 12 + (i - 12) = i by omega]

/-- A4 -- W^X per page-table instance. -/
theorem a4_wx_bit (w x : BitVec 1) :
    ¬(w = 1 ∧ x = 1) ↔ (w &&& x) = 0 := by
  rcases BitVec.eq_zero_or_eq_one w with rfl | rfl <;>
    rcases BitVec.eq_zero_or_eq_one x with rfl | rfl <;> decide

/-- A5 -- the refcount fell by exactly one. -/
theorem a5_refcount_down (n : BitVec 16) :
    n ≠ 0 → n - (n - 1) = 1 := by
  bv_omega

/-- A6 -- consuming a nonzero token decreases its count. -/
theorem a6_token_down (n : BitVec 8) :
    n ≠ 0 → n - 1 < n := by
  bv_omega

/-- A7 -- a wrapping addition had a nonzero length. -/
theorem a7_wrap_nonzero (s l : BitVec 8) :
    (s + l < s) → l ≠ 0 := by
  bv_omega

/-- A8 -- a masked index is in range. -/
theorem a8_mask_bound (i : BitVec 64) :
    (i &&& (0xFFF : BitVec 64)) < (4096 : BitVec 64) := by
  rw [BitVec.lt_def, BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-- A9 -- a single-bit write preserves every other bit. -/
theorem a9_single_bit_update (g : BitVec 32) :
    (((g &&& ~~~(1 : BitVec 32)) ||| 1) &&& ~~~(1 : BitVec 32))
      = g &&& ~~~(1 : BitVec 32) := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
    hi, decide_true, Bool.true_and]
  cases g.getLsbD i <;> cases (1 : BitVec 32).getLsbD i <;> decide

/-- K1 -- lowest-set-bit clear/isolate partition, at full 64-bit width. -/
theorem k1_lsb_partition (x : BitVec 64) :
    (x &&& (x - 1)) ||| (x &&& -x) = x := by
  rw [← BitVec.not_neg x, ← BitVec.and_or_distrib_left,
    BitVec.not_or_self, BitVec.and_allOnes]

/-- K2a -- align-up to 4096 yields a multiple of 4096. -/
theorem k2a_align_mult (x : BitVec 64) :
    (((x + 4095) &&& ~~~(4095 : BitVec 64)) &&& (4095 : BitVec 64)) = 0 := by
  rw [BitVec.and_assoc, BitVec.not_and_self, BitVec.and_zero]

/-- K2b -- align-up is the identity on aligned addresses. -/
theorem k2b_align_idem (x : BitVec 64) :
    x &&& (4095 : BitVec 64) = 0 →
      (x + 4095) &&& ~~~(4095 : BitVec 64) = x := by
  intro aligned
  rw [BitVec.add_eq_or_of_and_eq_zero x 4095 aligned,
    BitVec.and_or_distrib_right, BitVec.and_not_self, BitVec.or_zero]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  have bit := congrArg (fun v : BitVec 64 => v.getLsbD i) aligned
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at bit
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not,
    hi, decide_true, Bool.true_and]
  cases x.getLsbD i <;> cases (4095 : BitVec 64).getLsbD i <;> simp_all

/-- K3 -- page-table index extraction is in range. -/
theorem k3_pt_index (va : BitVec 64) :
    ((va >>> 12) &&& (0x1FF : BitVec 64)) < (512 : BitVec 64) := by
  rw [BitVec.lt_def, BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-- K4 -- one CRC-8 byte, MSB-first, polynomial 0x07, init folded in. -/
def crc8Byte (d : BitVec 8) : BitVec 8 :=
  let s0 := d
  let s1 := if s0.msb then (s0 <<< 1) ^^^ (0x07 : BitVec 8) else s0 <<< 1
  let s2 := if s1.msb then (s1 <<< 1) ^^^ (0x07 : BitVec 8) else s1 <<< 1
  let s3 := if s2.msb then (s2 <<< 1) ^^^ (0x07 : BitVec 8) else s2 <<< 1
  let s4 := if s3.msb then (s3 <<< 1) ^^^ (0x07 : BitVec 8) else s3 <<< 1
  let s5 := if s4.msb then (s4 <<< 1) ^^^ (0x07 : BitVec 8) else s4 <<< 1
  let s6 := if s5.msb then (s5 <<< 1) ^^^ (0x07 : BitVec 8) else s5 <<< 1
  let s7 := if s6.msb then (s6 <<< 1) ^^^ (0x07 : BitVec 8) else s6 <<< 1
  let s8 := if s7.msb then (s7 <<< 1) ^^^ (0x07 : BitVec 8) else s7 <<< 1
  s8

private def crc8Step (x : BitVec 8) : BitVec 8 :=
  if x.msb then (x <<< 1) ^^^ 7 else x <<< 1

private theorem crc8Step_linear (a b : BitVec 8) :
    crc8Step (a ^^^ b) = crc8Step a ^^^ crc8Step b := by
  unfold crc8Step
  rw [BitVec.msb_xor]
  cases ha : a.msb <;> cases hb : b.msb <;>
    simp only [ha, hb, Bool.false_xor, Bool.true_xor, Bool.not_false,
      Bool.not_true, Bool.false_eq_true, ite_false, ite_true,
      BitVec.shiftLeft_xor_distrib]
  all_goals
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro i hi
    simp only [BitVec.getLsbD_xor]
    cases (a <<< 1).getLsbD i <;> cases (b <<< 1).getLsbD i <;>
      cases (7 : BitVec 8).getLsbD i <;> decide

/-- K4a -- closed known answer for a zero byte. -/
theorem k4a_crc_zero : crc8Byte 0x00 = 0x00 := by
  decide +kernel

/-- The all-ones byte has CRC-8 value 0xF3. -/
theorem k4a_crc_ff : crc8Byte 0xFF = 0xF3 := by
  decide +kernel

/-- K4b -- eight linear steps give a GF(2)-linear CRC byte operation. -/
theorem k4b_crc_linear (a b : BitVec 8) :
    crc8Byte (a ^^^ b) = crc8Byte a ^^^ crc8Byte b := by
  change crc8Step (crc8Step (crc8Step (crc8Step
    (crc8Step (crc8Step (crc8Step (crc8Step (a ^^^ b)))))))) =
    crc8Step (crc8Step (crc8Step (crc8Step
      (crc8Step (crc8Step (crc8Step (crc8Step a))))))) ^^^
    crc8Step (crc8Step (crc8Step (crc8Step
      (crc8Step (crc8Step (crc8Step (crc8Step b)))))))
  simp only [crc8Step_linear]

/-- K5 -- one Newton step gives the odd modular inverse modulo four. -/
theorem k5_newton_mod4 (x : BitVec 32) :
    (x &&& (1 : BitVec 32)) = 1 → ((x * (2 - x)) &&& (3 : BitVec 32)) = 1 := by
  intro odd
  have small : ∀ y : BitVec 2, y &&& 1 = 1 → (y * (2 - y)) &&& 3 = 1 := by
    clear odd x
    decide +kernel
  have oddLow := congrArg (BitVec.setWidth 2) odd
  change (x &&& BitVec.ofNat 32 1).setWidth 2 = (BitVec.ofNat 32 1).setWidth 2 at oddLow
  simp only [BitVec.setWidth_and,
    BitVec.setWidth_ofNat_of_le (by decide : 2 ≤ 32)] at oddLow
  have subtractLow : ((2 : BitVec 32) - x).setWidth 2 = 2 - x.setWidth 2 := by
    bv_omega
  have resultLow : ((x * (2 - x)) &&& (3 : BitVec 32)).setWidth 2 =
      (1 : BitVec 32).setWidth 2 := by
    simp only [BitVec.setWidth_and, BitVec.setWidth_mul _ _ (by decide : 2 ≤ 32),
      subtractLow, show (3 : BitVec 32).setWidth 2 = 3 from rfl,
      show (1 : BitVec 32).setWidth 2 = 1 from rfl]
    exact small (x.setWidth 2) oddLow
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  by_cases low : i < 2
  · have bit := congrArg (fun v : BitVec 2 => v.getLsbD i) resultLow
    simpa only [BitVec.getLsbD_setWidth, low, decide_true, Bool.true_and] using bit
  · change ((x * (2 - x)) &&& BitVec.ofNat 32 (2 ^ 2 - 1)).getLsbD i =
      (BitVec.ofNat 32 (2 ^ 0)).getLsbD i
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat,
      Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow,
      low, decide_false, Bool.and_false, Bool.false_and,
      show ¬ (0 = i) by omega]

/-- C1 -- the lowest-set-bit partition also has a small exhaustive witness. -/
theorem c1_kernel_lsb4 (x : BitVec 4) :
    (x &&& (x - 1)) ||| (x &&& -x) = x := by
  decide +revert

#print axioms a1_virtio_or_sum
#print axioms a2_reset_sets
#print axioms a3_frame_split
#print axioms a4_wx_bit
#print axioms a5_refcount_down
#print axioms a6_token_down
#print axioms a7_wrap_nonzero
#print axioms a8_mask_bound
#print axioms a9_single_bit_update
#print axioms k1_lsb_partition
#print axioms k2a_align_mult
#print axioms k2b_align_idem
#print axioms k3_pt_index
#print axioms k4a_crc_zero
#print axioms k4a_crc_ff
#print axioms k4b_crc_linear
#print axioms k5_newton_mod4
#print axioms c1_kernel_lsb4

end Gabbro.Grammatik.BitVecProben
