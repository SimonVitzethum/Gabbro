module
public import Runner.Beweis.Handler.Gerade
@[expose] public section

namespace Runner.Beweis
open Runner.X86 Runner.Prog

/-! Scalar storage facts, independent of native floating arithmetic. -/

@[simp] theorem fpLow32_idem (value : W) : fpLow32 (fpLow32 value) = fpLow32 value := by
  unfold fpLow32
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

@[simp] theorem scalar32_clear :
    (~~~(BitVec.ofNat 128 0xFFFFFFFF)).setWidth 32 = 0 := by decide

@[simp] theorem scalar64_clear :
    (~~~(BitVec.ofNat 128 0xFFFFFFFFFFFFFFFF)).setWidth 64 = 0 := by decide

@[simp] theorem xmmWord_setScalar (x : X) (format : FPFormat) (r : Xmm) (value : W) :
    (x.setScalar format r value).xmmWord format r =
      (match format with | .f32 => fpLow32 value | .f64 => value) := by
  cases format <;>
    simp (disch := decide) [X.setScalar, X.xmmWord, X.setXmm, fpLow32,
      BitVec.setWidth_setWidth_of_le]

/-- Saving the three UCOMIS flags reconstructs precisely their observable mask. -/
theorem pack_compare_flags (value : W) :
    ((if value.getLsbD 0 then (1 : W) else 0) |||
      ((if value.getLsbD 2 then (1 : W) else 0) <<< 2)) |||
      ((if value.getLsbD 6 then (1 : W) else 0) <<< 6) = value &&& 0x45 := by
  have mask : (0x45 : W) =
      (BitVec.twoPow 64 0 ||| BitVec.twoPow 64 2) ||| BitVec.twoPow 64 6 := by decide
  rw [mask, BitVec.and_or_distrib_left, BitVec.and_or_distrib_left,
    BitVec.and_twoPow, BitVec.and_twoPow, BitVec.and_twoPow]
  cases value.getLsbD 0 <;> cases value.getLsbD 2 <;> cases value.getLsbD 6 <;> rfl

theorem fpNegWord_word32 (value : W) :
    fpNegWord .f32 value = fpLow32 value ^^^ 0x80000000 := by
  rw [fpNegWord, BitVec.setWidth_xor]
  rfl

private theorem uint32_bne (a b : BitVec 32) :
    (UInt32.ofBitVec a != UInt32.ofBitVec b) = (a != b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne]
  constructor
  · intro h same
    exact h (congrArg UInt32.ofBitVec same)
  · intro h same
    exact h (congrArg UInt32.toBitVec same)

private theorem uint64_bne (a b : W) :
    (UInt64.ofBitVec a != UInt64.ofBitVec b) = (a != b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne]
  constructor
  · intro h same
    exact h (congrArg UInt64.ofBitVec same)
  · intro h same
    exact h (congrArg UInt64.toBitVec same)

private theorem extend32_bne (a b : BitVec 32) :
    (a.setWidth 64 != b.setWidth 64) = (a != b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne]
  constructor
  · intro h same
    exact h (congrArg (fun value : BitVec 32 => value.setWidth 64) same)
  · intro h same
    apply h
    have low := congrArg (fun value : W => value.setWidth 32) same
    simpa only [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq] using low

theorem fpFiniteWord_word32 (value : W) :
    fpFiniteWord .f32 value = flagWord ((fpLow32 value &&& 0x7F800000) != 0x7F800000) := by
  have guard : ((fpLow32 value &&& 0x7F800000) != (0x7F800000 : W)) =
      (((value.setWidth 32) &&& 0x7F800000) != (0x7F800000 : BitVec 32)) := by
    change (((value.setWidth 32).setWidth 64 &&& (0x7F800000 : BitVec 32).setWidth 64) !=
      (0x7F800000 : BitVec 32).setWidth 64) = _
    rw [← BitVec.setWidth_and, extend32_bne]
  change flagWord (UInt32.ofBitVec ((value.setWidth 32) &&& 0x7F800000) !=
    UInt32.ofBitVec 0x7F800000) = _
  rw [uint32_bne, guard]

theorem fpFiniteWord_word64 (value : W) :
    fpFiniteWord .f64 value = flagWord ((value &&& 0x7FF0000000000000) != 0x7FF0000000000000) := by
  change flagWord (UInt64.ofBitVec (value &&& 0x7FF0000000000000) !=
    UInt64.ofBitVec 0x7FF0000000000000) = _
  rw [uint64_bne]

end Runner.Beweis
