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

end Runner.Beweis
