module
public import Runner.Basis.FloatingSequence
import all Init.Data.SInt.Float
import all Init.Data.SInt.Float32
@[expose] public section

namespace Runner

/-! Adapters to the existing Std primitives. This file introduces no arithmetic
    model: both conversions below pass the same integer to Std's conversion. -/

theorem uint64_toFloat_nonnegative (value : W) (h : value.msb = false) :
    (UInt64.ofBitVec value).toFloat = (Int64.ofBitVec value).toFloat := by
  unfold Int64.toFloat Float.Model.ofInt64 Float.Model.UnpackedFloat.ofInt64
  change Float.ofModel (Float.Model.pack (Float.Model.UnpackedFloat.ofInt
      Float.Model.Format.binary64 (value.toNat : Int))) =
    Float.ofModel (Float.Model.pack (Float.Model.UnpackedFloat.ofInt
      Float.Model.Format.binary64 value.toInt))
  rw [BitVec.toInt_eq_toNat_of_msb h]

theorem uint64_toFloat32_nonnegative (value : W) (h : value.msb = false) :
    (UInt64.ofBitVec value).toFloat32 = (Int64.ofBitVec value).toFloat32 := by
  unfold Int64.toFloat32 Float32.Model.ofInt64 Float.Model.UnpackedFloat.ofInt64
  change Float32.ofModel (Float32.Model.pack (Float.Model.UnpackedFloat.ofInt
      Float.Model.Format.binary32 (value.toNat : Int))) =
    Float32.ofModel (Float32.Model.pack (Float.Model.UnpackedFloat.ofInt
      Float.Model.Format.binary32 value.toInt))
  rw [BitVec.toInt_eq_toNat_of_msb h]

theorem nativeFromUInt64_low {format : FPFormat} {value result : W} (h : value.msb = false)
    (hr : NativeFPEval (.fromInt64 format) value 0 result) :
    NativeFPEval (.fromUInt64 format) value 0 result := by
  cases format
  · simpa only [NativeFPEval, nativeFP, uint64_toFloat32_nonnegative value h] using hr
  · simpa only [NativeFPEval, nativeFP, uint64_toFloat_nonnegative value h] using hr

end Runner
