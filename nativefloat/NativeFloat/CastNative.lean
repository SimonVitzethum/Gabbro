/- Native value boundaries for the common stored-word cast proofs. -/
module
public import NativeFloat.CastHigh
import all NativeFloat.CastDecode
import all NativeFloat.CastHigh
import all Init.Data.SInt.Float
import all Init.Data.SInt.Float32
@[expose] public section

namespace RootNativeFloat.CastNative
open Float.Model
open Float.Model.UnpackedFloat
open CastDecode

private theorem read64 (word : BitVec 64) :
    (Float.ofBits (UInt64.ofBitVec word)).toModel.unpack = UnpackedFloat.unpack Format.binary64 word :=
  repack_unpack Format.binary64 (Or.inr rfl) word

private theorem read32 (word : BitVec 32) :
    (Float32.ofBits (UInt32.ofBitVec word)).toModel.unpack = UnpackedFloat.unpack Format.binary32 word :=
  repack_unpack Format.binary32 (Or.inl rfl) word

private theorem min64 : Int64.minValue.toFloat.toModel.unpack =
    .finite .negative (2 ^ 52) 11 (Nat.two_pow_pos _) := by cbv

private theorem max64 : (UInt64.ofNat (2 ^ 63)).toFloat.toModel.unpack =
    .finite .positive (2 ^ 52) 11 (Nat.two_pow_pos _) := by cbv

private theorem min32 : Int64.minValue.toFloat32.toModel.unpack =
    .finite .negative (2 ^ 23) 40 (Nat.two_pow_pos _) := by cbv

private theorem max32 : (UInt64.ofNat (2 ^ 63)).toFloat32.toModel.unpack =
    .finite .positive (2 ^ 23) 40 (Nat.two_pow_pos _) := by cbv

private theorem bias64 : (Float.ofBits 0x43e0000000000000).toModel.unpack =
    UnpackedFloat.unpack Format.binary64 (limitBits Format.binary64 63) := by
  have word : (0x43e0000000000000 : BitVec 64) = limitBits Format.binary64 63 := by decide
  exact (read64 0x43e0000000000000).trans (congrArg (UnpackedFloat.unpack Format.binary64) word)

private theorem bias32 : (Float32.ofBits 0x5f000000).toModel.unpack =
    UnpackedFloat.unpack Format.binary32 (limitBits Format.binary32 63) := by
  have word : (0x5f000000 : BitVec 32) = limitBits Format.binary32 63 := by decide
  exact (read32 0x5f000000).trans (congrArg (UnpackedFloat.unpack Format.binary32) word)

private theorem domain64 (value : Float) (domain : Domain Format.binary64 value.toModel.unpack) :
    value.isNaN = false ∧ Float.lt value Int64.minValue.toFloat = false ∧
      Float.lt value (UInt64.ofNat (2 ^ 63)).toFloat = true := by
  change value.toModel.unpack.isNaN = false ∧
    value.toModel.unpack.lt Int64.minValue.toFloat.toModel.unpack = false ∧
    value.toModel.unpack.lt (UInt64.ofNat (2 ^ 63)).toFloat.toModel.unpack = true
  rw [min64, max64]
  exact domain

private theorem domain32 (value : Float32) (domain : Domain Format.binary32 value.toModel.unpack) :
    value.isNaN = false ∧ Float32.lt value Int64.minValue.toFloat32 = false ∧
      Float32.lt value (UInt64.ofNat (2 ^ 63)).toFloat32 = true := by
  change value.toModel.unpack.isNaN = false ∧
    value.toModel.unpack.lt Int64.minValue.toFloat32.toModel.unpack = false ∧
    value.toModel.unpack.lt (UInt64.ofNat (2 ^ 63)).toFloat32.toModel.unpack = true
  rw [min32, max32]
  exact domain

end RootNativeFloat.CastNative
