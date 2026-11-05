module

public import NativeFloat.Primitives

public section

namespace RootNativeFloat.Contracts

/-- Exact native saturation and reduced signed-truncation domains, including NaN and overflow.
    These are explicit hardware assumptions; this module supplies no implementation or instance. -/
structure SaturatingCast : Prop where
  float32_cvtt_domain : ∀ (word : BitVec 32)
      (small : (word &&& 0x7fffffff).ult 0x5f000000 = true),
      let x := Float32.hwOfBits (UInt32.ofBitVec word)
      x.hwIsNaN = false ∧ Float32.hwLt x Int64.minValue.hwToFloat32 = false ∧
        Float32.hwLt x (UInt64.ofNat (2 ^ 63)).hwToFloat32 = true

  float64_cvtt_domain : ∀ (word : BitVec 64)
      (small : (word &&& 0x7fffffffffffffff).ult 0x43e0000000000000 = true),
      let x := Float.hwOfBits (UInt64.ofBitVec word)
      x.hwIsNaN = false ∧ Float.hwLt x Int64.minValue.hwToFloat = false ∧
        Float.hwLt x (UInt64.ofNat (2 ^ 63)).hwToFloat = true

  float32_toInt64_nan : ∀ (word : BitVec 32)
      (nan : (0x7f800000 : BitVec 32).ult (word &&& 0x7fffffff) = true),
      (Float32.hwOfBits (UInt32.ofBitVec word)).hwToInt64.toBitVec = 0

  float64_toInt64_nan : ∀ (word : BitVec 64)
      (nan : (0x7ff0000000000000 : BitVec 64).ult (word &&& 0x7fffffffffffffff) = true),
      (Float.hwOfBits (UInt64.ofBitVec word)).hwToInt64.toBitVec = 0

  float32_toInt64_overflow : ∀ (word : BitVec 32)
      (nan : (0x7f800000 : BitVec 32).ult (word &&& 0x7fffffff) = false)
      (large : (word &&& 0x7fffffff).ult 0x5f000000 = false),
      (Float32.hwOfBits (UInt32.ofBitVec word)).hwToInt64.toBitVec =
        if word.msb then 0x8000000000000000 else 0x7fffffffffffffff

  float64_toInt64_overflow : ∀ (word : BitVec 64)
      (nan : (0x7ff0000000000000 : BitVec 64).ult (word &&& 0x7fffffffffffffff) = false)
      (large : (word &&& 0x7fffffffffffffff).ult 0x43e0000000000000 = false),
      (Float.hwOfBits (UInt64.ofBitVec word)).hwToInt64.toBitVec =
        if word.msb then 0x8000000000000000 else 0x7fffffffffffffff

  float32_toUInt64_high : ∀ (word : BitVec 32) (nonnegative : word.msb = false)
      (lower : (word &&& 0x7fffffff).ult 0x5f000000 = false)
      (upper : (word &&& 0x7fffffff).ult 0x5f800000 = true),
      let x := Float32.hwOfBits (UInt32.ofBitVec word)
      let reduced := Float32.hwSub x (Float32.hwOfBits 0x5f000000)
      x.hwToUInt64.toBitVec = reduced.hwToInt64.toBitVec ||| 0x8000000000000000 ∧
        reduced.hwIsNaN = false ∧ Float32.hwLt reduced Int64.minValue.hwToFloat32 = false ∧
        Float32.hwLt reduced (UInt64.ofNat (2 ^ 63)).hwToFloat32 = true

  float64_toUInt64_high : ∀ (word : BitVec 64) (nonnegative : word.msb = false)
      (lower : (word &&& 0x7fffffffffffffff).ult 0x43e0000000000000 = false)
      (upper : (word &&& 0x7fffffffffffffff).ult 0x43f0000000000000 = true),
      let x := Float.hwOfBits (UInt64.ofBitVec word)
      let reduced := Float.hwSub x (Float.hwOfBits 0x43e0000000000000)
      x.hwToUInt64.toBitVec = reduced.hwToInt64.toBitVec ||| 0x8000000000000000 ∧
        reduced.hwIsNaN = false ∧ Float.hwLt reduced Int64.minValue.hwToFloat = false ∧
        Float.hwLt reduced (UInt64.ofNat (2 ^ 63)).hwToFloat = true

  float32_toUInt64_low : ∀ (word : BitVec 32) (nonnegative : word.msb = false)
      (small : (word &&& 0x7fffffff).ult 0x5f000000 = true),
      (Float32.hwOfBits (UInt32.ofBitVec word)).hwToUInt64.toBitVec =
        (Float32.hwOfBits (UInt32.ofBitVec word)).hwToInt64.toBitVec

  float64_toUInt64_low : ∀ (word : BitVec 64) (nonnegative : word.msb = false)
      (small : (word &&& 0x7fffffffffffffff).ult 0x43e0000000000000 = true),
      (Float.hwOfBits (UInt64.ofBitVec word)).hwToUInt64.toBitVec =
        (Float.hwOfBits (UInt64.ofBitVec word)).hwToInt64.toBitVec

  float32_toUInt64_nan : ∀ (word : BitVec 32)
      (nan : (0x7f800000 : BitVec 32).ult (word &&& 0x7fffffff) = true),
      (Float32.hwOfBits (UInt32.ofBitVec word)).hwToUInt64.toBitVec = 0

  float64_toUInt64_nan : ∀ (word : BitVec 64)
      (nan : (0x7ff0000000000000 : BitVec 64).ult (word &&& 0x7fffffffffffffff) = true),
      (Float.hwOfBits (UInt64.ofBitVec word)).hwToUInt64.toBitVec = 0

  float32_toUInt64_negative : ∀ (word : BitVec 32) (negative : word.msb = true),
      (Float32.hwOfBits (UInt32.ofBitVec word)).hwToUInt64.toBitVec = 0

  float64_toUInt64_negative : ∀ (word : BitVec 64) (negative : word.msb = true),
      (Float.hwOfBits (UInt64.ofBitVec word)).hwToUInt64.toBitVec = 0

  float32_toUInt64_overflow : ∀ (word : BitVec 32) (nonnegative : word.msb = false)
      (nan : (0x7f800000 : BitVec 32).ult (word &&& 0x7fffffff) = false)
      (large : (word &&& 0x7fffffff).ult 0x5f800000 = false),
      (Float32.hwOfBits (UInt32.ofBitVec word)).hwToUInt64.toBitVec = -1#64

  float64_toUInt64_overflow : ∀ (word : BitVec 64) (nonnegative : word.msb = false)
      (nan : (0x7ff0000000000000 : BitVec 64).ult (word &&& 0x7fffffffffffffff) = false)
      (large : (word &&& 0x7fffffffffffffff).ult 0x43f0000000000000 = false),
      (Float.hwOfBits (UInt64.ofBitVec word)).hwToUInt64.toBitVec = -1#64

end RootNativeFloat.Contracts
