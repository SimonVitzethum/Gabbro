module

public import Init.Data.SInt.Float
public import Init.Data.SInt.Float32

public section

namespace RootNativeFloat.Contracts

/-- Exact native saturation and reduced signed-truncation domains, including NaN and overflow.
    These are explicit hardware assumptions; this module supplies no implementation or instance. -/
structure SaturatingCast : Prop where
  float32_cvtt_domain : ∀ (word : BitVec 32)
      (small : (word &&& 0x7fffffff).ult 0x5f000000 = true),
      let x := Float32.ofBits (UInt32.ofBitVec word)
      x.isNaN = false ∧ Float32.lt x Int64.minValue.toFloat32 = false ∧
        Float32.lt x (UInt64.ofNat (2 ^ 63)).toFloat32 = true

  float64_cvtt_domain : ∀ (word : BitVec 64)
      (small : (word &&& 0x7fffffffffffffff).ult 0x43e0000000000000 = true),
      let x := Float.ofBits (UInt64.ofBitVec word)
      x.isNaN = false ∧ Float.lt x Int64.minValue.toFloat = false ∧
        Float.lt x (UInt64.ofNat (2 ^ 63)).toFloat = true

  float32_toInt64_nan : ∀ (word : BitVec 32)
      (nan : (0x7f800000 : BitVec 32).ult (word &&& 0x7fffffff) = true),
      (Float32.ofBits (UInt32.ofBitVec word)).toInt64.toBitVec = 0

  float64_toInt64_nan : ∀ (word : BitVec 64)
      (nan : (0x7ff0000000000000 : BitVec 64).ult (word &&& 0x7fffffffffffffff) = true),
      (Float.ofBits (UInt64.ofBitVec word)).toInt64.toBitVec = 0

  float32_toInt64_overflow : ∀ (word : BitVec 32)
      (nan : (0x7f800000 : BitVec 32).ult (word &&& 0x7fffffff) = false)
      (large : (word &&& 0x7fffffff).ult 0x5f000000 = false),
      (Float32.ofBits (UInt32.ofBitVec word)).toInt64.toBitVec =
        if word.msb then 0x8000000000000000 else 0x7fffffffffffffff

  float64_toInt64_overflow : ∀ (word : BitVec 64)
      (nan : (0x7ff0000000000000 : BitVec 64).ult (word &&& 0x7fffffffffffffff) = false)
      (large : (word &&& 0x7fffffffffffffff).ult 0x43e0000000000000 = false),
      (Float.ofBits (UInt64.ofBitVec word)).toInt64.toBitVec =
        if word.msb then 0x8000000000000000 else 0x7fffffffffffffff

  float32_toUInt64_high : ∀ (word : BitVec 32) (nonnegative : word.msb = false)
      (lower : (word &&& 0x7fffffff).ult 0x5f000000 = false)
      (upper : (word &&& 0x7fffffff).ult 0x5f800000 = true),
      let x := Float32.ofBits (UInt32.ofBitVec word)
      let reduced := Float32.sub x (Float32.ofBits 0x5f000000)
      x.toUInt64.toBitVec = reduced.toInt64.toBitVec ||| 0x8000000000000000 ∧
        reduced.isNaN = false ∧ Float32.lt reduced Int64.minValue.toFloat32 = false ∧
        Float32.lt reduced (UInt64.ofNat (2 ^ 63)).toFloat32 = true

  float64_toUInt64_high : ∀ (word : BitVec 64) (nonnegative : word.msb = false)
      (lower : (word &&& 0x7fffffffffffffff).ult 0x43e0000000000000 = false)
      (upper : (word &&& 0x7fffffffffffffff).ult 0x43f0000000000000 = true),
      let x := Float.ofBits (UInt64.ofBitVec word)
      let reduced := Float.sub x (Float.ofBits 0x43e0000000000000)
      x.toUInt64.toBitVec = reduced.toInt64.toBitVec ||| 0x8000000000000000 ∧
        reduced.isNaN = false ∧ Float.lt reduced Int64.minValue.toFloat = false ∧
        Float.lt reduced (UInt64.ofNat (2 ^ 63)).toFloat = true

  float32_toUInt64_low : ∀ (word : BitVec 32) (nonnegative : word.msb = false)
      (small : (word &&& 0x7fffffff).ult 0x5f000000 = true),
      (Float32.ofBits (UInt32.ofBitVec word)).toUInt64.toBitVec =
        (Float32.ofBits (UInt32.ofBitVec word)).toInt64.toBitVec

  float64_toUInt64_low : ∀ (word : BitVec 64) (nonnegative : word.msb = false)
      (small : (word &&& 0x7fffffffffffffff).ult 0x43e0000000000000 = true),
      (Float.ofBits (UInt64.ofBitVec word)).toUInt64.toBitVec =
        (Float.ofBits (UInt64.ofBitVec word)).toInt64.toBitVec

  float32_toUInt64_nan : ∀ (word : BitVec 32)
      (nan : (0x7f800000 : BitVec 32).ult (word &&& 0x7fffffff) = true),
      (Float32.ofBits (UInt32.ofBitVec word)).toUInt64.toBitVec = 0

  float64_toUInt64_nan : ∀ (word : BitVec 64)
      (nan : (0x7ff0000000000000 : BitVec 64).ult (word &&& 0x7fffffffffffffff) = true),
      (Float.ofBits (UInt64.ofBitVec word)).toUInt64.toBitVec = 0

  float32_toUInt64_negative : ∀ (word : BitVec 32) (negative : word.msb = true),
      (Float32.ofBits (UInt32.ofBitVec word)).toUInt64.toBitVec = 0

  float64_toUInt64_negative : ∀ (word : BitVec 64) (negative : word.msb = true),
      (Float.ofBits (UInt64.ofBitVec word)).toUInt64.toBitVec = 0

  float32_toUInt64_overflow : ∀ (word : BitVec 32) (nonnegative : word.msb = false)
      (nan : (0x7f800000 : BitVec 32).ult (word &&& 0x7fffffff) = false)
      (large : (word &&& 0x7fffffff).ult 0x5f800000 = false),
      (Float32.ofBits (UInt32.ofBitVec word)).toUInt64.toBitVec = -1#64

  float64_toUInt64_overflow : ∀ (word : BitVec 64) (nonnegative : word.msb = false)
      (nan : (0x7ff0000000000000 : BitVec 64).ult (word &&& 0x7fffffffffffffff) = false)
      (large : (word &&& 0x7fffffffffffffff).ult 0x43f0000000000000 = false),
      (Float.ofBits (UInt64.ofBitVec word)).toUInt64.toBitVec = -1#64

end RootNativeFloat.Contracts
