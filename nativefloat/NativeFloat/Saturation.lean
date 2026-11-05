/- Std-native equalities for every branch of the portable saturating casts. -/
module
public import NativeFloat.CastNative
import all NativeFloat.CastDecode
import all NativeFloat.CastBounds
import all NativeFloat.CastHigh
import all NativeFloat.CastNative
import all Init.Data.SInt.Float
import all Init.Data.SInt.Float32
@[expose] public section

namespace RootNativeFloat
open Float.Model
open Float.Model.UnpackedFloat
open CastDecode CastBounds CastHigh CastNative

theorem float64_toInt64_nan (word : BitVec 64)
    (nan : (0x7ff0000000000000 : BitVec 64).ult (word &&& 0x7fffffffffffffff) = true) :
    (Float.ofBits (UInt64.ofBitVec word)).toInt64.toBitVec = 0 := by
  change (Float.ofBits (UInt64.ofBitVec word)).toModel.unpack.toInt64.toBitVec = 0
  rw [read64, decoded_nan Format.binary64 (Or.inr rfl) word nan]
  rfl

theorem float32_toInt64_nan (word : BitVec 32)
    (nan : (0x7f800000 : BitVec 32).ult (word &&& 0x7fffffff) = true) :
    (Float32.ofBits (UInt32.ofBitVec word)).toInt64.toBitVec = 0 := by
  change (Float32.ofBits (UInt32.ofBitVec word)).toModel.unpack.toInt64.toBitVec = 0
  rw [read32, decoded_nan Format.binary32 (Or.inl rfl) word nan]
  rfl

theorem float64_toUInt64_nan (word : BitVec 64)
    (nan : (0x7ff0000000000000 : BitVec 64).ult (word &&& 0x7fffffffffffffff) = true) :
    (Float.ofBits (UInt64.ofBitVec word)).toUInt64.toBitVec = 0 := by
  change (Float.ofBits (UInt64.ofBitVec word)).toModel.unpack.toUInt64.toBitVec = 0
  rw [read64, decoded_nan Format.binary64 (Or.inr rfl) word nan]
  exact unsigned_zero

theorem float32_toUInt64_nan (word : BitVec 32)
    (nan : (0x7f800000 : BitVec 32).ult (word &&& 0x7fffffff) = true) :
    (Float32.ofBits (UInt32.ofBitVec word)).toUInt64.toBitVec = 0 := by
  change (Float32.ofBits (UInt32.ofBitVec word)).toModel.unpack.toUInt64.toBitVec = 0
  rw [read32, decoded_nan Format.binary32 (Or.inl rfl) word nan]
  exact unsigned_zero

theorem float64_cvtt_domain (word : BitVec 64)
    (small : (word &&& 0x7fffffffffffffff).ult 0x43e0000000000000 = true) :
    let x := Float.ofBits (UInt64.ofBitVec word)
    x.isNaN = false ∧ Float.lt x Int64.minValue.toFloat = false ∧
      Float.lt x (UInt64.ofNat (2 ^ 63)).toFloat = true := by
  apply domain64
  rw [read64]
  exact decoded_cvtt Format.binary64 (Or.inr rfl) word small

theorem float32_cvtt_domain (word : BitVec 32)
    (small : (word &&& 0x7fffffff).ult 0x5f000000 = true) :
    let x := Float32.ofBits (UInt32.ofBitVec word)
    x.isNaN = false ∧ Float32.lt x Int64.minValue.toFloat32 = false ∧
      Float32.lt x (UInt64.ofNat (2 ^ 63)).toFloat32 = true := by
  apply domain32
  rw [read32]
  exact decoded_cvtt Format.binary32 (Or.inl rfl) word small

theorem float64_toInt64_overflow (word : BitVec 64)
    (nan : (0x7ff0000000000000 : BitVec 64).ult (word &&& 0x7fffffffffffffff) = false)
    (large : (word &&& 0x7fffffffffffffff).ult 0x43e0000000000000 = false) :
    (Float.ofBits (UInt64.ofBitVec word)).toInt64.toBitVec =
      if word.msb then 0x8000000000000000 else 0x7fffffffffffffff := by
  change (Float.ofBits (UInt64.ofBitVec word)).toModel.unpack.toInt64.toBitVec = _
  rw [read64]
  exact decoded_signed_overflow Format.binary64 (Or.inr rfl) word nan large

theorem float32_toInt64_overflow (word : BitVec 32)
    (nan : (0x7f800000 : BitVec 32).ult (word &&& 0x7fffffff) = false)
    (large : (word &&& 0x7fffffff).ult 0x5f000000 = false) :
    (Float32.ofBits (UInt32.ofBitVec word)).toInt64.toBitVec =
      if word.msb then 0x8000000000000000 else 0x7fffffffffffffff := by
  change (Float32.ofBits (UInt32.ofBitVec word)).toModel.unpack.toInt64.toBitVec = _
  rw [read32]
  exact decoded_signed_overflow Format.binary32 (Or.inl rfl) word nan large

theorem float64_toUInt64_negative (word : BitVec 64) (negative : word.msb = true) :
    (Float.ofBits (UInt64.ofBitVec word)).toUInt64.toBitVec = 0 := by
  change (Float.ofBits (UInt64.ofBitVec word)).toModel.unpack.toUInt64.toBitVec = 0
  rw [read64]
  exact decoded_negative_unsigned Format.binary64 word negative

theorem float32_toUInt64_negative (word : BitVec 32) (negative : word.msb = true) :
    (Float32.ofBits (UInt32.ofBitVec word)).toUInt64.toBitVec = 0 := by
  change (Float32.ofBits (UInt32.ofBitVec word)).toModel.unpack.toUInt64.toBitVec = 0
  rw [read32]
  exact decoded_negative_unsigned Format.binary32 word negative

theorem float64_toUInt64_low (word : BitVec 64) (nonnegative : word.msb = false)
    (small : (word &&& 0x7fffffffffffffff).ult 0x43e0000000000000 = true) :
    (Float.ofBits (UInt64.ofBitVec word)).toUInt64.toBitVec =
      (Float.ofBits (UInt64.ofBitVec word)).toInt64.toBitVec := by
  change (Float.ofBits (UInt64.ofBitVec word)).toModel.unpack.toUInt64.toBitVec =
    (Float.ofBits (UInt64.ofBitVec word)).toModel.unpack.toInt64.toBitVec
  rw [read64]
  exact decoded_unsigned_low Format.binary64 (Or.inr rfl) word nonnegative small

theorem float32_toUInt64_low (word : BitVec 32) (nonnegative : word.msb = false)
    (small : (word &&& 0x7fffffff).ult 0x5f000000 = true) :
    (Float32.ofBits (UInt32.ofBitVec word)).toUInt64.toBitVec =
      (Float32.ofBits (UInt32.ofBitVec word)).toInt64.toBitVec := by
  change (Float32.ofBits (UInt32.ofBitVec word)).toModel.unpack.toUInt64.toBitVec =
    (Float32.ofBits (UInt32.ofBitVec word)).toModel.unpack.toInt64.toBitVec
  rw [read32]
  exact decoded_unsigned_low Format.binary32 (Or.inl rfl) word nonnegative small

theorem float64_toUInt64_overflow (word : BitVec 64) (nonnegative : word.msb = false)
    (nan : (0x7ff0000000000000 : BitVec 64).ult (word &&& 0x7fffffffffffffff) = false)
    (large : (word &&& 0x7fffffffffffffff).ult 0x43f0000000000000 = false) :
    (Float.ofBits (UInt64.ofBitVec word)).toUInt64.toBitVec = -1#64 := by
  change (Float.ofBits (UInt64.ofBitVec word)).toModel.unpack.toUInt64.toBitVec = -1#64
  rw [read64]
  exact decoded_unsigned_overflow Format.binary64 (Or.inr rfl) word nonnegative nan large

theorem float32_toUInt64_overflow (word : BitVec 32) (nonnegative : word.msb = false)
    (nan : (0x7f800000 : BitVec 32).ult (word &&& 0x7fffffff) = false)
    (large : (word &&& 0x7fffffff).ult 0x5f800000 = false) :
    (Float32.ofBits (UInt32.ofBitVec word)).toUInt64.toBitVec = -1#64 := by
  change (Float32.ofBits (UInt32.ofBitVec word)).toModel.unpack.toUInt64.toBitVec = -1#64
  rw [read32]
  exact decoded_unsigned_overflow Format.binary32 (Or.inl rfl) word nonnegative nan large

theorem float64_toUInt64_high (word : BitVec 64) (nonnegative : word.msb = false)
    (lower : (word &&& 0x7fffffffffffffff).ult 0x43e0000000000000 = false)
    (upper : (word &&& 0x7fffffffffffffff).ult 0x43f0000000000000 = true) :
    let x := Float.ofBits (UInt64.ofBitVec word)
    let reduced := Float.sub x (Float.ofBits 0x43e0000000000000)
    x.toUInt64.toBitVec = reduced.toInt64.toBitVec ||| 0x8000000000000000 ∧
      reduced.isNaN = false ∧ Float.lt reduced Int64.minValue.toFloat = false ∧
      Float.lt reduced (UInt64.ofNat (2 ^ 63)).toFloat = true := by
  dsimp only
  have post := decoded_high Format.binary64 (Or.inr rfl) word nonnegative lower upper
  dsimp only at post
  have reduced : (Float.sub (Float.ofBits (UInt64.ofBitVec word))
      (Float.ofBits 0x43e0000000000000)).toModel.unpack =
      UnpackedFloat.unpack Format.binary64 (UnpackedFloat.pack Format.binary64
        (UnpackedFloat.sub Format.binary64 (UnpackedFloat.unpack Format.binary64 word)
          (UnpackedFloat.unpack Format.binary64 (limitBits Format.binary64 63)))) := by
    change UnpackedFloat.unpack Format.binary64 (UnpackedFloat.pack Format.binary64
      (UnpackedFloat.sub Format.binary64 (Float.ofBits (UInt64.ofBitVec word)).toModel.unpack
        (Float.ofBits 0x43e0000000000000).toModel.unpack)) = _
    rw [read64, bias64]
  refine ⟨?_, domain64 _ ?_⟩
  · change (Float.ofBits (UInt64.ofBitVec word)).toModel.unpack.toUInt64.toBitVec =
      (Float.sub (Float.ofBits (UInt64.ofBitVec word)) (Float.ofBits 0x43e0000000000000)).toModel.unpack.toInt64.toBitVec ||| _
    rw [read64, reduced]
    exact post.1
  · rw [reduced]
    exact post.2

theorem float32_toUInt64_high (word : BitVec 32) (nonnegative : word.msb = false)
    (lower : (word &&& 0x7fffffff).ult 0x5f000000 = false)
    (upper : (word &&& 0x7fffffff).ult 0x5f800000 = true) :
    let x := Float32.ofBits (UInt32.ofBitVec word)
    let reduced := Float32.sub x (Float32.ofBits 0x5f000000)
    x.toUInt64.toBitVec = reduced.toInt64.toBitVec ||| 0x8000000000000000 ∧
      reduced.isNaN = false ∧ Float32.lt reduced Int64.minValue.toFloat32 = false ∧
      Float32.lt reduced (UInt64.ofNat (2 ^ 63)).toFloat32 = true := by
  dsimp only
  have post := decoded_high Format.binary32 (Or.inl rfl) word nonnegative lower upper
  dsimp only at post
  have reduced : (Float32.sub (Float32.ofBits (UInt32.ofBitVec word))
      (Float32.ofBits 0x5f000000)).toModel.unpack =
      UnpackedFloat.unpack Format.binary32 (UnpackedFloat.pack Format.binary32
        (UnpackedFloat.sub Format.binary32 (UnpackedFloat.unpack Format.binary32 word)
          (UnpackedFloat.unpack Format.binary32 (limitBits Format.binary32 63)))) := by
    change UnpackedFloat.unpack Format.binary32 (UnpackedFloat.pack Format.binary32
      (UnpackedFloat.sub Format.binary32 (Float32.ofBits (UInt32.ofBitVec word)).toModel.unpack
        (Float32.ofBits 0x5f000000).toModel.unpack)) = _
    rw [read32, bias32]
  refine ⟨?_, domain32 _ ?_⟩
  · change (Float32.ofBits (UInt32.ofBitVec word)).toModel.unpack.toUInt64.toBitVec =
      (Float32.sub (Float32.ofBits (UInt32.ofBitVec word)) (Float32.ofBits 0x5f000000)).toModel.unpack.toInt64.toBitVec ||| _
    rw [read32, reduced]
    exact post.1
  · rw [reduced]
    exact post.2

end RootNativeFloat
