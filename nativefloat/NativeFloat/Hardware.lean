module

public import NativeFloat.Contracts.Codec
public import NativeFloat.Contracts.Order
public import NativeFloat.Contracts.SourceInt
public import NativeFloat.Contracts.Unsigned
public import NativeFloat.Contracts.SaturatingCast
public import NativeFloat.Contracts.Literal

public section

namespace RootNativeFloat

/-- The named native floating-point hardware boundary. A caller must supply all
    contracts explicitly; this package defines no default or global instance. -/
class Hardware : Prop where
  codec : Contracts.Codec
  order : Contracts.Order
  sourceInt : Contracts.SourceInt
  unsigned : Contracts.Unsigned
  saturatingCast : Contracts.SaturatingCast
  literal : Contracts.Literal

/- The public adapters only project the supplied hardware certificate. -/

theorem bits32_roundtrip [hardware : Hardware] (x : Float32) : Float32.ofBits x.toBits = x :=
  hardware.codec.bits32_roundtrip x

theorem bits_roundtrip [hardware : Hardware] (x : Float) : Float.ofBits x.toBits = x :=
  hardware.codec.bits_roundtrip x

theorem bits_ofBits_notNaN [hardware : Hardware] {word : UInt64} (notNaN : (Float.ofBits word).isNaN = false) :
    (Float.ofBits word).toBits = word :=
  hardware.codec.bits_ofBits_notNaN notNaN

theorem finite_bits_inverse [hardware : Hardware] {word : UInt64} (finite : (Float.ofBits word).isFinite = true) :
    (Float.ofBits word).toBits = word :=
  hardware.codec.finite_bits_inverse finite

theorem finite_word32_mask [hardware : Hardware] (word : UInt32) :
    (Float32.ofBits word).isFinite = ((word &&& 0x7f800000) != 0x7f800000) :=
  hardware.codec.finite_word32_mask word

theorem finite_word_mask [hardware : Hardware] (word : UInt64) :
    (Float.ofBits word).isFinite = ((word &&& 0x7ff0000000000000) != 0x7ff0000000000000) :=
  hardware.codec.finite_word_mask word

theorem neg_bits32 [hardware : Hardware] (word : BitVec 32) :
    Float32.ofBits (UInt32.ofBitVec (word ^^^ 0x80000000)) =
      -(Float32.ofBits (UInt32.ofBitVec word)) :=
  hardware.codec.neg_bits32 word

theorem neg_bits64 [hardware : Hardware] (word : BitVec 64) :
    Float.ofBits (UInt64.ofBitVec (word ^^^ 0x8000000000000000)) =
      -(Float.ofBits (UInt64.ofBitVec word)) :=
  hardware.codec.neg_bits64 word

theorem le_refl [hardware : Hardware] {a : Float} (ha : a.isFinite = true) : Float.le a a = true :=
  hardware.order.le_refl ha

theorem le_trans [hardware : Hardware] {a b c : Float} (ab : Float.le a b = true) (bc : Float.le b c = true) :
    Float.le a c = true :=
  hardware.order.le_trans ab bc

theorem le_upper [hardware : Hardware] {a x y : Float} (ha : a.isFinite = false)
    (hx : x.isFinite = true) (hy : y.isFinite = true) (xa : Float.le x a = true) :
    Float.le y a = true :=
  hardware.order.le_upper ha hx hy xa

theorem lower_le [hardware : Hardware] {a x y : Float} (ha : a.isFinite = false)
    (hx : x.isFinite = true) (hy : y.isFinite = true) (ax : Float.le a x = true) :
    Float.le a y = true :=
  hardware.order.lower_le ha hx hy ax

theorem ofInt_not_nan [hardware : Hardware] (z : Int) : (Float.ofInt z).isNaN = false :=
  hardware.sourceInt.ofInt_not_nan z

theorem ofInt_signed64_bits [hardware : Hardware] (z : Int) (lower : -(2 ^ 63) ≤ z) (upper : z < 2 ^ 63) :
    Float.ofInt z = (Int64.ofBitVec (BitVec.ofInt 64 z)).toFloat :=
  hardware.sourceInt.ofInt_signed64_bits z lower upper

theorem ofInt_unsigned64 [hardware : Hardware] (z : Int) (lower : 0 ≤ z) (upper : z < 2 ^ 64) :
    Float.ofInt z = (UInt64.ofNat z.toNat).toFloat :=
  hardware.sourceInt.ofInt_unsigned64 z lower upper

theorem ofInt_jam56 [hardware : Hardware] (z : Int) (large : 2 ^ 55 ≤ z.natAbs) :
    let n := z.natAbs
    let k := n.log2 - 55
    let g := (n >>> k) ||| (if n % 2 ^ k = 0 then 0 else 1)
    let i := min 2047 (k + 1078)
    Float.ofInt z = Float.mul (Int64.ofInt (g : Int)).toFloat
      (Float.ofBits (UInt64.ofNat ((if z < 0 then 2 ^ 63 else 0) + (i - 55) * 2 ^ 52))) :=
  hardware.sourceInt.ofInt_jam56 z large

theorem uint64_toFloat32_high [hardware : Hardware] (word : BitVec 64) (high : word.msb = true) :
    let half := (word >>> 1) ||| (word &&& 1)
    (UInt64.ofBitVec word).toFloat32 =
      Float32.add (Int64.ofBitVec half).toFloat32 (Int64.ofBitVec half).toFloat32 :=
  hardware.unsigned.uint64_toFloat32_high word high

theorem uint64_toFloat_high [hardware : Hardware] (word : BitVec 64) (high : word.msb = true) :
    let half := (word >>> 1) ||| (word &&& 1)
    (UInt64.ofBitVec word).toFloat =
      Float.add (Int64.ofBitVec half).toFloat (Int64.ofBitVec half).toFloat :=
  hardware.unsigned.uint64_toFloat_high word high

theorem float32_cvtt_domain [hardware : Hardware] (word : BitVec 32)
    (small : (word &&& 0x7fffffff).ult 0x5f000000 = true) :
    let x := Float32.ofBits (UInt32.ofBitVec word)
    x.isNaN = false ∧ Float32.lt x Int64.minValue.toFloat32 = false ∧
      Float32.lt x (UInt64.ofNat (2 ^ 63)).toFloat32 = true :=
  hardware.saturatingCast.float32_cvtt_domain word small

theorem float64_cvtt_domain [hardware : Hardware] (word : BitVec 64)
    (small : (word &&& 0x7fffffffffffffff).ult 0x43e0000000000000 = true) :
    let x := Float.ofBits (UInt64.ofBitVec word)
    x.isNaN = false ∧ Float.lt x Int64.minValue.toFloat = false ∧
      Float.lt x (UInt64.ofNat (2 ^ 63)).toFloat = true :=
  hardware.saturatingCast.float64_cvtt_domain word small

theorem float32_toInt64_nan [hardware : Hardware] (word : BitVec 32)
    (nan : (0x7f800000 : BitVec 32).ult (word &&& 0x7fffffff) = true) :
    (Float32.ofBits (UInt32.ofBitVec word)).toInt64.toBitVec = 0 :=
  hardware.saturatingCast.float32_toInt64_nan word nan

theorem float64_toInt64_nan [hardware : Hardware] (word : BitVec 64)
    (nan : (0x7ff0000000000000 : BitVec 64).ult (word &&& 0x7fffffffffffffff) = true) :
    (Float.ofBits (UInt64.ofBitVec word)).toInt64.toBitVec = 0 :=
  hardware.saturatingCast.float64_toInt64_nan word nan

theorem float32_toInt64_overflow [hardware : Hardware] (word : BitVec 32)
    (nan : (0x7f800000 : BitVec 32).ult (word &&& 0x7fffffff) = false)
    (large : (word &&& 0x7fffffff).ult 0x5f000000 = false) :
    (Float32.ofBits (UInt32.ofBitVec word)).toInt64.toBitVec =
      if word.msb then 0x8000000000000000 else 0x7fffffffffffffff :=
  hardware.saturatingCast.float32_toInt64_overflow word nan large

theorem float64_toInt64_overflow [hardware : Hardware] (word : BitVec 64)
    (nan : (0x7ff0000000000000 : BitVec 64).ult (word &&& 0x7fffffffffffffff) = false)
    (large : (word &&& 0x7fffffffffffffff).ult 0x43e0000000000000 = false) :
    (Float.ofBits (UInt64.ofBitVec word)).toInt64.toBitVec =
      if word.msb then 0x8000000000000000 else 0x7fffffffffffffff :=
  hardware.saturatingCast.float64_toInt64_overflow word nan large

theorem float32_toUInt64_high [hardware : Hardware] (word : BitVec 32) (nonnegative : word.msb = false)
    (lower : (word &&& 0x7fffffff).ult 0x5f000000 = false)
    (upper : (word &&& 0x7fffffff).ult 0x5f800000 = true) :
    let x := Float32.ofBits (UInt32.ofBitVec word)
    let reduced := Float32.sub x (Float32.ofBits 0x5f000000)
    x.toUInt64.toBitVec = reduced.toInt64.toBitVec ||| 0x8000000000000000 ∧
      reduced.isNaN = false ∧ Float32.lt reduced Int64.minValue.toFloat32 = false ∧
      Float32.lt reduced (UInt64.ofNat (2 ^ 63)).toFloat32 = true :=
  hardware.saturatingCast.float32_toUInt64_high word nonnegative lower upper

theorem float64_toUInt64_high [hardware : Hardware] (word : BitVec 64) (nonnegative : word.msb = false)
    (lower : (word &&& 0x7fffffffffffffff).ult 0x43e0000000000000 = false)
    (upper : (word &&& 0x7fffffffffffffff).ult 0x43f0000000000000 = true) :
    let x := Float.ofBits (UInt64.ofBitVec word)
    let reduced := Float.sub x (Float.ofBits 0x43e0000000000000)
    x.toUInt64.toBitVec = reduced.toInt64.toBitVec ||| 0x8000000000000000 ∧
      reduced.isNaN = false ∧ Float.lt reduced Int64.minValue.toFloat = false ∧
      Float.lt reduced (UInt64.ofNat (2 ^ 63)).toFloat = true :=
  hardware.saturatingCast.float64_toUInt64_high word nonnegative lower upper

theorem float32_toUInt64_low [hardware : Hardware] (word : BitVec 32) (nonnegative : word.msb = false)
    (small : (word &&& 0x7fffffff).ult 0x5f000000 = true) :
    (Float32.ofBits (UInt32.ofBitVec word)).toUInt64.toBitVec =
      (Float32.ofBits (UInt32.ofBitVec word)).toInt64.toBitVec :=
  hardware.saturatingCast.float32_toUInt64_low word nonnegative small

theorem float64_toUInt64_low [hardware : Hardware] (word : BitVec 64) (nonnegative : word.msb = false)
    (small : (word &&& 0x7fffffffffffffff).ult 0x43e0000000000000 = true) :
    (Float.ofBits (UInt64.ofBitVec word)).toUInt64.toBitVec =
      (Float.ofBits (UInt64.ofBitVec word)).toInt64.toBitVec :=
  hardware.saturatingCast.float64_toUInt64_low word nonnegative small

theorem float32_toUInt64_nan [hardware : Hardware] (word : BitVec 32)
    (nan : (0x7f800000 : BitVec 32).ult (word &&& 0x7fffffff) = true) :
    (Float32.ofBits (UInt32.ofBitVec word)).toUInt64.toBitVec = 0 :=
  hardware.saturatingCast.float32_toUInt64_nan word nan

theorem float64_toUInt64_nan [hardware : Hardware] (word : BitVec 64)
    (nan : (0x7ff0000000000000 : BitVec 64).ult (word &&& 0x7fffffffffffffff) = true) :
    (Float.ofBits (UInt64.ofBitVec word)).toUInt64.toBitVec = 0 :=
  hardware.saturatingCast.float64_toUInt64_nan word nan

theorem float32_toUInt64_negative [hardware : Hardware] (word : BitVec 32) (negative : word.msb = true) :
    (Float32.ofBits (UInt32.ofBitVec word)).toUInt64.toBitVec = 0 :=
  hardware.saturatingCast.float32_toUInt64_negative word negative

theorem float64_toUInt64_negative [hardware : Hardware] (word : BitVec 64) (negative : word.msb = true) :
    (Float.ofBits (UInt64.ofBitVec word)).toUInt64.toBitVec = 0 :=
  hardware.saturatingCast.float64_toUInt64_negative word negative

theorem float32_toUInt64_overflow [hardware : Hardware] (word : BitVec 32) (nonnegative : word.msb = false)
    (nan : (0x7f800000 : BitVec 32).ult (word &&& 0x7fffffff) = false)
    (large : (word &&& 0x7fffffff).ult 0x5f800000 = false) :
    (Float32.ofBits (UInt32.ofBitVec word)).toUInt64.toBitVec = -1#64 :=
  hardware.saturatingCast.float32_toUInt64_overflow word nonnegative nan large

theorem float64_toUInt64_overflow [hardware : Hardware] (word : BitVec 64) (nonnegative : word.msb = false)
    (nan : (0x7ff0000000000000 : BitVec 64).ult (word &&& 0x7fffffffffffffff) = false)
    (large : (word &&& 0x7fffffffffffffff).ult 0x43f0000000000000 = false) :
    (Float.ofBits (UInt64.ofBitVec word)).toUInt64.toBitVec = -1#64 :=
  hardware.saturatingCast.float64_toUInt64_overflow word nonnegative nan large

theorem canonLiteral_integer [hardware : Hardware] (z : Int) : canonLiteral (z, 1) = Float.ofInt z :=
  hardware.literal.canonLiteral_integer z

theorem canonLiteral_subnormal_one [hardware : Hardware] : (canonLiteral (1, 2 ^ 1074)).toBits = 1 :=
  hardware.literal.canonLiteral_subnormal_one

theorem canonLiteral_subnormal_two [hardware : Hardware] : (canonLiteral (2, 2 ^ 1074)).toBits = 2 :=
  hardware.literal.canonLiteral_subnormal_two

theorem canonLiteral_subnormal_negative [hardware : Hardware] :
    (canonLiteral (-1, 2 ^ 1074)).toBits = 0x8000000000000001 ∧
      (canonLiteral (1, -(2 ^ 1074))).toBits = 0x8000000000000001 ∧
      (canonLiteral (-1, -(2 ^ 1074))).toBits = 1 :=
  hardware.literal.canonLiteral_subnormal_negative

end RootNativeFloat
