module

public import Init.Data.Float
public import Init.Data.SInt.Float
public import Init.Data.SInt.Float32

public section

/-! Logical floating operations are opaque to the proof kernel and independent of
    the target ISA. Their executable bodies delegate to toolchain operations for
    compiler input preparation and probes; they are not the execution backend of
    a compiled Gabbro program. Each target implements the logical operations with
    its own instructions and profile. Numerical correspondence belongs to the
    explicitly supplied `RootNativeFloat.Hardware` contract. No theorem may unfold
    a toolchain floating model to establish that correspondence. -/

/-- Integer-only preparation for a native conversion and power-of-two scaling.
    No floating rounding, significand representation or floating evaluator is
    implemented here. The hardware contract specifies the numerical result. -/
private def integerScaleWords (value : Int) (kept bias maxIndex fraction signBit : Nat) :
    Int × Nat :=
  let magnitude := value.natAbs
  let shift := magnitude.log2 - kept
  let retained := (magnitude >>> shift) ||| (if magnitude % 2 ^ shift = 0 then 0 else 1)
  let index := min maxIndex (shift + kept + bias)
  ((retained : Int), (if value < 0 then 2 ^ signBit else 0) + (index - kept) * 2 ^ fraction)

namespace Int64

opaque hwToFloat (a : Int64) : Float := Int64.toFloat a
opaque hwToFloat32 (a : Int64) : Float32 := Int64.toFloat32 a

end Int64

namespace UInt64

opaque hwToFloat (a : UInt64) : Float := UInt64.toFloat a
opaque hwToFloat32 (a : UInt64) : Float32 := UInt64.toFloat32 a

end UInt64

namespace Float

opaque hwAdd (a b : Float) : Float := Float.add a b
opaque hwSub (a b : Float) : Float := Float.sub a b
opaque hwMul (a b : Float) : Float := Float.mul a b
opaque hwDiv (a b : Float) : Float := Float.div a b
opaque hwNeg (a : Float) : Float := Float.neg a
opaque hwBEq (a b : Float) : Bool := Float.beq a b
opaque hwLt (a b : Float) : Bool := Float.lt a b
opaque hwLe (a b : Float) : Bool := Float.le a b
opaque hwIsFinite (a : Float) : Bool := Float.isFinite a
opaque hwIsNaN (a : Float) : Bool := Float.isNaN a
opaque hwOfBits (a : UInt64) : Float := Float.ofBits a
opaque hwToBits (a : Float) : UInt64 := Float.toBits a
/-- Native machine-word conversion, or integer normalization followed by native
    conversion and multiplication. Arbitrary source integers retain their domain. -/
opaque hwOfInt (a : Int) : Float :=
  if -(2 ^ 63) ≤ a ∧ a < 2 ^ 63 then (Int64.ofInt a).hwToFloat
  else if 0 ≤ a ∧ a < 2 ^ 64 then (UInt64.ofNat a.toNat).hwToFloat
  else
    let prepared := integerScaleWords a 55 1023 2047 52 63
    hwMul (Int64.ofInt prepared.1).hwToFloat (hwOfBits (UInt64.ofNat prepared.2))
opaque hwOfNat (a : Nat) : Float := hwOfInt (a : Int)
opaque hwToInt64 (a : Float) : Int64 := Float.toInt64 a
opaque hwToUInt64 (a : Float) : UInt64 := Float.toUInt64 a
opaque hwToFloat32 (a : Float) : Float32 := Float.toFloat32 a

end Float

namespace Float32

opaque hwAdd (a b : Float32) : Float32 := Float32.add a b
opaque hwSub (a b : Float32) : Float32 := Float32.sub a b
opaque hwMul (a b : Float32) : Float32 := Float32.mul a b
opaque hwDiv (a b : Float32) : Float32 := Float32.div a b
opaque hwNeg (a : Float32) : Float32 := Float32.neg a
opaque hwBEq (a b : Float32) : Bool := Float32.beq a b
opaque hwLt (a b : Float32) : Bool := Float32.lt a b
opaque hwLe (a b : Float32) : Bool := Float32.le a b
opaque hwIsFinite (a : Float32) : Bool := Float32.isFinite a
opaque hwIsNaN (a : Float32) : Bool := Float32.isNaN a
opaque hwOfBits (a : UInt32) : Float32 := Float32.ofBits a
opaque hwToBits (a : Float32) : UInt32 := Float32.toBits a
opaque hwOfInt (a : Int) : Float32 :=
  if -(2 ^ 63) ≤ a ∧ a < 2 ^ 63 then (Int64.ofInt a).hwToFloat32
  else if 0 ≤ a ∧ a < 2 ^ 64 then (UInt64.ofNat a.toNat).hwToFloat32
  else
    let prepared := integerScaleWords a 26 127 255 23 31
    hwMul (Int64.ofInt prepared.1).hwToFloat32 (hwOfBits (UInt32.ofNat prepared.2))
opaque hwOfNat (a : Nat) : Float32 := hwOfInt (a : Int)
opaque hwToInt64 (a : Float32) : Int64 := Float32.toInt64 a
opaque hwToUInt64 (a : Float32) : UInt64 := Float32.toUInt64 a
opaque hwToFloat (a : Float32) : Float := Float32.toFloat a

end Float32
