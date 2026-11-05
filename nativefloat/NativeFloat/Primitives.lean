module

public import Init.Data.Float
public import Init.Data.SInt.Float
public import Init.Data.SInt.Float32

public section

/-! Native floating operations are opaque to the proof kernel. Their executable
    bodies delegate to the toolchain primitives; numerical correspondence belongs
    to the explicitly supplied `RootNativeFloat.Hardware` contract. No theorem may
    unfold a toolchain floating model to establish that correspondence. -/

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
opaque hwOfInt (a : Int) : Float := Float.ofInt a
opaque hwToInt64 (a : Float) : Int64 := Float.toInt64 a
opaque hwToUInt64 (a : Float) : UInt64 := Float.toUInt64 a
opaque hwToFloat32 (a : Float) : Float32 := Float.toFloat32 a
opaque hwOfScientific (mantissa : Nat) (negativeExponent : Bool) (exponent : Nat) : Float :=
  Float.ofScientific mantissa negativeExponent exponent

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
opaque hwToInt64 (a : Float32) : Int64 := Float32.toInt64 a
opaque hwToUInt64 (a : Float32) : UInt64 := Float32.toUInt64 a
opaque hwToFloat (a : Float32) : Float := Float32.toFloat a

end Float32

namespace Int64

opaque hwToFloat (a : Int64) : Float := Int64.toFloat a
opaque hwToFloat32 (a : Int64) : Float32 := Int64.toFloat32 a

end Int64

namespace UInt64

opaque hwToFloat (a : UInt64) : Float := UInt64.toFloat a
opaque hwToFloat32 (a : UInt64) : Float32 := UInt64.toFloat32 a

end UInt64
