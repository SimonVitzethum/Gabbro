/- Compile-time literal input to the opaque native conversion boundary. -/
module
public import NativeFloat.Primitives
public section

namespace RootNativeFloat

/-- Integer exponent of the source ratio. This prepares native operands without
    converting either unbounded input to a float first. -/
private def ratioExponent (numerator denominator : Nat) : Int :=
  let initial := (numerator.log2 : Int) - (denominator.log2 : Int)
  let below := if initial < 0 then
      decide (numerator <<< (-initial).toNat < denominator)
    else decide (numerator < denominator <<< initial.toNat)
  if below then initial - 1 else initial

/-- Prepare a bounded integer significand and exact power-of-two operands. All
    floating conversion and rounding is performed by native CPU operations.
    The split scale keeps a subnormal scale operand from underflowing to zero.
    Its numerical meaning is an explicit literal hardware contract, not a kernel
    execution of a floating-point model. -/
opaque canonLiteral (q : Int × Int) : Float :=
  if q.2 = 1 then Float.hwOfInt q.1
  else if q.2 = 0 then Float.hwDiv (Float.hwOfInt q.1) (Float.hwOfInt 0)
  else
    let negative := decide (q.1 < 0) != decide (q.2 < 0)
    if q.1 = 0 then Float.hwOfBits (if negative then 0x8000000000000000 else 0)
    else
      let numerator := q.1.natAbs
      let denominator := q.2.natAbs
      let exponent := ratioExponent numerator denominator
      let value :=
        if 1023 < exponent then Float.hwOfBits 0x7ff0000000000000
        else if exponent < -1075 then Float.hwOfBits 0
        else
          let precision := min 53 (max 1 (exponent + 1075).toNat)
          let shift := exponent - ((precision + 1 : Nat) : Int)
          let scaled := if shift < 0 then numerator <<< (-shift).toNat else numerator
          let divisor := if shift < 0 then denominator else denominator <<< shift.toNat
          let retained := (scaled / divisor) ||| (if scaled % divisor = 0 then 0 else 1)
          let converted := (Int64.ofInt (retained : Int)).hwToFloat
          if -1022 ≤ shift then
            Float.hwMul converted
              (Float.hwOfBits (UInt64.ofNat ((shift + 1023).toNat * 2 ^ 52)))
          else
            Float.hwMul
              (Float.hwMul converted
                (Float.hwOfBits (UInt64.ofNat ((shift + 2045).toNat * 2 ^ 52))))
              (Float.hwOfBits 0x0010000000000000)
      if negative then Float.hwNeg value else value

end RootNativeFloat
