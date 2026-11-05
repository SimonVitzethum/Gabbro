/- Compile-time literal input to the opaque native conversion boundary. -/
module
public import NativeFloat.Primitives
public section

namespace RootNativeFloat

/-- Serialize a source fraction for the toolchain's native decimal conversion.
    The integer prefix extends beyond every binary64 midpoint's terminating
    decimal expansion; a final nonzero digit retains a nonzero remainder.
    This is compile-time input preparation, with no floating evaluator or packer.
    Its numerical meaning is supplied by the named literal hardware contract. -/
opaque canonLiteral (q : Int × Int) : Float :=
  if q.2 = 1 then Float.hwOfInt q.1
  else if q.2 = 0 then Float.hwDiv (Float.hwOfInt q.1) (Float.hwOfInt 0)
  else
    let scaled := q.1.natAbs * 10 ^ 1076
    let divisor := q.2.natAbs
    let digits := (scaled / divisor) * 10 + (if scaled % divisor = 0 then 0 else 1)
    let value := Float.hwOfScientific digits true 1077
    if (q.1 < 0) != (q.2 < 0) then Float.hwNeg value else value

end RootNativeFloat
