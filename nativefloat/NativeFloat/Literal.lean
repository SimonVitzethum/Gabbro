/- Compile-time literal conversion without intermediate integer rounding. -/
module
public import Init.Data.Float
@[expose] public section

namespace RootNativeFloat
open Float.Model
open Float.Model.UnpackedFloat

/-- Round a source fraction only after division of its exact integer
    mantissas. Runtime arithmetic continues to use the native primitives. -/
def canonLiteral (q : Int × Int) : Float :=
  let exact (z : Int) : UnpackedFloat :=
    if h : z = 0 then .zero .positive
    else .finite (if z < 0 then .negative else .positive) z.natAbs 0 (Int.natAbs_pos.mpr h)
  Float.ofModel (Float.Model.pack (UnpackedFloat.div Format.binary64 (exact q.1) (exact q.2)))

end RootNativeFloat
