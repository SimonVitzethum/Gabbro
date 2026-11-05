/- Literal correspondence is separate from the source type definitions. -/
module
public import Grammatik.Kern.Syntax.Typen.Teil1
public import NativeFloat.Hardware
@[expose] public section

namespace Gabbro.Grammatik

theorem bruch_integer [RootNativeFloat.Hardware] (z : Int) : bruch (z, 1) = Float.hwOfInt z :=
  RootNativeFloat.canonLiteral_integer z

end Gabbro.Grammatik
