/- Literal correspondence is separate from the source type definitions. -/
module
public import Grammatik.Kern.Syntax.Typen.Teil1
public import NativeFloat.LiteralFacts
@[expose] public section

namespace Gabbro.Grammatik

theorem bruch_integer (z : Int) : bruch (z, 1) = Float.ofInt z :=
  RootNativeFloat.canonLiteral_integer z

end Gabbro.Grammatik
