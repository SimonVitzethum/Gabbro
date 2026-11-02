/- Sequential product-field lowering, parameterized by expression lowering. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Hilfen
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

/-- Empty argument lists emit no padding: the enclosing product owns its marker.
    Parameterization keeps this traversal independent of expression recursion. -/
def prodArgsL {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (lower : {τ : Ty} → Expr D Γ Λ τ → Nat → Option (List II × Nat)) :
    {fs : List Ty} → Args D Γ Λ fs → Nat → Option (List II × Nat)
  | _, .nil, d => some ([], d)
  | _, @Args.cons _ _ _ τ _ e rest, d => do
    let head ← lower e d
    let tail ← prodArgsL lower rest (d + valueWords τ)
    pure (head.1 ++ tail.1, max head.2 tail.2)

end Gabbro.Stage0.Senke
