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

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

/-- Sequential fields reserve their complete canonical span. The caller supplies
    the expression bound, independently of the expression recursion scheme. -/
theorem prodArgsL_top {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (lower : {τ : Ty} → Expr D Γ Λ τ → Nat → Option (List II × Nat))
    (fieldTop : ∀ {τ} (e : Expr D Γ Λ τ) d c top,
      lower e d = some (c, top) → d + valueWords τ ≤ top) :
    ∀ {fs} (args : Args D Γ Λ fs) d c top,
      prodArgsL lower args d = some (c, top) → d + productWords fs ≤ top
  | _, .nil, d, c, top, h => by
    simp only [prodArgsL, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [productWords]
  | _, @Args.cons _ _ _ τ fs e rest, d, c, top, h => by
    simp only [prodArgsL, bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨ce, te⟩, he, ⟨cr, tr⟩, hr, rfl, rfl⟩ := h
    have headBound := fieldTop e d ce te he
    have tailBound := prodArgsL_top lower fieldTop rest (d + valueWords τ) cr tr hr
    simp only [productWords]
    have upper := Nat.le_max_right te tr
    omega

end Gabbro.Stage0.Senke
