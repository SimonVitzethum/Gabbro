module
public import Stage0.Senke.Ausdruck
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable {D : Deklaration}

/-- Specialize the common expression traversal to cached frame lookup. Tagged
    payloads and product construction keep their canonical fallback traversal. -/
@[inline] def lowEFast (L : Lay D) {Λ : List (Res D)} {Γ : Ctx} {τ : Ty}
    (e : Expr D Γ Λ τ) (d : Nat) (reserved : Nat := 0)
    (currentOld : Bool := true) (frame : FrameCache Γ) : Option (List II × Nat) :=
  lowEWith cachedLookup L e d reserved currentOld frame

/-- The cache changes neither instructions, scratch ceilings nor refusal. This
    proof uses lookup equality, without unfolding any recursive definition. -/
theorem lowEFast_eq (L : Lay D) {Λ : List (Res D)} {Γ : Ctx} {τ : Ty}
    (e : Expr D Γ Λ τ) (d reserved : Nat) (currentOld : Bool) (frame : FrameCache Γ) :
    lowEFast L e d reserved currentOld frame = lowE L e d reserved currentOld := by
  unfold lowEFast lowE
  rw [cachedLookup_eq, FrameCache.eq_ofCtx frame]

end Gabbro.Stage0.Senke
