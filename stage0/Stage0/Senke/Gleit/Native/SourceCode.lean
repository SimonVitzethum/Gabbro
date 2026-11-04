/- Source integer conversion uses the existing complete integer normalization. -/
module
public import Stage0.Senke.Gleit.Native.Conversion
public import Stage0.Senke.Gleit.Native.Choice
public import Stage0.Senke.Ausdruck.Gleit.Wide.Values
public import Stage0.Senke.Ausdruck.Gleit.Grenze
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable {D : Deklaration}

/-- Preserve the complete source integer. The existing typed search and sticky
    normalization supply native CVT and an exact power-of-two multiplier; no
    source value is truncated to its first machine word. -/
def wideComputedFloatOfE (L : Lay D) {Γ : Ctx} {Λ : List (Res D)}
    {lo hi : Int} (e : Expr D Γ Λ (.int lo hi)) (d : Nat) (reserved : Nat := 0) :
    Option (List II × Nat) :=
  let w := WideFloat.width lo hi
  let field := fun {a b : Int} (t : Expr D Γ Λ (.int a b)) j => lowE L t j reserved
  let flag := fun j => lowE L (.lt (WideFloat.magnitude w e) (.lit (2 ^ 55))) j reserved
  let sign := fun j => lowE L (.lt e (.lit 0)) j reserved
  let small := fun j => nativeSignedFloatL j (field (WideFloat.small e))
  let large := fun j => nativeFPWordL (.mul .f64) j
    (nativeSignedFloatL j (field (WideFloat.guard w e)))
    (nativeFloatScaleL (j + 1) sign (field (WideFloat.index w e)))
  routineChooseL d flag small large

/-- The signed-word fast path and complete-magnitude path retain the original
    interval gate. Source float values use native binary64, as `Ty.fl` requires. -/
def computedFloatOfE (L : Lay D) {Γ : Ctx} {Λ : List (Res D)}
    {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (d : Nat) (reserved : Nat := 0) : Option (List II × Nat) :=
  if -2 ^ 63 ≤ lo ∧ hi < 2 ^ 63 then
    nativeSignedFloatL d (fun j => lowE L e j reserved)
  else wideComputedFloatOfE L e d reserved

theorem wideComputedFloatOfE_top {L : Lay D} {Γ : Ctx} {Λ : List (Res D)}
    {lo hi : Int} {e : Expr D Γ Λ (.int lo hi)} {d reserved top : Nat} {c : List II}
    (h : wideComputedFloatOfE L e d reserved = some (c, top)) : d < top := by
  simp only [wideComputedFloatOfE, routineChooseL, bind, Option.bind_eq_some_iff,
    pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨cc, tt⟩, _, _, rfl⟩ := h
  omega

theorem computedFloatOfE_bounds {L : Lay D} {Γ : Ctx} {Λ : List (Res D)}
    {lo hi : Int} {e : Expr D Γ Λ (.int lo hi)}
    {d reserved top : Nat} {code : List II}
    (hc : computedFloatOfE L e d reserved = some (code, top)) : d < top := by
  unfold computedFloatOfE at hc
  split at hc
  · have bound := nativeFPWordL_bounds hc
    omega
  · exact wideComputedFloatOfE_top hc

end Gabbro.Stage0.Senke
