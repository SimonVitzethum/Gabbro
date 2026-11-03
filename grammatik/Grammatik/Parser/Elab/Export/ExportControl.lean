module
public import Grammatik.Parser.Elab.UebersetzeAllg2
@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg2
open Uebersetze UebersetzeAllg

/-- The ordinary call's typed failure and success continuations, retaining argument effects,
    conformance, reason type and the exact post-call resource index (C16: both live at
    the call transformer, no cast). -/
def nestedElse {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx)
    (Λ : List (Res (declOf u))) (k : RufKopf u caller Γ Λ) (τ : Ty)
    (he : (declOf u).erg k.callee = some τ) (hr : 0 < (declOf u).gruende k.callee)
    (err : Endblock (declOf u) (verOf u caller) l (Ty.why ((declOf u).gruende k.callee) :: Γ) (nach (declOf u) k.callee Λ))
    (body : Endblock (declOf u) (verOf u caller) l (τ :: Γ) (nach (declOf u) k.callee Λ)) :
    Endblock (declOf u) (verOf u caller) l Γ Λ :=
  .bindCallElse k.callee k.args he k.hp hr err body

/-- The indirect call's typed failure and success continuations («C07»): like `nestedElse`, over the
    pointer type's signature with its reason channel; the pointer is evaluated once by the caller. -/
def nestedElseN {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx)
    (Λ : List (Res (declOf u))) (m : Nat) (v : Var Γ (Ty.fnptr m))
    (k : RufKopfN u caller Γ Λ m) (τ : Ty)
    (he : ((declOf u).sigNr m).erg = some τ) (hr : 0 < ((declOf u).sigNr m).gruende)
    (err : Endblock (declOf u) (verOf u caller) l (Ty.why (((declOf u).sigNr m).gruende) :: Γ) (nachSig (declOf u) ((declOf u).sigNr m) Λ))
    (body : Endblock (declOf u) (verOf u caller) l (τ :: Γ) (nachSig (declOf u) ((declOf u).sigNr m) Λ)) :
    Endblock (declOf u) (verOf u caller) l Γ Λ :=
  .bindCallIndElse (n := m) (Expr.var v) k.args he k.hp hr err body

end Gabbro.Grammatik.Parser.UebersetzeAllg2
