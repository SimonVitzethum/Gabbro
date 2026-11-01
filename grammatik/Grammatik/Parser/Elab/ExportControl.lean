import Grammatik.Parser.Elab.UebersetzeAllg2

namespace Gabbro.Grammatik.Parser.UebersetzeAllg2
open Uebersetze UebersetzeAllg

/-- The ordinary call's typed failure and success continuations, retaining argument effects,
    conformance, reason type and the exact post-call resource index. -/
def nestedElse {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx)
    (Λ : List (Res (declOf u))) (k : RufKopf u caller Γ Λ) (τ : Ty)
    (he : (declOf u).erg k.callee = some τ) (hr : 0 < (declOf u).gruende k.callee)
    (err : Endblock (declOf u) (verOf u caller) l (Ty.why ((declOf u).gruende k.callee) :: Γ) Λ)
    (body : Endblock (declOf u) (verOf u caller) l (τ :: Γ) Λ) :
    Endblock (declOf u) (verOf u caller) l Γ Λ :=
  .bindCallElse k.callee k.args he k.hp hr
    (by rw [nach_eq u k.callee Λ]; exact err)
    (by rw [nach_eq u k.callee Λ]; exact body)

end Gabbro.Grammatik.Parser.UebersetzeAllg2
