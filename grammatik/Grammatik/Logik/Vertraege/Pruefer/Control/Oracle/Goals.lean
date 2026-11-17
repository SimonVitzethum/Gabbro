module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Oracle.Result

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Symbolic

open Invarianten.Frag.Symbolic

variable {D : Deklaration} {program : Programm D} {S : SperrInv D} {V : Vertrag D}

def Goals.shrinkResult {context : Context A next}
    (goals : Goals (program := program) (S := S) context V Γ) :
    (result : Option Ty) → Goals (program := program) (S := S) context V (ErgCtx Γ result)
  | none => goals
  | some kind => goals.shrink kind

theorem Goals.holds_shrinkResult {context : Context A next} {l : Bool}
    (goals : Goals (program := program) (S := S) context V Γ) (result : Option Ty)
    (item : A) (runtime : Invarianten.VC.Runtime program (fun _ => []) S) (allowed : Logik D → Prop)
    (outcome : Ausgang V l (ErgCtx Γ result)) :
    (goals.shrinkResult result).holds item runtime allowed outcome ↔
      goals.holds item runtime allowed (Ausgang.weiterOpt result outcome) := by
  cases result with
  | none => rfl
  | some kind => exact goals.holds_shrink kind item runtime allowed outcome

theorem Goals.endHolds_shrinkResult {context : Context A next} {l : Bool}
    (goals : Goals (program := program) (S := S) context V Γ) (result : Option Ty)
    (item : A) (runtime : Invarianten.VC.Runtime program (fun _ => []) S) (allowed : Logik D → Prop)
    (outcome : EndAusgang V l (ErgCtx Γ result)) :
    (goals.shrinkResult result).endHolds item runtime allowed outcome ↔
      goals.endHolds item runtime allowed (EndAusgang.weiterOpt result outcome) := by
  cases result with
  | none => rfl
  | some kind => exact goals.endHolds_shrink kind item runtime allowed outcome

theorem Goals.endHolds_to_statement {context : Context A next} {l : Bool}
    (goals : Goals (program := program) (S := S) context V Γ) (item : A)
    (runtime : Invarianten.VC.Runtime program (fun _ => []) S) (allowed : Logik D → Prop)
    (outcome : EndAusgang V l Γ) :
    goals.endHolds item runtime allowed outcome ↔ goals.holds item runtime allowed outcome.zuAusgang := by
  cases outcome <;> rfl

end Gabbro.Grammatik.Vertraege.Pruefer.Symbolic
