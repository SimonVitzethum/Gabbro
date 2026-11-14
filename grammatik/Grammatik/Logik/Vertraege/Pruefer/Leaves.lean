module

public import Grammatik.Logik.Vertraege.Pruefer.Control

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.VC

variable {D : Deklaration} {V : Vertrag D} {S : SperrInv D} {program : Programm D}
variable (policy : CallPolicy program)

/-- A return is checked against its actual typed result. Complete finite
    domains are budgeted; an oversized range is refused, never sampled. -/
def returnCondition (budget : Nat) {Γ : Ctx} {Λ : List (Res D)}
    (expression : ErgExpr D Γ Λ V.erg) (locals : Env D Γ) (goals : Goals D V Γ) :
    Except Frag.Refusal (Condition (fun (_ : Runtime program (fun _ => []) S) world =>
      denotes (goals.returned (evalErg world expression world locals)) world)) :=
  match expression with
  | .empty => requireCondition (goals.returned ())
  | .val expression =>
      localSelect budget expression locals
        (fun value _ world => denotes (goals.returned value) world)
        (fun value => requireCondition (goals.returned value))

/-- Scalar updates reuse P20's substitution; the post is stronger at logic
    stops and value returns. Unsupported leaves have no accepting fallback. -/
def leafCondition (budget : Nat) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (code : Stmt D V l Γ Λ Λ') (locals : Env D Γ) (goals : Goals D V Γ) :
    Except Frag.Refusal (StatementCondition (S := S) policy code locals goals) :=
  match code with
  | .assignGlob name expression _ _ => do
      match h : goals.normal locals with
      | .error cause => .error cause
      | .ok normal => do
          let pre ← scalarWP expression locals (.glob name) normal
          return {
              formula := pre.formula
              sound := fun runtime world valid allowed safe => by
                unfold Runtime.wpS
                simp only [execStmtH, Goals.holds, h, denotes]
                rw [assignment_schreibGlob]
                apply pre.sound
                rw [assignment_lese]
                exact valid }
  | .assignSlot table field index expression _ _ => do
      match h : goals.normal locals with
      | .error cause => .error cause
      | .ok normal => do
          let encodedIndex ← translate index locals
          let offset ← encodedIndex.constantIndex
          let pre ← scalarWP expression locals (.slot table field offset.val) normal
          return {
              formula := pre.formula
              sound := fun runtime world valid allowed safe => by
                unfold Runtime.wpS
                simp only [execStmtH, Goals.holds, h, denotes]
                rw [assignment_schreibSlot, offset.property]
                apply pre.sound
                rw [assignment_lese]
                exact valid }
  | .assignVar name expression => do
      let pre ← localSelect budget expression locals
        (fun value _ world => denotes (goals.normal (locals.set name value)) world)
        (fun value => requireCondition (goals.normal (locals.set name value)))
      return (pre.read Λ expression.orte).map (fun _ _ valid _ _ => valid)
  | .ret expression _ => do
      let pre ← returnCondition (S := S) budget expression locals goals
      return (pre.read Λ expression.orte).map (fun _ _ valid _ _ => valid)
  | .retWhy _ _ => .ok
      { formula := goals.reason
        sound := fun _ _ valid _ _ => valid }
  | .leave _ => do
      let pre ← requireCondition (program := program) (checked := fun _ => []) (S := S) (goals.escape locals)
      return pre.map (fun _ _ valid _ _ => valid)
  | .next _ => do
      let pre ← requireCondition (program := program) (checked := fun _ => []) (S := S) (goals.again locals)
      return pre.map (fun _ _ valid _ _ => valid)
  | _ => .error (.unsupported "contract statement is outside the checked scalar/control fragment")

end Gabbro.Grammatik.Vertraege.Pruefer
