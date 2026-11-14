module

public import Grammatik.Logik.Invarianten.VC.Domain

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.VC

open Frag Elim Elim.Korrekt Modell

variable {D : Deklaration} {V : Vertrag D} {S : SperrInv D}
variable {program : Programm D} {checked : D.Fn → List D.Inv}

/-- A refused continuation is false, never an unchecked default. -/
def requireCondition (result : Except Refusal (QF (Observation D))) :
    Except Refusal (Condition (fun (_ : Runtime program checked S) world => denotes result world)) :=
  match result with
  | .error cause => .error cause
  | .ok formula => .ok
      { formula := formula
        sound := fun _ _ valid => valid }

def generatedFormula {target : Runtime program checked S → World D → Prop}
    (result : Except Refusal (Condition target)) : Except Refusal (QF (Observation D)) :=
  result.map (fun pre => pre.formula)

theorem generated_sound {target : Runtime program checked S → World D → Prop}
    (result : Except Refusal (Condition target)) (runtime : Runtime program checked S)
    (world : World D) (valid : denotes (generatedFormula result) world) : target runtime world := by
  cases h : result with
  | error cause => simp only [generatedFormula, h, Except.map, denotes] at valid
  | ok pre =>
      apply pre.sound runtime world
      simpa only [generatedFormula, h, Except.map, denotes] using valid

/-- A bound call result receives its own range-constrained observation. The
    callee's output is otherwise arbitrary within the complete decoded domain. -/
def Condition.freshResult {target : Runtime program checked S → World D → Prop}
    (τ : Ty) (value : Wert D τ) (pre : Condition target) : Condition target where
  formula := freshImplication τ value .tru pre.formula
  sound := fun runtime world valid => pre.sound runtime world
    (freshImplication_sound τ value .tru pre.formula (assignment world) valid trivial)

/-- Bindings shrink only the local environment. Returns retain their final
    invariant, independent of the initializer and unreachable continuation. -/
def bindingCondition {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (budget : Nat) (expression : Expr D Γ Λ τ)
    (rest : Block D V l (τ :: Γ) Λ Λ') (locals : Env D Γ) (goals : Goals D Γ)
    (compile : ∀ next, Except Refusal (BlockCondition program checked S rest next (goals.shrink τ))) :
    Except Refusal (BlockCondition program checked S (.bind expression rest) locals goals) := do
  let selected ← localSelect budget expression locals
    (fun value runtime world => runtime.wpB rest
      (goals.shrink τ).holds world (.cons value locals))
    (fun value => compile (.cons value locals))
  return (selected.read Λ expression.orte).map (fun runtime world ready => by
    unfold Runtime.wpB at ready ⊢
    simp only [execBlockH]
    exact (goals.holds_shrink τ _).mp ready)

/-- Mutable assignment selects a new typed value and passes the updated
    environment to the actual remaining block. It never asserts locals stayed equal. -/
def mutableCondition {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (budget : Nat) (name : Var Γ τ) (expression : Expr D Γ Λ τ)
    (locals : Env D Γ) (goals : Goals D Γ) :
    Except Refusal (StatementCondition program checked S (.assignVar name expression) locals goals) := do
  let selected ← localSelect budget expression locals
    (fun value _ world => denotes (goals.normal (locals.set name value)) world)
    (fun value => do
      let pre ← requireCondition (program := program) (checked := checked)
        (goals.normal (locals.set name value))
      return pre.map (fun _ _ ready => ready))
  return (selected.read Λ expression.orte).map (fun _ _ ready => ready)

/-- Bound call results contribute their full decoded type range. Checked callee
    invariants and the frame are the only restrictions on the post-call world. -/
def boundCallCondition {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (budget : Nat) (f : D.Fn) (args : Args D Γ Λ (D.params f))
    (he : D.erg f = some τ) (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0)
    (rest : Block D V l (τ :: Γ) (nach D f Λ) Λ') (locals : Env D Γ) (goals : Goals D Γ)
    (compile : ∀ next, Except Refusal (BlockCondition program checked S rest next (goals.shrink τ))) :
    Except Refusal (BlockCondition program checked S (.bindCall f args he hp hr rest) locals goals) := do
  let domain ← localDomain (D := D) budget τ
  let tails ← allConditions domain.values
    (fun value runtime world => runtime.wpB rest
      (goals.shrink τ).holds world (.cons value locals))
    (fun value => do
      let pre ← compile (.cons value locals)
      return pre.freshResult τ value)
  let facts ← invariantFormula program (checked f)
  return
    { formula := callWP f facts.formula tails.formula
      sound := fun runtime world valid => by
        let read := world.lese Λ args.orte
        let actual := evalArgs read args read locals
        have validRead : (callWP f facts.formula tails.formula).denote (assignment read) := by
          rw [assignment_lese]
          exact valid
        unfold Runtime.wpB
        dsimp only [execBlockH]
        cases reply : runtime.calls f read actual with
        | ok next value =>
            have frame := runtime.evidence.frame f read actual next value reply
            have known := (facts.correct next).mpr
              (runtime.evidence.invariants f read actual next value reply)
            have ready := callWP_sound f facts.formula tails.formula read next validRead frame known
            have result := tails.sound runtime next ready (ergWert he value) (domain.complete _)
            exact (goals.holds_shrink τ _).mp result
        | why next reason => exact (Fin.cast hr reason).elim0
        | logik error => trivial
        | hardware error => trivial }

end Gabbro.Grammatik.Invarianten.VC
