module

public import Gabbro.Sicherheit.Anweisung.Teil1
public import Gabbro.Coverage.Teil3

@[expose] public section

namespace Gabbro.Sicherheit
open Gabbro.Body

/-- A mixed, nested record in both the world and the local scope. -/
def recordValues : List Value := [.int 7, .record [.bool true]]
def recordShapes : List Shape := [.intIn 0 10, .record [.bool]]
def recordTyping : Typing := fun _ => some (.record recordShapes)
def recordScope : Lokal := fun _ => some (.record recordShapes)

def recordD : Deklaration where
  slot := fun _ _ => some (.record recordShapes)
  count := fun _ => 1
  feld := fun _ _ => some (.record recordShapes)
  global := fun _ => some (.record recordShapes)

def recordState : State where
  world := fun _ => .record recordValues
  local' := fun _ => .record recordValues

def recordEnv : Env := fun _ t => (t, some (.record recordValues))

theorem recordDeclared : Deklariert recordD recordTyping :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem recordWF : WF recordTyping recordState.world := by
  intro p sh h
  cases h
  rfl

theorem recordWFL : WFL recordScope recordState.local' := by
  intro n sh h
  cases h
  rfl

theorem recordKetten : KettenWohlgeformt recordD recordState.world := by
  intro c via k h
  cases h

theorem literalShape_sicher_zeuge :
    (Value.record recordValues).hasShape
      (.record [.intIn 7 7, .record [.bool]]) = true :=
  literalShape_sicher _ _ (by decide)

theorem literalFieldsShape_sicher_zeuge :
    recordValues.length = [Shape.intIn 7 7, .record [.bool]].length ∧
      Value.fieldsHaveShape recordValues [.intIn 7 7, .record [.bool]] = true :=
  literalFieldsShape_sicher _ _ (by decide)

theorem fieldsHaveShape_get_zeuge :
    ∃ v, recordValues[1]? = some v ∧ v.hasShape (.record [.bool]) = true :=
  fieldsHaveShape_get recordValues recordShapes 1 (.record [.bool]) (by decide) (by decide)

theorem fieldsHaveShape_setBoth_zeuge :
    Value.fieldsHaveShape (recordValues.set 1 (.int 12))
      (recordShapes.set 1 (.intIn 12 12)) = true :=
  fieldsHaveShape_setBoth recordValues recordShapes 1 (.int 12) (.intIn 12 12)
    (by decide) (by decide)

theorem passt_hasShape_zeuge :
    (Value.record recordValues).hasShape (.record recordShapes) = true :=
  passt_hasShape (a := .record [.intIn 7 7, .record [.bool]]) (by decide) (by decide)

theorem passtFelder_hasShape_zeuge :
    [Shape.intIn 7 7, .record [.bool]].length = recordShapes.length ∧
      Value.fieldsHaveShape recordValues recordShapes = true :=
  passtFelder_hasShape (as := [.intIn 7 7, .record [.bool]]) (by decide) (by decide)

def recordArgs : List Expr :=
  [.recGet (.name "r") 0, .recSet (.name "r") 0 (.lit (.int 9))]

def recordResultShapes : List Shape :=
  [.intIn 0 10, .record [.intIn 9 9, .record [.bool]]]

/-- All entry premises hold together; construction, projection and replacement all occur. -/
theorem schluss_sicher_zeuge :
    ∃ v, eval recordState (.recOf recordArgs) = some v ∧
      v.hasShape (.record recordResultShapes) = true :=
  schluss_sicher recordD recordTyping recordDeclared (.recOf recordArgs)
    recordScope recordState (.record recordResultShapes)
    recordWF recordWFL recordKetten (by decide)

theorem schlussAll_sicher_zeuge :
    ∃ vs, evalAll recordState recordArgs = some vs ∧
      vs.length = recordResultShapes.length ∧
      Value.fieldsHaveShape vs recordResultShapes = true :=
  schlussAll_sicher recordD recordTyping recordDeclared recordArgs
    recordScope recordState recordResultShapes
    recordWF recordWFL recordKetten (by decide)

theorem schlussMitZiel_sicher_record_zeuge :
    ∃ v, eval recordState (.recOf recordArgs) = some v ∧
      v.hasShape (.record recordResultShapes) = true :=
  schlussMitZiel_sicher recordD recordTyping recordDeclared (some (0, 10))
    (.recOf recordArgs) recordScope recordState (.record recordResultShapes)
    recordWF recordWFL recordKetten (by decide)

/-- Invalid field shapes, bases, arities and positions remain refusals. -/
theorem record_refusals_zeuge :
    schluss recordD recordScope (.lit (.record [.reason "error"])) = none ∧
    schluss recordD recordScope (.recOf [.tagOf "Case" none]) = none ∧
    schluss recordD recordScope (.recGet (.lit (.int 7)) 0) = none ∧
    schluss recordD recordScope (.recGet (.name "r") 2) = none ∧
    schluss recordD recordScope (.recSet (.name "r") 2 (.lit (.int 9))) = none ∧
    schluss recordD recordScope (.recSet (.name "r") 0 (.lit (.reason "error"))) = none ∧
    passt (.record [.int]) (.record [.int, .bool]) = false ∧
    passt (.record [.bool]) (.record [.int]) = false := by decide

/-- Empty records are valid values; reading their first position is refused. -/
theorem empty_record_zeuge :
    schluss recordD recordScope (.lit (.record [])) = some (.record []) ∧
    schluss recordD recordScope (.recOf []) = some (.record []) ∧
    schluss recordD recordScope (.recGet (.recOf []) 0) = none := by decide

/-- A record is a successful answer, distinct from every error reason. -/
theorem call_with_error_exit_record_zeuge :
    step recordEnv (.bindCallElse "n" "f" [] [] (.lit (.bool true)) "err" []) recordState =
      .running ⟨recordState.world, bindLocal recordState.local' "n" (.record recordValues)⟩ := by
  have hc : Contract recordEnv "f" (fun t => WF recordTyping t.world ∧
      eval t (.lit (.bool true)) = some (.bool true)) (fun _ _ _ => True) :=
    fun _ _ => trivial
  have h := Gabbro.Coverage.call_with_error_exit_carried recordEnv recordTyping "f" "n" [] []
    (.lit (.bool true)) "err" [] (fun _ _ _ => True) recordState []
    hc recordWF rfl rfl
  exact h.2.2 (.record recordValues) rfl (by intro x h; cases h)

theorem reason_match_record_zeuge (ρ : Env) :
    step ρ (.onReason (.lit (.record recordValues)) []) recordState = .stuck :=
  Gabbro.Coverage.reason_match_carried.2 ρ [] (.lit (.record recordValues)) recordState
    (by intro x h; cases h)

end Gabbro.Sicherheit
