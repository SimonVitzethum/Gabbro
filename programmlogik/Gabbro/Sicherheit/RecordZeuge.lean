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

def recordArgs : List Expr :=
  [.recGet (.name "r") 0, .recSet (.name "r") 0 (.lit (.int 9))]

def recordResultShapes : List Shape :=
  [.intIn 0 10, .record [.intIn 9 9, .record [.bool]]]

end Gabbro.Sicherheit
