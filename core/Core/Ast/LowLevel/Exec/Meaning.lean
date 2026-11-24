module

public import Core.Ast.LowLevel.Exec.State
public import Core.Ast.LowLevel.Exec.Syntax

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

inductive ExecInstruction where
  | declareState (decl : ExecStateDecl)
  | jump (target state : Nat)
  | jumpLong (target dest : Nat) (space stack : Option Nat)
  | waitInterrupt
  | stopCore
  | declareEntry (name : Identifier) (kind : EntryKind) (stack : EntryStack)
      (priority : Option Nat)

/-- Name resolution uses the arrival-contract scope. A `jump` pins the
    state its target code item runs in; a `jump long` pins the destination
    state and the abstract space and stack capabilities. -/
def elaborateExec (scope : ExecScope) : ExecTree form → Option ExecInstruction
  | .stateDecl _ decl =>
      if decl.wellformed then some (.declareState decl) else none
  | .jump target => do
      let code ← scope.slotCode target
      let state ← scope.codeState target
      pure (.jump code state)
  | .jumpLong target dest space stack => do
      let code ← scope.slotCode target
      let dst ← scope.slotState dest
      let sp ← match space with
        | none => pure none
        | some s => (scope.slotSpace s).map some
      let st ← match stack with
        | none => pure none
        | some s => (scope.slotStack s).map some
      pure (.jumpLong code dst sp st)
  | .waitInterrupt => some .waitInterrupt
  | .stopCore => some .stopCore
  | .entryDecl name kind stack priority =>
      (List.idxOf? name.val (scope.entries.map Subtype.val)).map
        (fun _ => .declareEntry name kind stack priority)

/-- The first declared state is the arrival state: declaring it starts the
    core in that state. Later declarations only extend the table. -/
def ExecFrame.declare (frame : ExecFrame) (decl : ExecStateDecl) : ExecFrame :=
  { frame with
    result := some (.stateDeclared frame.states.length)
    states := frame.states ++ [decl]
    current := match frame.states with | [] => some 0 | _ => frame.current }

def ExecInstruction.evaluate (op : ExecInstruction) (s : ExecState) (c : Kontext) :
    Option ExecFrame :=
  let frame := s.lokal c
  match op with
  | .declareState decl =>
      if decl.wellformed then pure (frame.declare decl) else none
  | .jump target state => do
      let cur ← frame.current
      if cur == state ∧ ¬ frame.halted ∧ state < frame.states.length then
        pure { frame with result := some (.jumped target state) }
      else none
  | .jumpLong target dest space stack => do
      let cur ← frame.current
      let dst ← frame.states[dest]?
      if cur != dest ∧ ¬ frame.halted ∧
          (match stack with | some st => st < frame.stapel.length | none => True) ∧
          (match dst.translation, space with
            | .on, some sp => sp < frame.spaces.length
            | .off, none => True
            | _, _ => False) then
        pure { frame with
          result := some (.jumpedLong target dest)
          current := some dest
          activeSpace := space }
      else none
  | .waitInterrupt =>
      if frame.current.isSome ∧ ¬ frame.halted then
        pure { frame with result := some .waited }
      else none
  | .stopCore =>
      if frame.current.isSome ∧ ¬ frame.halted then
        pure { frame with result := some .stopped, halted := true }
      else none
  | .declareEntry name kind stack priority =>
      if frame.entries.all (fun p => p.1.val != name.val) ∧
          (kind.needsOwnStack → stack = .own) ∧
          (kind.needsPriority ↔ priority.isSome) then
        pure { frame with result := some (.entryDeclared name),
          entries := frame.entries ++ [(name, kind)] }
      else none

/-- Evaluation reads only the acting frame. -/
theorem ExecInstruction.evaluate_congr (op : ExecInstruction) (c : Kontext)
    {s₁ s₂ : ExecState} (locals : s₁.lokal = s₂.lokal) :
    op.evaluate s₁ c = op.evaluate s₂ c := by
  cases s₁
  cases s₂
  cases locals
  cases op <;> rfl

end Gabbro.Core.Ast.LowLevel
