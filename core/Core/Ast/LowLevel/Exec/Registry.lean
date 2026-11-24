module

public import Core.Ast.LowLevel.Exec.Obligations

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Waechter

/-- Declaring a state appends it; the first declaration starts the core in
    the arrival state. -/
def StateDeclMeaningAussage : Prop :=
  ∀ decl s c frame, (ExecInstruction.declareState decl).evaluate s c = some frame →
    frame.states = (s.lokal c).states ++ [decl] ∧
    frame.result = some (.stateDeclared (s.lokal c).states.length) ∧
    frame.current = match (s.lokal c).states with | [] => some 0 | _ => (s.lokal c).current

/-- A same-state jump keeps the current state and records both slots. -/
def JumpMeaningAussage : Prop :=
  ∀ code state s c frame, (ExecInstruction.jump code state).evaluate s c = some frame →
    (s.lokal c).current = some state ∧ state < (s.lokal c).states.length ∧
    ¬ (s.lokal c).halted ∧ frame.current = some state ∧
    frame.result = some (.jumped code state)

/-- A long transfer changes the current state abstractly: the destination
    differs, exists, and carries a space exactly when translation is on. -/
def JumpLongMeaningAussage : Prop :=
  ∀ code dest sp st s c frame,
    (ExecInstruction.jumpLong code dest sp st).evaluate s c = some frame →
    ∃ cur decl, (s.lokal c).current = some cur ∧ cur ≠ dest ∧
      (s.lokal c).states[dest]? = some decl ∧ ¬ (s.lokal c).halted ∧
      frame.current = some dest ∧ frame.activeSpace = sp ∧
      frame.result = some (.jumpedLong code dest) ∧
      (decl.translation = .on → ∃ id, sp = some id) ∧
      (decl.translation = .off → sp = none)

/-- Waiting and stopping need a started, running core. -/
def WaitMeaningAussage : Prop :=
  ∀ s c frame, ExecInstruction.waitInterrupt.evaluate s c = some frame →
    (s.lokal c).current.isSome ∧ ¬ (s.lokal c).halted ∧
    frame.result = some .waited ∧ frame.halted = false

def StopMeaningAussage : Prop :=
  ∀ s c frame, ExecInstruction.stopCore.evaluate s c = some frame →
    (s.lokal c).current.isSome ∧ ¬ (s.lokal c).halted ∧
    frame.result = some .stopped ∧ frame.halted = true

/-- An entry installs a fresh vector name; privileged kinds need the own
    stack, and only interrupts carry a priority. -/
def EntryMeaningAussage : Prop :=
  ∀ name kind stack priority s c frame,
    (ExecInstruction.declareEntry name kind stack priority).evaluate s c = some frame →
    (s.lokal c).entries.all (fun p => p.1.val != name.val) ∧
    (kind.needsOwnStack → stack = .own) ∧
    (kind.needsPriority ↔ priority.isSome) ∧
    frame.entries = (s.lokal c).entries ++ [(name, kind)] ∧
    frame.result = some (.entryDeclared name)

def JumpJointAussage : Prop :=
  ExecErfuellbarNach .jump fun «prefix» op =>
    ∃ decl code state, «prefix» = [.declareState decl] ∧ op = .jump code state

def JumpLongJointAussage : Prop :=
  ExecErfuellbarNach .jumpLong fun «prefix» op =>
    ∃ first second code dest sp st, «prefix» = [.declareState first, .declareState second] ∧
      op = .jumpLong code dest sp st

def WaitJointAussage : Prop :=
  ExecErfuellbarNach .waitInterrupt fun «prefix» op =>
    ∃ decl, «prefix» = [.declareState decl] ∧ op = .waitInterrupt

def StopJointAussage : Prop :=
  ExecErfuellbarNach .stopCore fun «prefix» op =>
    ∃ decl, «prefix» = [.declareState decl] ∧ op = .stopCore

def MeaningAussageExec : ExecForm → Prop
  | .stateDecl => StateDeclMeaningAussage
  | .jump => JumpMeaningAussage
  | .jumpLong => JumpLongMeaningAussage
  | .waitInterrupt => WaitMeaningAussage
  | .stopCore => StopMeaningAussage
  | .entryDecl => EntryMeaningAussage
  | form => ExecErfuellbarAussage form

def JointAussageExec : ExecForm → Prop
  | .jump => JumpJointAussage
  | .jumpLong => JumpLongJointAussage
  | .waitInterrupt => WaitJointAussage
  | .stopCore => StopJointAussage
  | form => ExecErfuellbarAussage form

def StateDeclAussage : Prop :=
  execObligationsKern .stateDecl ∧ StateDeclMeaningAussage ∧ ExecErfuellbarAussage .stateDecl

def JumpAussage : Prop :=
  execObligationsKern .jump ∧ JumpMeaningAussage ∧ JumpJointAussage

def JumpLongAussage : Prop :=
  execObligationsKern .jumpLong ∧ JumpLongMeaningAussage ∧ JumpLongJointAussage

def WaitAussage : Prop :=
  execObligationsKern .waitInterrupt ∧ WaitMeaningAussage ∧ WaitJointAussage

def StopAussage : Prop :=
  execObligationsKern .stopCore ∧ StopMeaningAussage ∧ StopJointAussage

def EntryAussage : Prop :=
  execObligationsKern .entryDecl ∧ EntryMeaningAussage ∧ ExecErfuellbarAussage .entryDecl

def statementsExec (constructor : Lean.Name) (form : ExecForm) : RegistryStatements constructor .surface where
  realization := .surface (ExecParseAussage form ∧ ExecInversionAussage form ∧
    ExecEindeutigAussage form ∧ ExecDruckAussage form)
    (ExecElaboriertAussage form) (ExecRealisiertAussage form)
  acceptanceRule := ExecAnnahmeAussage form ∧ ExecAussenLokalAussage form ∧ MeaningAussageExec form
  idealRule := ExecIdealAussage form
  unitsAndCommutation := ExecEinheitAussage form
  implementationRule := ExecImplAussage form
  preservation := ExecErhaltungAussage form ∧ ExecFortschrittAussage form ∧
    ExecRegelSicherAussage form ∧ ExecRegelAntwortSicherAussage form ∧ ExecKostenAussage form ∧
    ExecSchrankenAussage ∧ ExecEtikettenAussage ∧ ExecFlussAussage
  jointlySatisfiable := JointAussageExec form

def schemaExec (constructor : Lean.Name) : RegistrySchema constructor :=
  let form := if constructor == ``ExecTree.stateDecl then ExecForm.stateDecl
    else if constructor == ``ExecTree.jump then .jump
    else if constructor == ``ExecTree.jumpLong then .jumpLong
    else if constructor == ``ExecTree.waitInterrupt then .waitInterrupt
    else if constructor == ``ExecTree.stopCore then .stopCore
    else if constructor == ``ExecTree.entryDecl then .entryDecl
    else if constructor == ``ExecTree.cpuCaps then .cpuCaps
    else if constructor == ``ExecTree.cpuCycles then .cpuCycles
    else if constructor == ``ExecTree.suspendSystem then .suspendSystem
    else if constructor == ``ExecTree.suspendCore then .suspendCore
    else ExecForm.resumeArrival
  ⟨.surface, statementsExec constructor form⟩

end Gabbro.Core.Ast.LowLevel
