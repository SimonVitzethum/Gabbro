module

public import Core.Annahme.AussenLauf
public import Core.Sicherheit.Regel

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel.Device

open Katalog Maschine Annahme

/-- A fallible read checks the declared interval against the one catalogue reply. -/
structure ReadRange where
  lower : Nat
  upper : Nat
  ordered : lower ≤ upper

inductive RegisterAccess where
  | read (offset : Nat)
  | write (offset value : Nat)
  | fallibleRead (offset : Nat) (range : ReadRange)

def RegisterAccess.operation : RegisterAccess → AussenOperation
  | .read offset | .fallibleRead offset _ => .registerRead offset
  | .write offset value => .registerWrite offset value

structure Binding (k : Katalog) where
  handle : Handle
  row : GeraeteDaten
  selected : k.enthaelt (.endpoint handle.origin.object.endpoint)
  described : k.plattform.geraet handle.origin.object.endpoint = some row

def Binding.question (binding : Binding k) (access : RegisterAccess) : Frage :=
  ⟨binding.handle.origin.object.endpoint, binding.handle, [], access.operation⟩

/-- Start and reset changes have to be established by the catalogue for the
    same device that acknowledges the register write. -/
structure RegisterTransition (k : Katalog) (binding : Binding k) where
  prior : GeraetePhase
  action : GeraeteAktion
  after : GeraetePhase
  rule : GeraeteUebergang binding.row k.plattform.ziel prior action after
  freeBefore : prior = .ready ∨ prior = .reset
  freeAfter : after = .ready ∨ after = .reset

inductive Result where
  | value (value : Nat)
  | written
  | readOutOfRange (value : Nat)
  | refused (failure : AussenFehler)
  | unexpectedAnswer

def RegisterAccess.result (access : RegisterAccess) (answer : Antwort) : Result :=
  match answer.result with
  | .error failure => .refused failure
  | .ok (.register value) =>
    match access with
    | .read _ => .value value
    | .fallibleRead _ range =>
      if range.lower ≤ value ∧ value ≤ range.upper then .value value else .readOutOfRange value
    | .write .. => .unexpectedAnswer
  | .ok (.registerWritten offset value) =>
    match access with
    | .write expected data => if (offset, value) = (expected, data) then .written else .unexpectedAnswer
    | .read _ | .fallibleRead .. => .unexpectedAnswer
  | .ok _ => .unexpectedAnswer

structure Frame where
  phases : Objekt → Option GeraetePhase := fun _ => none
  pending : Option Frage := none
  last : Option Result := none

abbrev State := Zustand PUnit Nat UInt8 PUnit Frame PUnit
abbrev Plan := SchrittPlan PUnit Nat UInt8 PUnit

/-- A check at issue and reply. In addition to M5's handle-right ledger, the
    exact device has one free owner and must be in the required phase. -/
def Befugt (binding : Binding k) (required : GeraetePhase) (access : RegisterAccess)
    (s : State) (c : Kontext) : Prop :=
  s.buchung.geraet binding.handle.origin.object = some (c, .frei) ∧
  (s.lokal c).phases binding.handle.origin.object = some required ∧
  AussengriffeEigen s c (binding.question access) ∧
  registerZugriff binding.row access.operation = true

def internal : Plan :=
  ⟨.intern, [], [], fun _ => false, fun _ => .na, fun _ => 0⟩

def setFrame (s : State) (c : Kontext) (frame : Frame) : State :=
  { s with lokal := Function.update s.lokal c frame }

/-- One request goes through the machine's question action. Its response will
    be chosen by the catalogue in the view of the answer event. -/
inductive Rule (binding : Binding k) (access : RegisterAccess) (required : GeraetePhase)
    (target : Option GeraetePhase) (c : Kontext) (s : State) : Plan → State → Prop where
  | issue (owned : Befugt binding required access s c) (idle : (s.lokal c).pending = none) :
      Rule binding access required target c s
        { internal with aktion := .frage (binding.question access) }
        (setFrame s c { s.lokal c with pending := some (binding.question access) })
  | consume (owned : Befugt binding required access s c) {answer}
      (pending : (s.lokal c).pending = some (binding.question access))
      (ready : s.naechsteAntwort c = some answer)
      (matches : answer.question = binding.question access) :
      Rule binding access required target c s { internal with aktion := .verbrauche answer }
        (setFrame s c { s.lokal c with
          pending := none
          last := some (access.result answer.reply)
          phases := match access.result answer.reply, target with
            | .written, some phase => Function.update (s.lokal c).phases binding.handle.origin.object (some phase)
            | _, _ => (s.lokal c).phases })

def registerRule (binding : Binding k) (access : RegisterAccess) :
    Regel State Plan PUnit :=
  let step := fun c s (_ : PUnit) plans next =>
    ∃ plan, plans = [plan] ∧ Rule binding access .ready none c s plan next
  ⟨step, step⟩

def transitionRule (binding : Binding k) (offset value : Nat)
    (transition : RegisterTransition k binding) : Regel State Plan PUnit :=
  let step := fun c s (_ : PUnit) plans next =>
    ∃ plan, plans = [plan] ∧ Rule binding (.write offset value) transition.prior
      (some transition.after) c s plan next
  ⟨step, step⟩

end Gabbro.Core.Ast.LowLevel.Device
