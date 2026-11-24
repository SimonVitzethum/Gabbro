module

public import Core.Ast.Tree
public import Core.Maschine.Start

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine

/-- Each context has its own instruction pointer, temporary slots and immutable locals.
    Locals are stored in scope order. Temporaries are numbered by the elaborator. -/
structure Rahmen where
  pc : Nat
  temp : Nat → Int
  lokale : List (Identifier × Int)

def Rahmen.start : Rahmen := ⟨0, fun _ => 0, []⟩

abbrev Zustand := Maschine.Zustand PUnit PUnit Int PUnit Rahmen PUnit
abbrev Plan := SchrittPlan PUnit PUnit Int PUnit
abbrev Regel := Maschine.Regel Zustand Plan PUnit

/-- One linearisation point per expression node or binding. A binary instruction
    consumes the slots left by its children. A binding takes its initializer's slot. -/
inductive Befehl where
  | literal (ziel : Nat) (wert : Nat)
  | binaer (op : Arith) (links : Nat)
  | binden (name : Identifier) (quelle : Nat)

def operation : Arith → Int → Int → Int
  | .add => Int.add
  | .mul => Int.mul

/-- Mathematical evaluation at the instruction boundary. The separate range
    guard makes each use representable in the machine type of an accepted run. -/
def Befehl.auswerten : Befehl → Rahmen → Rahmen
  | .literal dst val, frame =>
    { frame with pc := frame.pc + 1, temp := Function.update frame.temp dst (Int.ofNat val) }
  | .binaer op left, frame =>
    { frame with
      pc := frame.pc + 1
      temp := Function.update frame.temp left (operation op (frame.temp left) (frame.temp (left + 1))) }
  | .binden name src, frame =>
    { frame with pc := frame.pc + 1, lokale := (name, frame.temp src) :: frame.lokale }

abbrev Bedarf := (op : PartielleOperation) × Operanden op

def Befehl.guard : Befehl → Nat → Rahmen → Option Bedarf
  | .literal _ val, width, _ => some ⟨.ganzzahlBereich, (Int.ofNat val, width)⟩
  | .binaer op left, width, frame =>
    some ⟨.ganzzahlBereich, (operation op (frame.temp left) (frame.temp (left + 1)), width)⟩
  | .binden _ _, _, _ => none

def plan : Plan := ⟨.intern, [], [], fun _ort => false, fun _ort => .na, fun _ort => 0⟩

def Befehl.nach (b : Befehl) (c : Kontext) (s : Zustand) : Zustand :=
  { s with lokal := Function.update s.lokal c (b.auswerten (s.lokal c)) }

/-- The context-local transition used by the ideal rule. -/
def Befehl.ideal (b : Befehl) (c : Kontext) (s : Zustand) (_ : PUnit.{1})
    (plans : List Plan) (u : Zustand) : Prop :=
  plans = [plan] ∧ u = b.nach c s

/-- The concrete one-step realization uses the same mathematical transfer on
    context-local values. Shared events go through the machine protocol. -/
def Befehl.impl (b : Befehl) (c : Kontext) (s : Zustand) (_ : PUnit.{1})
    (plans : List Plan) (u : Zustand) : Prop :=
  plans = [plan] ∧ u = b.nach c s

def Befehl.regel (b : Befehl) : Regel := ⟨b.impl, b.ideal⟩

abbrev LokalSystem := MaschinenSystem PUnit PUnit Int PUnit Rahmen PUnit PUnit PUnit Befehl

def eintritt : Kontext := .faden 0

def kopf (code : List Befehl) (s : Zustand) (c : Kontext) : Option Befehl :=
  if c = eintritt then
    match s.status c with
    | .ruht => none
    | .laeuft => code[(s.lokal c).pc]?
    | .beendet _ => none
  else none

def system (code : List Befehl) : LokalSystem :=
  ⟨Befehl.regel, kopf code, fun s c => kopf code s c = none, fun _ _ _ => False⟩

end Gabbro.Core.Ast.Semantik
