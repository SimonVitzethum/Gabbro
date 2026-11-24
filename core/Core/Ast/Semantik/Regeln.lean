module

public import Core.Ast.Semantik.Arithmetik
public import Core.Maschine.Start

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine

/-- The runtime integer package retains its two bounds and their proofs. -/
structure Ganzzahl where
  lo : Int
  hi : Int
  zahl : Zahl lo hi

def Ganzzahl.typ (value : Ganzzahl) : Ty .value := .int value.lo value.hi

def Ganzzahl.literal (value : Int) : Ganzzahl := ⟨value, value, Zahl.literal value⟩

def Ganzzahl.binaer (op : Arith) (a b : Ganzzahl) : Ganzzahl :=
  ⟨_, _, op.auswerten a.zahl b.zahl⟩

/-- Each context has its own instruction pointer, temporary slots and immutable locals.
    Locals are stored in scope order. Temporaries are numbered by the elaborator. -/
structure Rahmen where
  pc : Nat
  temp : Nat → Ganzzahl
  lokale : List (Identifier × Ganzzahl)

def Rahmen.start : Rahmen := ⟨0, fun _ => Ganzzahl.literal 0, []⟩

abbrev Zustand := Maschine.Zustand PUnit PUnit Int PUnit Rahmen PUnit
abbrev Plan := SchrittPlan PUnit PUnit Int PUnit
abbrev Regel := Maschine.Regel Zustand Plan PUnit

/-- One linearisation point per expression node or binding. A binary instruction
    consumes the slots left by its children. A binding takes its initializer's slot. -/
inductive Befehl where
  | literal (ziel : Nat) (wert : Nat)
  | binaer (op : Arith) (links : Nat)
  | binden (name : Identifier) (quelle : Nat)

/-- Exact evaluation at the instruction boundary. Each result retains its source range. -/
def Befehl.auswerten : Befehl → Rahmen → Rahmen
  | .literal dst val, frame =>
    { frame with pc := frame.pc + 1, temp := Function.update frame.temp dst (Ganzzahl.literal val) }
  | .binaer op left, frame =>
    { frame with
      pc := frame.pc + 1
      temp := Function.update frame.temp left (Ganzzahl.binaer op (frame.temp left) (frame.temp (left + 1))) }
  | .binden name src, frame =>
    { frame with pc := frame.pc + 1, lokale := (name, frame.temp src) :: frame.lokale }

abbrev Bedarf := (op : PartielleOperation) × Operanden op

/-- The three worked instructions are total. Explicit narrowing will contribute
    the range guard at its own instruction. -/
def Befehl.guard : Befehl → Rahmen → Option Bedarf
  | .literal _ _, _ => none
  | .binaer _ _, _ => none
  | .binden _ _, _ => none

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
