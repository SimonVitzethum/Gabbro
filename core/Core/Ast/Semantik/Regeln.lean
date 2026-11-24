module

public import Core.Ast.Semantik.Arithmetik
public import Core.Maschine.Start

@[expose] public section

namespace Gabbro.Core.Ast

abbrev Dynamisch := (type : Ty .value) × Wert type

end Gabbro.Core.Ast

namespace Gabbro.Core.Ast.Semantik

open Maschine

/-- The runtime integer package retains its two bounds and their proofs. -/
structure Ganzzahl where
  lo : Int
  hi : Int
  zahl : Zahl lo hi

def Ganzzahl.pack (value : Ganzzahl) : Dynamisch := ⟨.int value.lo value.hi, value.zahl⟩

def alsGanzzahl : Dynamisch → Option Ganzzahl
  | ⟨.int lo hi, value⟩ => some ⟨lo, hi, value⟩
  | ⟨.bool, _⟩ => none

def alsBoolean : Dynamisch → Option Bool
  | ⟨.int _ _, _⟩ => none
  | ⟨.bool, value⟩ => some value

def wertIn (type : Ty .value) (value : Dynamisch) : Option Dynamisch :=
  match type, value with
  | .int lo hi, ⟨.int _ _, number⟩ =>
    if bounds : lo ≤ number.wert ∧ number.wert ≤ hi then
      some ⟨.int lo hi, ⟨number.wert, bounds.1, bounds.2⟩⟩
    else none
  | .bool, ⟨.bool, value⟩ => some ⟨.bool, value⟩
  | .int _ _, ⟨.bool, _⟩ => none
  | .bool, ⟨.int _ _, _⟩ => none

def anfangswert : Ty .value → Option Dynamisch
  | .bool => some ⟨.bool, false⟩
  | .int lo hi =>
    if ordered : lo ≤ hi then some ⟨.int lo hi, ⟨lo, Int.le_refl _, ordered⟩⟩ else none

/-- Each context has its own instruction pointer, temporary slots and local values.
    Locals are stored in scope order. Temporaries are numbered by the elaborator. -/
structure Rahmen where
  pc : Nat
  temp : Nat → Option Dynamisch
  lokale : List (Option Dynamisch)
  rueckgabe : Option Dynamisch

/-- Fragment entry chooses the lower endpoint of each nonempty incoming interval.
    A source unit starts with the empty scope. -/
def Rahmen.start (scope : Scope) : Rahmen :=
  ⟨0, fun _ => none, scope.map (fun binding => anfangswert binding.type), none⟩

def Rahmen.schreibe (frame : Rahmen) (ziel : Nat) (value : Option Dynamisch) : Rahmen :=
  { frame with pc := frame.pc + 1, temp := Function.update frame.temp ziel value }

def Rahmen.zahl (frame : Rahmen) (slot : Nat) : Option Ganzzahl :=
  (frame.temp slot).bind alsGanzzahl

abbrev Zustand := Maschine.Zustand PUnit PUnit Int PUnit Rahmen PUnit
abbrev Plan := SchrittPlan PUnit PUnit Int PUnit
abbrev Regel := Maschine.Regel Zustand Plan PUnit

/-- One linearisation point per expression node or binding. A binary instruction
    consumes the slots left by its children. A binding takes its initializer's slot. -/
inductive Befehl where
  | literal (ziel : Nat) (wert : Nat)
  | binaer (op : Arith) (links : Nat)
  | binden (name : Identifier) (quelle : Nat)
  | wahrheitswert (ziel : Nat) (wert : Bool)
  | lesen (ziel index : Nat)
  | negativ (ziel : Nat) (betrag : Nat)
  | negieren (ziel : Nat)
  | verneinen (ziel : Nat)
  | teilen (links : Nat)
  | vergleichen (op : Compare) (links : Nat)
  | springeWenn (quelle : Nat) (bei : Bool) (abstand : Nat)
  | zuweisen (quelle index : Nat) (zieltyp : Ty .value)
  | zurueck (quelle : Nat) (zieltyp : Ty .value)
  | springe (abstand : Nat)
  | blockEnde (freigabe : Nat)

/-- Exact evaluation at the instruction boundary. Each result retains its source range. -/
def Befehl.auswerten : Befehl → Rahmen → Rahmen
  | .literal dst val, frame =>
    frame.schreibe dst (some ⟨.int val val, Zahl.literal val⟩)
  | .binaer op left, frame =>
    frame.schreibe left (do
      let a ← frame.zahl left
      let b ← frame.zahl (left + 1)
      pure (Ganzzahl.pack ⟨_, _, op.auswerten a.zahl b.zahl⟩))
  | .binden _ src, frame =>
    { frame with pc := frame.pc + 1, lokale := frame.temp src :: frame.lokale }
  | .wahrheitswert dst value, frame =>
    frame.schreibe dst (some ⟨.bool, value⟩)
  | .lesen dst index, frame =>
    frame.schreibe dst (frame.lokale[index]?.join)
  | .negativ dst magnitude, frame =>
    let value : Int := -(magnitude : Int)
    frame.schreibe dst (some ⟨.int value value, Zahl.literal value⟩)
  | .negieren dst, frame =>
    frame.schreibe dst ((frame.zahl dst).map fun a => Ganzzahl.pack ⟨_, _, a.zahl.neg⟩)
  | .verneinen dst, frame =>
    frame.schreibe dst (((frame.temp dst).bind alsBoolean).map fun bit => ⟨.bool, !bit⟩)
  | .teilen left, frame =>
    frame.schreibe left (do
      let a ← frame.zahl left
      let b ← frame.zahl (left + 1)
      if h : 1 ≤ b.lo ∨ b.hi ≤ -1 then
        pure ⟨quotientType a.lo a.hi b.lo, a.zahl.div b.zahl h⟩
      else none)
  | .vergleichen op left, frame =>
    frame.schreibe left (do
      let a ← frame.zahl left
      let b ← frame.zahl (left + 1)
      pure ⟨.bool, op.eval a.zahl.wert b.zahl.wert⟩)
  | .springeWenn src whenValue distance, frame =>
    let taken := (frame.temp src).bind alsBoolean = some whenValue
    { frame with pc := frame.pc + (if taken then distance else 1) }
  | .zuweisen src index target, frame =>
    let value := (frame.temp src).bind (wertIn target)
    { frame with pc := frame.pc + 1, lokale := frame.lokale.set index value }
  | .zurueck src target, frame =>
    { frame with pc := frame.pc + 1, rueckgabe := (frame.temp src).bind (wertIn target) }
  | .springe distance, frame =>
    { frame with pc := frame.pc + distance }
  | .blockEnde count, frame =>
    { frame with pc := frame.pc + 1, lokale := frame.lokale.drop count }

abbrev Bedarf := (op : PartielleOperation) × Operanden op

/-- Division reports both operand magnitudes at the pre-state, as required by the natural-number guard row. -/
def Befehl.guard : Befehl → Rahmen → Option Bedarf
  | .teilen left, frame => do
    let a ← frame.zahl left
    let b ← frame.zahl (left + 1)
    pure ⟨.division, (a.zahl.wert.natAbs, b.zahl.wert.natAbs)⟩
  | _, _ => none

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
    | .laeuft =>
      match (s.lokal c).rueckgabe with
      | none => code[(s.lokal c).pc]?
      | some _ => none
    | .beendet _ => none
  else none

def system (code : List Befehl) : LokalSystem :=
  ⟨Befehl.regel, kopf code, fun s c => kopf code s c = none, fun _ _ _ => False⟩

end Gabbro.Core.Ast.Semantik
