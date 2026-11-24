module

public import Core.Ast.Grammar
public import Core.Ast.Semantik.Regeln

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

/-- Elaborating a fragment records both its executable instructions and its written clauses.
    Sequencing preserves the order of the instructions and of each kind of clause. -/
structure Fragment where
  code : List Befehl
  klauseln : Quellklauseln Zustand

def Fragment.leer : Fragment := ⟨[], .leer⟩

def Fragment.einzel (b : Befehl) : Fragment := ⟨[b], .leer⟩

def Fragment.anhaengen (a b : Fragment) : Fragment :=
  ⟨a.code ++ b.code, a.klauseln.anhaengen b.klauseln⟩

/-- An expression writes its result to the requested temporary. Its right
    operand starts above its left result, which must survive that operand. -/
def expr (slot : Nat) : Expr scope type → Fragment
  | .lit value => .einzel (.literal slot value)
  | .binary op left right =>
    ((expr slot left).anhaengen (expr (slot + 1) right)).anhaengen (.einzel (.binaer op slot))

def stmt : Stmt before after → Fragment
  | .letValue name _ value => (expr 0 value).anhaengen (.einzel (.binden name 0))

def block : Block before after → Fragment
  | .done => .leer
  | .step first rest => (stmt first).anhaengen (block rest)

def decl (d : Decl before after) : Fragment := nomatch d

def unitBody : UnitBody before after → Fragment
  | .done => .leer
  | .step first rest => (decl first).anhaengen (unitBody rest)

def fragment : (category : Category) → category.Tree → Fragment
  | .expression _, tree => expr 0 tree.2
  | .statement _, tree => stmt tree.2
  | .block _, tree => block tree.2
  | .unit, tree => unitBody tree.2

abbrev Einheit := Maschine.Einheit PUnit PUnit Int PUnit Rahmen PUnit PUnit PUnit Befehl


def startdaten (kern : Option Nat) : Startdaten Int PUnit Rahmen PUnit :=
  ⟨fun _ => .start, fun c => if c = eintritt then .laeuft else .ruht,
    fun k => ⟨if some k = kern then some eintritt else none, .nutzer, (), fun _ => false,
      0, false, []⟩, ⟨fun _ => false, fun _ => 0⟩⟩

def einrichtung : Einrichtung PUnit PUnit Int PUnit Rahmen PUnit PUnit :=
  ⟨fun _ => 0, fun _ => (), fun _ => (), fun _ => 0, fun _ _ _ => False, fun _ _ => True,
    ⟨0, 0⟩, ⟨eintritt, 0, fun _ => startdaten (some 0), fun _ _ => 0⟩,
    fun _ => 0, fun _ _ _ => none⟩

/-- The model's entry slot. An image compiler and its byte-level proof are later milestones. -/
def bild : Bild := ⟨.elf, fun a => if a = 0 then some 0 else none, [0]⟩

def startmedium (_ : AussenStart) (_ : Nat) : UInt8 := 0

def laden (start : AussenStart) (image : Ladung) : Option Zustand :=
  if image.starts 0 = some 0 ∧ image.bytes 0 = some 0 then
    let d := startdaten (start.assignment 0)
    some (Maschine.Zustand.start d.lokal d.status d.kerne d.rechte einrichtung.initial
      (.leer (startmedium start)))
  else none

/-- Guards are collected at the source head, including at a cut with no hardware opportunity. -/
def Fragment.tabellen (p : Fragment) : Quelltabellen Zustand :=
  ⟨p.klauseln, fun s op args => ∃ c b, kopf p.code s c = some b ∧
    b.guard (s.lokal c) = some ⟨op, args⟩⟩

/-- The current forms each take one concrete step at their linearisation point. State
    matching is equality at those points and the number of private steps is zero. -/
def Fragment.einheit (p : Fragment) (platform : Plattform) : Einheit where
  katalog := platform.katalog
  bild := bild
  einrichtung := einrichtung
  system := system p.code
  startdaten := fun start => startdaten (start.assignment 0)
  startmedium := startmedium
  laden := laden
  lokalerBezug := Eq
  stotterLaenge := fun _ => 0
  quelltabellen := p.tabellen

def elaborieren (platform : Plattform) {category : Category} (tree : category.Tree) : Einheit :=
  (fragment category tree).einheit platform

/-- Platform selection binds the hardware catalogue without changing the source system or its guards. -/
theorem elaborieren_quellbedeutung (left right : Plattform) {category : Category}
    (tree : category.Tree) :
    (elaborieren left tree).system = (elaborieren right tree).system ∧
      (elaborieren left tree).quelltabellen = (elaborieren right tree).quelltabellen :=
  ⟨rfl, rfl⟩

def Elaboriert (platform : Plattform) {category : Category}
    (tree : category.Tree) (E : Einheit) : Prop :=
  E = elaborieren platform tree

theorem elab_korrekt (platform : Plattform) {category : Category} (tree : category.Tree) :
    Elaboriert platform tree (elaborieren platform tree) := rfl

theorem elab_vollstaendig {category : Category} {tree : category.Tree} (meaning : Elaboriert platform tree E) : E = elaborieren platform tree := meaning

theorem Elaboriert.deterministisch {category : Category} {tree : category.Tree}
    (a : Elaboriert platform tree E) (b : Elaboriert platform tree F) : E = F :=
  a.trans b.symm

def Bezeichnet (platform : Plattform) (category : Category) : Text.RawText → Einheit → Prop :=
  Ast.Bezeichnet (@Elaboriert platform category)

theorem bezeichnet_deterministisch
    (a : Bezeichnet platform category text E) (b : Bezeichnet platform category text F) : E = F :=
  Ast.bezeichnet_deterministic (elaborates := @Elaboriert platform category)
    (fun left right => left.trans right.symm) a b

end Gabbro.Core.Ast.Semantik
