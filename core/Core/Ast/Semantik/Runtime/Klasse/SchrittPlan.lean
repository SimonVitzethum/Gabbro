/- The operands, plans and authority checks of runtime classes. -/
module

public import Core.Ast.Semantik.Runtime.Klasse.Klasse
public import Core.Ast.Semantik.Runtime.Klasse.Zugriff
public import Core.Ast.Semantik.Runtime.Faden.Erhalt
public import Core.Maschine.Aussen
public import Core.Aussen.Frage.Wert
public import Core.Aussen.Frage.Commit

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog
open Gabbro.Core.Speicher (Etikett Modus)
open Gabbro.Core.Sicherheit (Speicherrecht)

/-- **The plan of a private step**: no memory access, no lock, no question, no waiting. It is the plan of
    every step of the classes `lokal` and `ruf`, and of a refused access. -/
def plan : Plan := ⟨.intern, [], [], fun _ort => false, fun _ort => .na, fun _ort => 0⟩

/-- A region is live while its object lives in its arrival generation and is not lent out. The
    acting context's own authority is its frame: only a frame that holds the owned-region value and
    lists the arrival extent can bind it, and a start gives the arrival regions to one context. -/
def Zustand.regionLive (s : Zustand) (slot : Nat) : Bool :=
  s.rechte.lebt slot && s.rechte.gen slot == 0 &&
    (match s.leihen slot with | .eigen => true | .verliehen _device => false)

/-- **What an interrupt-control step names** (MK-20): the immediates of the four instructions. A mask
    step names its vector and direction, a threshold step its bound, a send its vector and target core,
    a route its line, target core and priority. The operand is filled from the instruction, not the frame. -/
structure Unterbrechungsoperand where
  vektor : Nat
  aus : Bool
  grenze : Nat
  kern : Nat
  leitung : Nat
  prioritaet : Nat

/-- The operand of a step that names no interrupt (every other class). -/
def Unterbrechungsoperand.keiner : Unterbrechungsoperand := ⟨0, false, 0, 0, 0, 0⟩

/-- **What a step names, read from its frame**: the cell of an access, the value it writes, the lock of a
    lock action, the question it asks, the answer slot named by a consume step, and the immediates
    of an interrupt-control step. A class reads the fields it needs and ignores the others.
structure Operand where
  ort : Zelle
  wert : Int
  sperre : Nat
  frage : Option Frage
  aenderung : Aenderung
  faden : Fadenoperand
  ziel : Nat
  unterbrechung : Unterbrechungsoperand

/-- The operand of a step that names nothing (the frame-only classes). -/
def Operand.keiner : Operand :=
  ⟨.aussen, 0, 0, none, .tausche, Fadenoperand.keiner, 0, Unterbrechungsoperand.keiner⟩

/-- The plan of a step that records no memory event and no question and carries the given protocol action. -/
def planMit (a : Aktion Nat PUnit) : Plan := ⟨a, [], [], fun _ort => false, fun _ort => .na, fun _ort => 0⟩

/-- The plan of a step that asks the question the operand names; an operand without a question has the
    private plan (the step is refused). -/
def Operand.fragePlan (o : Operand) : Plan :=
  match o.frage with
  | some q => ⟨.frage q, [], [], fun _ort => false, fun _ort => .na, fun _ort => 0⟩
  | none => Semantik.plan

/-- **The plan of one step of class `k`** at the operand `o`, where `v` is the value the memory model
    returned for a read. A read records its label with the value read; a write names its cell in the
    footprint with the value and the mode; an update is ONE event that reads `v` and writes the operand's
    value; a lock action and a question name their lock and question; an interrupt-control step plans
    its protocol action from the operand's immediates; a private step, a fence and a refused access have
    the private plan. -/
def Wirkungsklasse.plan : Wirkungsklasse → Operand → Int → Plan
  | .lokal, _o, _v => Semantik.plan
  | .ruf, _o, _v => Semantik.plan
  | .lesen m, o, v =>
    ⟨.intern, [⟨.lesen, o.ort, m, v, v⟩], [], fun _ort => false, fun _ort => .na, fun _ort => 0⟩
  | .schreiben m, o, _v =>
    ⟨.intern, [], [o.ort], fun x => decide (x = o.ort), fun _ort => m, fun _ort => o.wert⟩
  | .rmw m, o, v =>
    ⟨.intern, [⟨o.aenderung.art v, o.ort, m, v, o.aenderung.schreibt v o.wert⟩], [], fun _ort => false,
      fun _ort => .na, fun _ort => 0⟩
  | .zaun _m, _o, _v => Semantik.plan
  | .sperre a, o, _v =>
    ⟨.sperre o.sperre a, [], [], fun _ort => false, fun _ort => .na, fun _ort => 0⟩
  | .frage, o, _v => o.fragePlan
  | .verbrauche, _o, _v => Semantik.plan
  | .starte, _o, _v => planMit .starte
  | .beende, _o, _v => planMit .beende
  | .verbinde, o, _v => planMit (.verbinde (.faden o.faden.kind))
  | .wechsle, o, _v => planMit (.wechsle o.faden.kern (.faden o.faden.kind))
  | .maskiere, o, _v => planMit (.maskiere o.unterbrechung.vektor o.unterbrechung.aus)
  | .prioritaet, o, _v => planMit (.prioritaet o.unterbrechung.grenze)
  | .sendeUnterbrechung, o, _v => planMit (.sende o.unterbrechung.vektor o.unterbrechung.kern)
  | .leiteLeitung, o, _v =>
    planMit (.leite o.unterbrechung.leitung o.unterbrechung.kern o.unterbrechung.prioritaet)

/-- **The shape of the plans of a class**: the only plans a step of the class may have. The footprint of the
    step on the shared state is read off the class alone: nothing for a private step, a fence or a refused
    access, one read label for a load, one written cell for a store, one update label for an atomic update,
    one lock action, one question, one interrupt-control action with its immediates. -/
def Wirkungsklasse.Erlaubt : Wirkungsklasse → Plan → Prop
  | .lokal, p => p = Semantik.plan
  | .ruf, p => p = Semantik.plan
  | .lesen m, p =>
    p.aktion = .intern ∧ p.fuss = [] ∧ ∃ (z : Zelle) (v : Int), p.lesen = [⟨.lesen, z, m, v, v⟩]
  | .schreiben m, p =>
    p.aktion = .intern ∧ p.lesen = [] ∧
      ∃ z : Zelle, p.fuss = [z] ∧ p.schreibt z = true ∧ p.modus z = m
  | .rmw m, p =>
    p.aktion = .intern ∧ p.fuss = [] ∧
      ∃ (z : Zelle) (v w : Int), p.lesen = [⟨.rmw, z, m, v, w⟩] ∨ p.lesen = [⟨.lesen, z, m, v, v⟩]
  | .zaun _m, p => p = Semantik.plan
  | .sperre a, p => (∃ l : Nat, p.aktion = .sperre l a) ∧ p.lesen = [] ∧ p.fuss = []
  | .frage, p => (∃ q : Frage, p.aktion = .frage q) ∧ p.lesen = [] ∧ p.fuss = []
  | .verbrauche, p => p = Semantik.plan
  | .starte, p => p.aktion = .starte ∧ p.lesen = [] ∧ p.fuss = []
  | .beende, p => p.aktion = .beende ∧ p.lesen = [] ∧ p.fuss = []
  | .verbinde, p => (∃ k : Kontext, p.aktion = .verbinde k) ∧ p.lesen = [] ∧ p.fuss = []
  | .wechsle, p => (∃ (k : Kern) (d : Kontext), p.aktion = .wechsle k d) ∧ p.lesen = [] ∧ p.fuss = []
  | .maskiere, p =>
    (∃ vektor aus, p.aktion = .maskiere vektor aus) ∧ p.lesen = [] ∧ p.fuss = []
  | .prioritaet, p => (∃ grenze, p.aktion = .prioritaet grenze) ∧ p.lesen = [] ∧ p.fuss = []
  | .sendeUnterbrechung, p =>
    (∃ vektor kern, p.aktion = .sende vektor kern) ∧ p.lesen = [] ∧ p.fuss = []
  | .leiteLeitung, p =>
    (∃ leitung kern prioritaet, p.aktion = .leite leitung kern prioritaet) ∧ p.lesen = [] ∧
      p.fuss = []

/-- Does a step of the class read a value from the memory model? Only a load and an atomic update do. -/
def Wirkungsklasse.liest : Wirkungsklasse → Bool
  | .lesen .. | .rmw .. => true
  | .lokal | .ruf | .schreiben .. | .zaun .. | .sperre .. | .frage | .starte | .beende | .verbinde
  | .wechsle | .verbrauche | .maskiere | .prioritaet | .sendeUnterbrechung | .leiteLeitung => false

/-- The value a step of the class may take from the memory model: any value for a class that reads, and
    the fixed value `0` for every other class (it reads nothing, so nothing is chosen). -/
def Wirkungsklasse.Lesewert (k : Wirkungsklasse) (v : Int) : Prop :=
  k.liest = true ∨ v = 0

/-- **The authority a step of the class needs at the pre-state** (`Zustand.befugt`, `Zustand.fragenBefugt`): the right
    on the ledger for the cell of a load or store (both rights for an atomic update), and the handles of
    the question and the device authority of a register access for a question. An update additionally needs an
    atomic mode: an `rmw` event at `na` is recorded by no consistent memory (`Wohlgeformt.rmw_nicht_na`), so the
    checker's form line `pruefeZugriffsform` refuses exactly the updates whose class is `.rmw .na`; the step of
    such a form therefore takes its refusal branch and halts the frame with a named reason, instead of hanging
    on an event no memory extension accepts. The frame-only classes, the fence, the interrupt-control classes
    and the lock actions need none: a fence orders but accesses nothing, and a lock action that
    the protocol does not allow does not execute, it waits or never runs. -/
def Wirkungsklasse.befugt : Wirkungsklasse → Operand → Zustand → Kontext → Prop
  | .lokal, _o, _s, _c => True
  | .ruf, _o, _s, _c => True
  | .lesen _m, o, s, c => s.befugt c o.ort .lesen
  | .schreiben _m, o, s, c => s.befugt c o.ort .schreiben
  | .rmw m, o, s, c => s.befugt c o.ort .lesen ∧ s.befugt c o.ort .schreiben ∧ m ≠ .na
  | .zaun _m, _o, _s, _c => True
  | .sperre _a, _o, _s, _c => True
  | .frage, o, s, c => ∃ q : Frage, o.frage = some q ∧ s.fragenBefugt c q
  | .verbrauche, _o, _s, _c => True
  | .starte, o, s, c =>
    o.faden.gueltig = true ∧ ∀ g ∈ o.faden.griffe, s.rechte.Gueltig g ∧ ∃ r, s.buchung.haelt c g r
  | .beende, o, _s, _c => o.faden.gueltig = true
  | .verbinde, o, _s, _c => o.faden.gueltig = true
  | .wechsle, o, _s, _c => o.faden.gueltig = true
  | .maskiere, _o, _s, _c => True
  | .prioritaet, _o, _s, _c => True
  | .sendeUnterbrechung, _o, _s, _c => True
  | .leiteLeitung, _o, _s, _c => True

end Gabbro.Core.Ast.Semantik
