module

public import Core.Ast.LowLevel.Meaning
public import Core.Annahme.Lokal
public import Core.Ideal.Komposition
public import Core.Ideal.Linearisierung
public import Core.Sicherheit.Regel

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

abbrev Plan := SchrittPlan PUnit Nat UInt8 PUnit
abbrev Unit (k : Katalog) := Maschine.Einheit PUnit Nat UInt8 PUnit (Frame k) PUnit PUnit PUnit (Instruction k)

def entryContext : Kontext := .faden 0

def plan : Plan := ⟨.intern, [], [], fun _ => false, fun _ => .na, fun _ => 0⟩

def Transfer.apply {k : Katalog} (transfer : Transfer k) (c : Kontext) (s : State k) : State k :=
  let frame := s.lokal c
  { s with lokal := Function.update s.lokal c {
      frame with
      pc := frame.pc + 1
      result := some transfer.value
      borrowed := transfer.loan.toList ++ frame.borrowed } }

def Instruction.ideal {k : Katalog} (op : Instruction k) (c : Kontext) (s : State k)
    (_ : PUnit.{1}) (plans : List Plan) (next : State k) : Prop :=
  ∃ transfer, op.evaluate s c = some transfer ∧ plans = [plan] ∧ next = transfer.apply c s

def Instruction.impl {k : Katalog} (op : Instruction k) (c : Kontext) (s : State k)
    (_ : PUnit.{1}) (plans : List Plan) (next : State k) : Prop :=
  match op.evaluate s c with
  | none => False
  | some transfer => plans = [plan] ∧ next = transfer.apply c s

def Instruction.rule {k : Katalog} (op : Instruction k) :
    Regel (State k) Plan PUnit :=
  ⟨op.impl, op.ideal⟩

def head {k : Katalog} (op : Instruction k) (s : State k) (c : Kontext) : Option (Instruction k) :=
  match s.status c with
  | .laeuft =>
    if c = entryContext ∧ (s.lokal c).pc = 0 ∧ (op.evaluate s c).isSome then some op else none
  | .ruht | .beendet _ => none

def system {k : Katalog} (op : Instruction k) :
    MaschinenSystem PUnit Nat UInt8 PUnit (Frame k) PUnit PUnit PUnit (Instruction k) :=
  ⟨Instruction.rule, head op, fun s c => head op s c = none, fun _ _ _ => False⟩

/-- The arrival contract is the only root of the local region names. Contexts
    other than the entry receive no regions. After a restart the entry needs a
    separate recovery contract before it can acquire regions again. -/
def bootData (k : Katalog) (regions : List Strecke) (core : Option Nat) :
    Startdaten UInt8 PUnit (Frame k) PUnit :=
  ⟨fun c => if c = entryContext then { regions := regions } else {},
    fun c => if c = entryContext then .laeuft else .ruht,
    fun n => ⟨if some n = core then some entryContext else none, .nutzer, (),
      fun _ => false, 0, false, []⟩,
    ⟨fun i => decide (i < regions.length), fun _ => 0⟩⟩

def setup (k : Katalog) : Einrichtung PUnit Nat UInt8 PUnit (Frame k) PUnit PUnit :=
  ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ _ _ => False, fun _ _ => True,
    ⟨0, 0⟩, ⟨entryContext, 0, fun _ => bootData k [] (some 0), fun _ _ => 0, id⟩,
    fun _ => 0, fun _ _ _ => none⟩

def image : Bild := ⟨.elf, fun a => if a = 0 then some 0 else none, [0]⟩

def medium (_ : AussenStart) (_ : Nat) : UInt8 := 0

def loaded (k : Katalog) (start : AussenStart) (load : Ladung) : Option (State k) :=
  if load.starts 0 = some 0 ∧ load.bytes 0 = some 0 then
    let d := bootData k start.regions (start.assignment 0)
    some (Zustand.start d.lokal d.status d.kerne d.rechte (setup k).initial (.leer (medium start)))
  else none

def unit {k : Katalog} (op : Instruction k) : Unit k where
  katalog := k
  bild := image
  einrichtung := setup k
  system := system op
  startdaten := fun start => bootData k start.regions (start.assignment 0)
  startmedium := medium
  laden := loaded k
  lokalerBezug := Eq
  stotterLaenge := fun _ => 0
  quelltabellen := ⟨.leer, fun _ _ _ => False⟩

def safetyUnit {k : Katalog} (op : Instruction k) :
    Sicherheit.Einheit PUnit Nat UInt8 PUnit (Frame k) PUnit PUnit PUnit (Instruction k) :=
  ⟨unit op, []⟩

def Elaboriert (k : Katalog) (scope : RegionScope) (tree : Tree form) (E : Unit k) : Prop :=
  ∃ op, elaborate k scope tree = some op ∧ E = unit op

def Bezeichnet {form : Form} (k : Katalog) (scope : RegionScope) (text : Text.RawText) (E : Unit k) : Prop :=
  ∃ tree : Tree form, Parse text tree ∧ Elaboriert k scope tree E

end Gabbro.Core.Ast.LowLevel
