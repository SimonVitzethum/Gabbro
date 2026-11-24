module

public import Core.Ast.LowLevel.Mem.Meaning
public import Core.Ast.LowLevel.Execution
public import Core.Annahme.AussenLauf

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

abbrev MemUnit := Maschine.Einheit PUnit Nat UInt8 PUnit MemFrame PUnit PUnit PUnit MemInstruction

def MemFrame.advance (next : MemFrame) (c : Kontext) (s : MemState) : MemState :=
  { s with lokal := Function.update s.lokal c { next with pc := (s.lokal c).pc + 1 } }

def MemInstruction.step (target : ZielDaten) (op : MemInstruction) (c : Kontext) (s : MemState)
    (_ : PUnit.{1}) (plans : List Plan) (next : MemState) : Prop :=
  ∃ frame, op.evaluate target s c = some frame ∧ plans = [plan] ∧ next = frame.advance c s

def MemInstruction.rule (target : ZielDaten) (op : MemInstruction) : Regel MemState Plan PUnit :=
  ⟨op.step target, op.step target⟩

def memHead (target : ZielDaten) (code : List MemInstruction) (s : MemState) (c : Kontext) :
    Option MemInstruction :=
  if c = entryContext then
    match s.status c with
    | .laeuft => do
      let op ← code[(s.lokal c).pc]?
      if (op.evaluate target s c).isSome then some op else none
    | .ruht | .beendet _ => none
  else none

def memBoot (regions : List Strecke) (core : Option Nat) :
    Startdaten UInt8 PUnit MemFrame PUnit :=
  let slots := regions.zipIdx |>.map fun (extent, i) => some (⟨extent, [⟨i, 0⟩]⟩ : MemRegion)
  ⟨fun c => if c = entryContext then { regions := slots } else {},
    fun c => if c = entryContext then .laeuft else .ruht,
    fun n => ⟨if some n = core then some entryContext else none, .nutzer, (),
      fun _ => false, 0, false, []⟩, ⟨fun i => decide (i < regions.length), fun _ => 0⟩⟩

def memSetup : Einrichtung PUnit Nat UInt8 PUnit MemFrame PUnit PUnit :=
  ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ _ _ => False, fun _ _ => True,
    ⟨0, 0⟩, ⟨entryContext, 0, fun _ => memBoot [] (some 0), fun _ _ => 0⟩,
    fun _ => 0, fun _ _ _ => none⟩

def memProgram (k : Katalog) (code : List MemInstruction) : MemUnit :=
  let target := k.plattform.ziel
  { katalog := k
    bild := image
    einrichtung := memSetup
    system := ⟨MemInstruction.rule target, memHead target code,
      fun s c => memHead target code s c = none, fun _ _ _ => False⟩
    startdaten := fun start => memBoot start.regions (start.assignment 0)
    startmedium := medium
    laden := fun start load =>
      if load.starts 0 = some 0 ∧ load.bytes 0 = some 0 then
        let d := memBoot start.regions (start.assignment 0)
        some (Zustand.start d.lokal d.status d.kerne d.rechte memSetup.initial (.leer (medium start)))
      else none
    lokalerBezug := Eq
    stotterLaenge := fun _ => 0
    quelltabellen := ⟨.leer, fun _ _ _ => False⟩ }

def memUnit (k : Katalog) (op : MemInstruction) : MemUnit := memProgram k [op]

def memSafetyUnit (k : Katalog) (op : MemInstruction) :
    Sicherheit.Einheit PUnit Nat UInt8 PUnit MemFrame PUnit PUnit PUnit MemInstruction :=
  ⟨memUnit k op, []⟩

end Gabbro.Core.Ast.LowLevel
