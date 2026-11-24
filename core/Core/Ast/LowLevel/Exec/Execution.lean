module

public import Core.Ast.LowLevel.Exec.Meaning
public import Core.Ast.LowLevel.Execution
public import Core.Annahme.AussenLauf

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

abbrev ExecUnit := Maschine.Einheit PUnit Nat UInt8 PUnit ExecFrame PUnit PUnit PUnit ExecInstruction

def ExecFrame.advance (next : ExecFrame) (c : Kontext) (s : ExecState) : ExecState :=
  { s with lokal := Function.update s.lokal c { next with pc := (s.lokal c).pc + 1 } }

def ExecInstruction.step (op : ExecInstruction) (c : Kontext) (s : ExecState)
    (_ : PUnit.{1}) (plans : List Plan) (next : ExecState) : Prop :=
  ∃ frame, op.evaluate s c = some frame ∧ plans = [plan] ∧ next = frame.advance c s

def ExecInstruction.rule (op : ExecInstruction) : Regel ExecState Plan PUnit :=
  ⟨op.step, op.step⟩

def execHead (code : List ExecInstruction) (s : ExecState) (c : Kontext) :
    Option ExecInstruction :=
  if c = entryContext then
    match s.status c with
    | .laeuft => do
      let op ← code[(s.lokal c).pc]?
      if (op.evaluate s c).isSome then some op else none
    | .ruht | .beendet _ => none
  else none

/-- The arrival contract hands RAM regions; each region backs one abstract
    stack capability. States, the current state and vector entries are
    declared by the program itself, starting from the arrival state. -/
def execBoot (regions : List Strecke) (core : Option Nat) :
    Startdaten UInt8 PUnit ExecFrame PUnit :=
  ⟨fun c => if c = entryContext then
      { pc := 0, stacks := List.range regions.length } else {},
    fun c => if c = entryContext then .laeuft else .ruht,
    fun n => ⟨if some n = core then some entryContext else none, .nutzer, (),
      fun _ => false, 0, false, []⟩, ⟨fun i => decide (i < regions.length), fun _ => 0⟩⟩

def execSetup : Einrichtung PUnit Nat UInt8 PUnit ExecFrame PUnit PUnit :=
  ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ _ _ => False, fun _ _ => True,
    ⟨0, 0⟩, ⟨entryContext, 0, fun _ => execBoot [] (some 0), fun _ _ => 0⟩,
    fun _ => 0, fun _ _ _ => none⟩

def execProgram (k : Katalog) (code : List ExecInstruction) : ExecUnit :=
  { katalog := k
    bild := image
    einrichtung := execSetup
    system := ⟨ExecInstruction.rule, execHead code,
      fun s c => execHead code s c = none, fun _ _ _ => False⟩
    startdaten := fun start => execBoot start.regions (start.assignment 0)
    startmedium := medium
    laden := fun start load =>
      if load.starts 0 = some 0 ∧ load.bytes 0 = some 0 then
        let d := execBoot start.regions (start.assignment 0)
        some (Zustand.start d.lokal d.status d.kerne d.rechte execSetup.initial (.leer (medium start)))
      else none
    lokalerBezug := Eq
    stotterLaenge := fun _ => 0
    quelltabellen := ⟨.leer, fun _ _ _ => False⟩ }

def execUnit (k : Katalog) (op : ExecInstruction) : ExecUnit := execProgram k [op]

def execSafetyUnit (k : Katalog) (op : ExecInstruction) :
    Sicherheit.Einheit PUnit Nat UInt8 PUnit ExecFrame PUnit PUnit PUnit ExecInstruction :=
  ⟨execUnit k op, []⟩

end Gabbro.Core.Ast.LowLevel
