module

public import Core.Ast.Semantik.Quellform
public import Core.Annahme.Annahme

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Gabbro.Core.Text Katalog Maschine Waechter

structure EnvironmentArgs where
  name : Identifier
  abi : DienstAbi
  row : FirmwareZeile
  after : Scope
  rest : UnitBody [] after

def EnvironmentArgs.unit (args : EnvironmentArgs) : Ast.Unit :=
  ⟨args.after, .step (.environment args.name args.abi args.row) args.rest⟩

def environmentInUnit : Surface.Rule .unit EnvironmentArgs where
  tree := EnvironmentArgs.unit
  production := fun args tokens => ∃ head tail,
    tokens = head ++ tail ∧
    (LowLevel.Tree.environment args.name args.abi args.row).production head ∧
    UnitReads [] tail ⟨args.after, args.rest⟩

theorem environmentInUnit_reads (args : EnvironmentArgs) (tokens : List Token)
    (read : environmentInUnit.production args tokens) :
    Category.unit.reads tokens (environmentInUnit.tree args) := by
  obtain ⟨head, tail, rfl, spelling, rest⟩ := read
  change head = _ at spelling
  subst head
  exact .step (.environment args.name args.abi args.row) rest

theorem environmentInUnit_printProduction (args : EnvironmentArgs) :
    environmentInUnit.production args (args.unit.2.printPieces.map PrintedToken.value) := by
  refine ⟨_, _, List.map_append, LowLevel.environment_printTokens args.name args.abi args.row,
    args.rest.printReads⟩

def environmentUnitForm : Quellform .unit EnvironmentArgs where
  produktion := environmentInUnit
  befehl := fun args => .waehleUmgebung args.name args.abi args.row
  position := fun _ => 0

theorem environmentUnit_parse : environmentUnitForm.ParseAussage := by
  intro args text pieces lexed production
  exact (Category.unit.syntax.parse_iff).mpr
    ⟨pieces, lexed, environmentInUnit_reads args _ production⟩

theorem environmentUnit_am_ort : environmentUnitForm.RegelAmOrt :=
  fun _ => rfl

theorem environmentUnit_realisiert : environmentUnitForm.RealisiertAussage :=
  environmentUnitForm.realisiert environmentUnit_am_ort

/-- The declaration's denotation requires the selected row and ABI in the unit
    catalogue, including when later declarations are valid. -/
def EnvironmentUnitAdmissionAussage : Prop :=
  ∀ (p : Plattform) (args : EnvironmentArgs) (E : Einheit),
    Elaboriert (category := .unit) p args.unit E →
    args.row.zugelassen E.katalog args.abi ∧
    ((programm args.unit).environment.map (fun e => e.1.val)).Nodup

theorem environmentUnit_admission : EnvironmentUnitAdmissionAussage := by
  intro p args E meaning
  obtain ⟨rfl, ⟨unique, allowed⟩, _⟩ := meaning
  have present : (args.name, args.abi, args.row) ∈ (programm args.unit).environment :=
    List.mem_cons_self
  exact ⟨allowed _ present, unique⟩

theorem environmentUnit_psci_x86_refused (args : EnvironmentArgs) (row : args.row = .psci)
    (E : Einheit) : ¬ Elaboriert (category := .unit) .x86_64 args.unit E := by
  intro meaning
  have selected := (environmentUnit_admission .x86_64 args E meaning).1
  rw [row] at selected
  cases meaning.1
  have abi := selected.2
  change none = some args.abi at abi
  cases abi

/-- The instruction registers the selected row and advances to the ordinary
    continuation at the next declaration. No outside request is emitted. -/
def EnvironmentUnitTransferAussage : Prop :=
  ∀ (args : EnvironmentArgs) (frame : Rahmen),
    (environmentUnitForm.befehl args).auswerten frame =
      { frame with
        pc := frame.pc + 1
        environment := (args.name, args.abi, args.row) :: frame.environment }

theorem environmentUnit_transfer : EnvironmentUnitTransferAussage :=
  fun _ _ => rfl

/-- A real unit contains the declaration, denotes an accepted machine, and
    reaches the instruction from a catalogue-conforming start. -/
def EnvironmentUnitErfuellbarAussage : Prop :=
  ∃ p start args env text s,
    let E := environmentUnitForm.einheit p args
    environmentInUnit.production args (args.unit.2.printPieces.map PrintedToken.value) ∧
    Ast.Parse (category := .unit) text args.unit ∧ Bezeichnet p .unit text E ∧
    Annahme.Akzeptiert E ∧ Hardware E.katalog env ∧ E.ZulStart env start ∧
    E.system.IErreichbar (I.start E start).2 s ∧ Realisiert environmentUnitForm p args s

def EnvironmentUnitAussage : Prop :=
  environmentUnitForm.ParseAussage ∧ environmentUnitForm.ElaboriertAussage ∧
    environmentUnitForm.RealisiertAussage ∧ EnvironmentUnitAdmissionAussage ∧
    EnvironmentUnitTransferAussage ∧ environmentUnitForm.AnnahmeAussage ∧
    environmentUnitForm.IdealAussage ∧ environmentUnitForm.EinheitAussage ∧
    environmentUnitForm.ImplAussage ∧ environmentUnitForm.ErhaltungsAussage ∧
    EnvironmentUnitErfuellbarAussage

end Gabbro.Core.Ast.Semantik
