module
public import Stage0.Zeugen.Annahme.NamedSpace.Image
import all Stage0.Zeugen.Annahme.NamedSpace.Program
import all Stage0.Zeugen.Annahme.NamedSpace.Input
import all Grammatik.Parser.Elab.UebersetzeAllg.TableCapabilities

@[expose] public section
namespace Gabbro.Stage0.NamedSpaceWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
set_option maxRecDepth 2000
set_option maxHeartbeats 400000

attribute [local cbv_opaque] Frontend.normalize Frontend.ConstPhases.compiledResult
attribute [local cbv_eval] Phases.header_unit

def candidate : Except String (Emitted text 64) := emit text 64

theorem candidate_present : candidate.toOption.isSome = true := by
  change (emit (Phases.sourceText false) 64).toOption.isSome = true
  rw [Phases.image_produced]
  rfl

def output : Emitted text 64 := Phases.image false

theorem accepted_image : emit text 64 = .ok output := Phases.image_produced false

def pointerCandidate : Except String (Emitted pointerText 64) := emit pointerText 64

theorem pointer_candidate_present : pointerCandidate.toOption.isSome = true := by
  change (emit (Phases.sourceText true) 64).toOption.isSome = true
  rw [Phases.image_produced]
  rfl

def pointerOutput : Emitted pointerText 64 := Phases.image true

theorem pointer_accepted_image : emit pointerText 64 = .ok pointerOutput := Phases.image_produced true

private theorem pointer_unit : pointerOutput.compiled.unit = Phases.unit true :=
  Phases.image_unit true

private theorem plain_unit : output.compiled.unit = Phases.unit false :=
  Phases.image_unit false

theorem pointer_table_bound : 0 < pointerOutput.compiled.unit.tabs.length := by
  rw [pointer_unit]
  cbv

/-- Both actual source units register a nonzero nominal space without an owner. -/
theorem table_space :
    output.compiled.unit.spaces = ["normal", "sharedData"] ∧
    (output.compiled.unit.tabs[0]?).map (fun table => (table.space, table.owner, table.count)) =
      some (1, none, 2) := by
  rw [plain_unit]
  constructor <;> cbv

/-- The written pointer retains the same space, table identity and exact read right. -/
theorem pointer_space :
    (declOf pointerOutput.compiled.unit).params pointerOutput.compiled.main =
      [.ptr ⟨1, ⟨true, false, none⟩, .table 0⟩] ∧
    ∀ bound : 0 < pointerOutput.compiled.unit.tabs.length,
      (declOf pointerOutput.compiled.unit).capTab 1 0 = some ⟨0, bound⟩ := by
  constructor
  · change (declOf (Phases.compilation true).val.unit).params (Phases.compilation true).val.main = _
    rw [Phases.compilation_parameters]
    cbv
  · rw [pointer_unit]
    intro bound
    cbv

/-- The checked lowerer's own gate refuses a foreign space on the same actual
    source table; no inconsistent function metadata or fabricated image is used. -/
theorem incompatible_space_refused :
    ∀ bound : 0 < pointerOutput.compiled.unit.tabs.length,
      checkedTableCap pointerOutput.compiled.unit 0 0 bound =
        .error "pointer table space is not registered" := by
  rw [pointer_unit]
  intro bound
  cbv

theorem incompatible_table_cap_refused :
    checkedTableCap pointerOutput.compiled.unit 0 0 pointer_table_bound =
      .error "pointer table space is not registered" := incompatible_space_refused pointer_table_bound

/-- Space lookup still rejects a name not declared by either source table. -/
theorem unknown_pointer_space_refused :
    uTypIn [] pointerOutput.compiled.unit.tabs [] pointerOutput.compiled.unit.spaces []
      (.ptr "missing" "r" (.atom "T")) = .error "unknown data space: missing" := by
  rw [pointer_unit]
  cbv

/-- Repeated declarations share an ordinal; repeated binders in one header fail. -/
theorem space_declarations :
    uSpaces [.tableT "A" none (some (.lit 1)) none none false [] (some "Data"),
      .tableT "B" none (some (.lit 1)) none none false [] (some "Data"),
      .tableT "C" none (some (.lit 1)) none none false [] (some "Other")] =
      ["normal", "Data", "Other"] ∧
    parseTabellenKopf 8 [.wort "space", .wort "Data", .wort "space", .wort "Other", .zeichen "{"] =
      .error "duplicate table space binding" := by
  constructor <;> cbv

/-- Missing nominal names are grammar errors, never an implicit normal binding. -/
theorem malformed_space_refused :
    parseTabellenKopf 8 [.wort "space", .zeichen "{"] = .error "name expected" := by cbv

/-- Both binders retain their own field, and a space never declares a linear mark. -/
theorem owner_space_independent :
    parseTabellenKopf 8 [.wort "space", .wort "Data", .wort "owner", .wort "Mark", .zeichen "{"] =
      .ok ((none, none, none, some "Mark", false, some "Data"), [.zeichen "{"]) ∧
    uPruefEigner [] (some "Mark") = .error "owner without declared linear mark: Mark" := by
  constructor <;> cbv

theorem images_correct [Runner.IR.Kern] [Senke.CloneOK] : output.Correct ∧ pointerOutput.Correct :=
  ⟨output.correct, pointerOutput.correct⟩

end Gabbro.Stage0.NamedSpaceWitness
