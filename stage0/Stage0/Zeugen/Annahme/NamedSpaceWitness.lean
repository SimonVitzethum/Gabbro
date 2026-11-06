module
public import Stage0.IRBild
import Stage0.SourceWitness.ImagePhases
import Stage0.Frontend.Witnesses.Constants.SourcePackets
import Stage0.Frontend.Witnesses.Constants.ProgramPackets
import all Stage0.Bindung
import all Stage0.Senke.Images.Bild
import all Stage0.Senke.Images.SourceStarts
import all Stage0.Senke.Welt.MainEnv
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
import all Grammatik.Parser.Elab.UebersetzeAllg3.Stufe
import all Grammatik.Parser.Elab.UebersetzeAllg3.Seq
import all Grammatik.Parser.Elab.UebersetzeAllg3.Struct
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section

namespace Gabbro.Stage0.NamedSpaceWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Frontend.ConstPhases
set_option maxRecDepth 2000
set_option maxHeartbeats 400000

-- Space binding is nominal; neither source manufactures an owner mark.
def text : String :=
  "module named_space_probe { table T count 2 space sharedData { slot { v : u32 in 0 .. 100, } } impl fn main() -> u32 in 0 .. 100 effects { reads T.slots } { return T.slots[0].v; } }"

def pointerText : String :=
  "module named_space_pointer_probe { table T count 2 space sharedData { slot { v : u32 in 0 .. 100, } } impl fn main(p : ptr<sharedData, r> T) -> u32 in 0 .. 100 effects { reads p.slots } { return p.slots[0].v; } }"

private def sourceText : Bool → String | false => text | true => pointerText

-- Each packet is produced by the actual phase, before a dependent consumer
-- inspects any field. No expected AST or image is supplied to these producers.
private def scanned : (pointer : Bool) →
    { tokens : List Token // lex (sourceText pointer) = .ok tokens }
  | false => by
    refine ⟨?plainTokens, ?plainLexed⟩
    case plainLexed => cbv <;> exact Eq.refl _
  | true => by
    refine ⟨?pointerTokens, ?pointerLexed⟩
    case pointerLexed => cbv <;> exact Eq.refl _

attribute [local cbv_opaque] Frontend.normalize uFloatLimit lowStufe lowSeqL lowStructL
attribute [local cbv_eval]
  Gabbro.Grammatik.Parser.UebersetzeProben2.seq_select
  Gabbro.Grammatik.Parser.UebersetzeProben2.struct_select
  lowStufe_seq lowStufe_struct

private def sourceInput : (pointer : Bool) → SourceInput (sourceText pointer)
  | false => by
    refine {
      tokens := (scanned false).val
      lexed := (scanned false).property
      items := ?plainItems
      parsed := ?plainParsed
      prepared := ?plainPrepared
      preparation := ?plainPreparation
      visibility := ?plainVisibility
      compileTime := ?plainSafe }
    case plainParsed => cbv <;> exact Eq.refl _
    case plainPreparation => cbv <;> exact Eq.refl _
    case plainVisibility => cbv
    case plainSafe => cbv
  | true => by
    refine {
      tokens := (scanned true).val
      lexed := (scanned true).property
      items := ?pointerItems
      parsed := ?pointerParsed
      prepared := ?pointerPrepared
      preparation := ?pointerPreparation
      visibility := ?pointerVisibility
      compileTime := ?pointerSafe }
    case pointerParsed => cbv <;> exact Eq.refl _
    case pointerPreparation => cbv <;> exact Eq.refl _
    case pointerVisibility => cbv
    case pointerSafe => cbv

private def sourceTail : (pointer : Bool) → SourceTail (sourceInput pointer)
  | false => by
    refine {
      metadata := ?plainMetadata
      order := ?plainOrder
      ordered := ?plainOrdered
      derived := ?plainScopes
      elaborated := ?plainElaborated
      aliases := ?plainAliases
      constants := ?plainConstants }
    case plainMetadata => cbv <;> exact Eq.refl _
    case plainOrdered => cbv <;> exact Eq.refl _
    case plainElaborated => cbv <;> exact Eq.refl _
    case plainAliases => cbv
    case plainConstants => cbv
  | true => by
    refine {
      metadata := ?pointerMetadata
      order := ?pointerOrder
      ordered := ?pointerOrdered
      derived := ?pointerScopes
      elaborated := ?pointerElaborated
      aliases := ?pointerAliases
      constants := ?pointerConstants }
    case pointerMetadata => cbv <;> exact Eq.refl _
    case pointerOrdered => cbv <;> exact Eq.refl _
    case pointerElaborated => cbv <;> exact Eq.refl _
    case pointerAliases => cbv
    case pointerConstants => cbv

private def header : (pointer : Bool) → Header (sourceText pointer)
  | false => by
    refine {
      source := sourceFrom (sourceInput false) (sourceTail false)
      sourceEq := sourceFrom_eq (sourceInput false) (sourceTail false)
      expanded := ?plainExpanded
      requirements := ?plainRequirements
      expansion := ?plainExpansion
      constants := ?plainConstants
      ordinary := by cbv
      metadata := (sourceTail false).metadata
      candidate := ?plainUnit
      elaborated := ?plainElaborated }
    case plainExpansion => cbv <;> exact Eq.refl _
    case plainConstants => cbv <;> exact Eq.refl _
    case plainElaborated => cbv <;> exact Eq.refl _
  | true => by
    refine {
      source := sourceFrom (sourceInput true) (sourceTail true)
      sourceEq := sourceFrom_eq (sourceInput true) (sourceTail true)
      expanded := ?pointerExpanded
      requirements := ?pointerRequirements
      expansion := ?pointerExpansion
      constants := ?pointerConstants
      ordinary := by cbv
      metadata := (sourceTail true).metadata
      candidate := ?pointerUnit
      elaborated := ?pointerElaborated }
    case pointerExpansion => cbv <;> exact Eq.refl _
    case pointerConstants => cbv <;> exact Eq.refl _
    case pointerElaborated => cbv <;> exact Eq.refl _

private theorem function_count (pointer : Bool) : (header pointer).unit.fns.length = 1 := by
  cases pointer <;> cbv

private def main (pointer : Bool) : Fin (header pointer).unit.fns.length :=
  ⟨0, by have count := function_count pointer; omega⟩

private theorem only_main (pointer : Bool) (f : Fin (header pointer).unit.fns.length) :
    f = main pointer := by
  apply Fin.ext
  have bound : f.val < 1 := by simpa only [function_count pointer] using f.isLt
  change f.val = 0
  omega

private def code (pointer : Bool) :
    { value : EnsTy (header pointer).unit (main pointer) ×
        RumpTy (header pointer).unit (main pointer) × ReqTy (header pointer).unit (main pointer) //
      lowerFnAt (header pointer).unit (main pointer) = .ok value } := by
  cases pointer with
  | false =>
    refine ⟨?plainCode, ?plainLowered⟩
    case plainLowered => cbv <;> exact Eq.refl _
  | true =>
    refine ⟨?pointerCode, ?pointerLowered⟩
    case pointerLowered => cbv <;> exact Eq.refl _

private def functions (pointer : Bool) : Functions (header pointer).unit :=
  Functions.of_success (fun f => by
    have same := only_main pointer f
    subst f
    rw [(code pointer).property]
    rfl) (by cases pointer <;> cbv) (fun f => by
      have same := only_main pointer f
      subst f
      cases pointer <;> cbv) (by cases pointer <;> cbv)

private def arrays (pointer : Bool) :
    { value : PLift (∀ item ∈ (sourceInput pointer).original,
        Frontend.ArrayMeaning (header pointer).unit (header pointer).source.scopes item) //
      Frontend.checkArrays (header pointer).unit (header pointer).source.scopes
        (sourceInput pointer).original = .ok value } := by
  cases pointer with
  | false =>
    refine ⟨?plainArrays, ?plainChecked⟩
    case plainChecked => cbv <;> exact Eq.refl _
  | true =>
    refine ⟨?pointerArrays, ?pointerChecked⟩
    case pointerChecked => cbv <;> exact Eq.refl _

private theorem entry_free (pointer : Bool) (f : Fin (header pointer).unit.fns.length) :
    (OldSource.clauses (header pointer).expanded (fnAt (header pointer).unit f).name).any
      OldSource.hasEntry = false := by
  have same := only_main pointer f
  subst f
  cases pointer <;> cbv

private def body (pointer : Bool) : Body (header pointer) where
  functions := functions pointer
  main := main pointer
  entry := by cases pointer <;> cbv
  initializers := by cases pointer <;> cbv
  arrays := (arrays pointer).val
  arrayEq := (arrays pointer).property
  program := (functions pointer).program
  restored := restore_entry_free _ (header pointer).expanded (header pointer).requirements
    (header pointer).unit (functions pointer).program (header pointer).expansion (entry_free pointer)
  accepted := by
    apply accepts_function_results (functions pointer)
    intro invariants pointers foreigns
    cases pointer <;> cbv

private def compilation (pointer : Bool) :
    { result : Compiled (sourceText pointer) // compile (sourceText pointer) = .ok result } :=
  compiledResult (header pointer) (body pointer)

private theorem compilation_source (pointer : Bool) :
    (compilation pointer).val.source = (header pointer).source := compiledResult_source _ _
private theorem compilation_unit (pointer : Bool) :
    (compilation pointer).val.unit = (header pointer).unit := compiledResult_unit _ _

private def tor (pointer : Bool) : (declOf (compilation pointer).val.unit).Ax → Option Senke.TorB :=
  fun _ => none

private def plan (pointer : Bool) :
    { value : StartArgument.Plan (compilation pointer).val.unit
        (uMembers (pre108 (compilation pointer).val.source.prepared.elaborierbar))
        (compilation pointer).val.main //
      StartArgument.plan (compilation pointer).val.unit
        (uMembers (pre108 (compilation pointer).val.source.prepared.elaborierbar))
        (compilation pointer).val.main = .ok value } := by
  cases pointer with
  | false =>
    refine ⟨?plainPlan, ?plainMade⟩
    case plainMade => cbv <;> exact Eq.refl _
  | true =>
    refine ⟨?pointerPlan, ?pointerMade⟩
    case pointerMade => cbv <;> exact Eq.refl _

private theorem initial (pointer : Bool) : GabbroV.sp0OkB (compilation pointer).val.unit = true := by
  rw [compilation_unit]
  cases pointer <;> cbv

private def arguments (pointer : Bool) :
    { value : Env (declOf (compilation pointer).val.unit)
        ((declOf (compilation pointer).val.unit).params (compilation pointer).val.main) //
      Senke.mainEnv ((declOf (compilation pointer).val.unit).params (compilation pointer).val.main) =
        some value } := by
  cases pointer with
  | false =>
    refine ⟨?plainArgs, ?plainMade⟩
    case plainMade => cbv <;> exact Eq.refl _
  | true =>
    refine ⟨?pointerArgs, ?pointerMade⟩
    case pointerMade => cbv <;> exact Eq.refl _

private def emission (pointer : Bool) :
    { value : Senke.Bild (declOf (compilation pointer).val.unit) //
      Senke.bild irDurchlaeufe (compilation pointer).val.program
        (Senke.layU (compilation pointer).val.unit (tor pointer))
        (List.finRange (compilation pointer).val.unit.fns.length) Fin.val
        (fun g => ((compilation pointer).val.unit.fns[g.val]?.map (·.name)).getD "?")
        (compilation pointer).val.main (arguments pointer).val
        ((plan pointer).val.starts (Senke.initialWorld (compilation pointer).val.unit (initial pointer)))
        64 (Senke.bodenAusrichtung (compilation pointer).val.unit) = .ok value } := by
  cases pointer with
  | false =>
    refine ⟨?plainImage, ?plainMade⟩
    case plainMade => cbv <;> exact Eq.refl _
  | true =>
    refine ⟨?pointerImage, ?pointerMade⟩
    case pointerMade => cbv <;> exact Eq.refl _

private def image (pointer : Bool) :
    { result : Emitted (sourceText pointer) 64 // emit (sourceText pointer) 64 = .ok result } := by
  have target : validateTargetFor ({} : Profil.Options).arch ({} : Profil.Options).target
      (uMembers (pre108 (compilation pointer).val.source.items)) = .ok () := by
    rw [compilation_source]
    cases pointer <;> cbv
  have bindings : toreVonFor ({} : Profil.Options).arch ({} : Profil.Options).target
      (uMembers (pre108 (compilation pointer).val.source.items)) = .ok [] := by
    rw [compilation_source]
    cases pointer <;> cbv
  have foreigns : (compilation pointer).val.unit.axs = [] := by
    rw [compilation_unit]
    cases pointer <;> cbv
  refine ⟨{
    compiled := (compilation pointer).val
    tor := tor pointer
    startPlan := (plan pointer).val
    initialValid := initial pointer
    args := (arguments pointer).val
    pointers := (arguments pointer).property
    image := (emission pointer).val
    emission := (emission pointer).property }, ?_⟩
  exact ImagePhases.emit_from_phases (compilation pointer).val (compilation pointer).property
    target [] bindings foreigns (tor pointer) rfl (plan pointer).val (plan pointer).property
    (initial pointer) (arguments pointer).val (arguments pointer).property
    (emission pointer).val (emission pointer).property

def candidate : Except String (Emitted text 64) := emit text 64

theorem candidate_present : candidate.toOption.isSome = true := by
  change (emit (sourceText false) 64).toOption.isSome = true
  rw [(image false).property]
  rfl

def output : Emitted text 64 := candidate.toOption.get candidate_present

theorem accepted_image : emit text 64 = .ok output := except_ok_get candidate_present

def pointerCandidate : Except String (Emitted pointerText 64) := emit pointerText 64

theorem pointer_candidate_present : pointerCandidate.toOption.isSome = true := by
  change (emit (sourceText true) 64).toOption.isSome = true
  rw [(image true).property]
  rfl

def pointerOutput : Emitted pointerText 64 := pointerCandidate.toOption.get pointer_candidate_present

theorem pointer_accepted_image : emit pointerText 64 = .ok pointerOutput :=
  except_ok_get pointer_candidate_present

private theorem output_selected : output = (image false).val :=
  Except.ok.inj (accepted_image.symm.trans (image false).property)
private theorem pointer_output_selected : pointerOutput = (image true).val :=
  Except.ok.inj (pointer_accepted_image.symm.trans (image true).property)

theorem pointer_table_bound : 0 < pointerOutput.compiled.unit.tabs.length := by
  rw [pointer_output_selected]
  cbv

/-- Both actual source units register a nonzero nominal space without an owner. -/
theorem table_space :
    output.compiled.unit.spaces = ["normal", "sharedData"] ∧
    (output.compiled.unit.tabs[0]?).map (fun table => (table.space, table.owner, table.count)) =
      some (1, none, 2) := by
  rw [output_selected]
  change (header false).unit.spaces = _ ∧ ((header false).unit.tabs[0]?).map _ = _
  constructor <;> cbv

/-- The written pointer retains the same space, table identity and exact read right. -/
theorem pointer_space :
    (declOf pointerOutput.compiled.unit).params pointerOutput.compiled.main =
      [.ptr ⟨1, ⟨true, false, none⟩, .table 0⟩] ∧
    ∀ bound : 0 < pointerOutput.compiled.unit.tabs.length,
      (declOf pointerOutput.compiled.unit).capTab 1 0 = some ⟨0, bound⟩ := by
  rw [pointer_output_selected]
  constructor
  · cbv
  · intro bound; cbv

/-- The checked lowerer's own gate refuses a foreign space on the same actual
    source table; no inconsistent function metadata or fabricated image is used. -/
theorem incompatible_space_refused :
    ∀ bound : 0 < pointerOutput.compiled.unit.tabs.length,
      checkedTableCap pointerOutput.compiled.unit 0 0 bound =
        .error "pointer table space is not registered" := by
  rw [pointer_output_selected]
  intro bound
  cbv

theorem incompatible_table_cap_refused :
    checkedTableCap pointerOutput.compiled.unit 0 0 pointer_table_bound =
      .error "pointer table space is not registered" := incompatible_space_refused pointer_table_bound

/-- Space lookup still rejects a name not declared by either source table. -/
theorem unknown_pointer_space_refused :
    uTypIn [] pointerOutput.compiled.unit.tabs [] pointerOutput.compiled.unit.spaces []
      (.ptr "missing" "r" (.atom "T")) = .error "unknown data space: missing" := by
  rw [pointer_output_selected]
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
