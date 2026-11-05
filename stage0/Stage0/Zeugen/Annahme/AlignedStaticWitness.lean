module
public import Stage0.IRBild
import Stage0.SourceWitness.ImagePhases
import all Stage0.Bindung
import all Stage0.Senke.Images.Bild
import all Stage0.Senke.Images.SourceStarts
import all Stage0.Senke.Welt.MainEnv
import all Stage0.Senke.Welt.AnordnungLayouta
import Stage0.Frontend.Witnesses.Constants.SourcePackets
import Stage0.Frontend.Witnesses.Constants.ProgramPackets
import all Grammatik.Parser.Lex.Lexer.Teil1
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
import all Grammatik.Parser.Elab.Konst.Ersetzung
import all Grammatik.Parser.Elab.Konst.ErsetzungTor
import all Grammatik.Parser.Elab.Konst.Scope
import all Grammatik.Parser.Elab.Konst.Replacement
import all Grammatik.Parser.Elab.Konst.Scalar.Model
import all Grammatik.Parser.Elab.Konst.Scalar.Expression
import all Grammatik.Parser.Elab.Konst.Scalar.Names
import all Grammatik.Parser.Elab.Konst.Scalar.Arguments
import all Grammatik.Parser.Elab.Konst.Scalar.KExpr
import all Grammatik.Parser.Elab.Konst.Scalar.Export
import all Grammatik.Parser.Elab.Konst.Values.Expression
import all Grammatik.Parser.Elab.Konst.Values.Quotation
import all Grammatik.Parser.Elab.Konst.Values.Export
import all Stage0.Profil
import all Stage0.Frontend.AliasOrder
import all Stage0.Frontend.Correctness
import all Stage0.Frontend.Environments
import all Stage0.Frontend.EnvironmentsPart1
import all Stage0.Frontend.DependentScopes
import all Stage0.Frontend.DependentScopesa
import all Stage0.Frontend.Functions
import all Stage0.Frontend.Guard
import all Stage0.Frontend.Constants.ConstantScopes
import all Stage0.Frontend.Constants.ConstantMeaning
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

namespace Gabbro.Stage0.AlignedStaticWitness

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Frontend.ConstPhases

set_option maxRecDepth 2000
set_option maxHeartbeats 400000

def text : String :=
  "module aligned16_probe { static VALUE : u32 = 1 aligned 16; impl fn main() -> u64 in 0 .. 100 { return 23; } }"

-- Each cut is an equation of the existing scanner with symbolic suffix and fuel.
private def scanPart0 : ScanPiece ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'a', 'l', 'i', 'g', 'n', 'e', 'd', '1', '6', '_', 'p', 'r', 'o', 'b', 'e', ' ', '{', ' ', 's', 't', 'a', 't', 'i', 'c', ' ', 'V', 'A', 'L', 'U', 'E', ' ', ':', ' '] := by
  let tokens := ((lexL ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'a', 'l', 'i', 'g', 'n', 'e', 'd', '1', '6', '_', 'p', 'r', 'o', 'b', 'e', ' ', '{', ' ', 's', 't', 'a', 't', 'i', 'c', ' ', 'V', 'A', 'L', 'U', 'E', ' ', ':', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 6, equation := ?_ }
  intro rest fuel
  cbv

private def scanPart1 : ScanPiece ['u', '3', '2', ' ', '=', ' ', '1', ' ', 'a', 'l', 'i', 'g', 'n', 'e', 'd', ' ', '1', '6', ';', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '6', '4', ' '] := by
  let tokens := ((lexL ['u', '3', '2', ' ', '=', ' ', '1', ' ', 'a', 'l', 'i', 'g', 'n', 'e', 'd', ' ', '1', '6', ';', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '6', '4', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 10, equation := ?_ }
  intro rest fuel
  cbv

private def scanPart2 : ScanPiece ['i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', '0', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', '2', '3', ';', ' ', '}', ' ', '}'] := by
  let tokens := ((lexL ['i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', '0', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', '2', '3', ';', ' ', '}', ' ', '}']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 8, equation := ?_ }
  intro rest fuel
  cbv

private def scanned := ((scanPart0).append scanPart1).append scanPart2

private theorem lexed : lex text = .ok (scanned.tokens ++ [.ende]) := by
  have characters : text = String.ofList ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'a', 'l', 'i', 'g', 'n', 'e', 'd', '1', '6', '_', 'p', 'r', 'o', 'b', 'e', ' ', '{', ' ', 's', 't', 'a', 't', 'i', 'c', ' ', 'V', 'A', 'L', 'U', 'E', ' ', ':', ' ', 'u', '3', '2', ' ', '=', ' ', '1', ' ', 'a', 'l', 'i', 'g', 'n', 'e', 'd', ' ', '1', '6', ';', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '6', '4', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', '0', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', '2', '3', ';', ' ', '}', ' ', '}'] := by cbv
  rw [characters, lex_ofList]
  exact scanned.lexed (by cbv)

private theorem parsed : (parseTopTief (scanned.tokens ++ [.ende])).toOption.isSome = true := by
  cbv

private def items : List SItemTief :=
  (parseTopTief (scanned.tokens ++ [.ende])).toOption.get parsed

-- Keep the generic normalizer and unused fuel-record fields symbolic.
attribute [local cbv_opaque] Frontend.normalize uFloatLimit lowStufe lowSeqL lowStructL
attribute [local cbv_eval]
  Gabbro.Grammatik.Parser.UebersetzeProben2.seq_select
  Gabbro.Grammatik.Parser.UebersetzeProben2.struct_select
  lowStufe_seq lowStufe_struct

private def sourceInput : SourceInput text := by
  refine {
    tokens := scanned.tokens ++ [.ende]
    items := ?items
    lexed := lexed
    parsed := ?parsed
    prepared := ?prepared
    preparation := ?preparation
    visibility := ?visibility
    compileTime := ?compileTime }
  case parsed => cbv <;> exact Eq.refl _
  case preparation => cbv <;> exact Eq.refl _
  case visibility => cbv
  case compileTime => cbv

private def sourceTail : SourceTail sourceInput := by
  refine {
    metadata := ?metadata
    order := ?order
    ordered := ?ordered
    derived := ?derived
    elaborated := ?elaborated
    aliases := ?aliases
    constants := ?constants }
  case metadata => cbv <;> exact Eq.refl _
  case ordered => cbv <;> exact Eq.refl _
  case elaborated => cbv <;> exact Eq.refl _
  case aliases => cbv
  case constants => cbv

private def compiledHeader : Header text := by
  refine {
    source := sourceFrom sourceInput sourceTail
    sourceEq := by exact sourceFrom_eq sourceInput sourceTail
    expanded := ?expanded
    requirements := ?requirements
    expansion := ?expansion
    constants := ?constants
    ordinary := by cbv
    metadata := by exact sourceTail.metadata
    candidate := ?candidate
    elaborated := ?elaborated }
  case expansion => cbv <;> exact Eq.refl _
  case constants =>
    change Konst.checkSourceConstants sourceInput.original = .ok ()
    unfold Konst.checkSourceConstants
    split
    · exact sourceTail.metadata
    · rfl
  case elaborated => cbv <;> exact Eq.refl _

private theorem function_count : compiledHeader.unit.fns.length = 1 := by cbv

private theorem functions_produced (f : Fin compiledHeader.unit.fns.length) :
    (lowerFnAt compiledHeader.unit f).toOption.isSome = true := by
  rcases f with ⟨index, bound⟩
  have small : index < 1 := by simpa only [function_count] using bound
  have zero : index = 0 := by omega
  subst index
  cbv

private def compiledBody : Body compiledHeader := by
  let functions : Functions compiledHeader.unit := Functions.of_success functions_produced
    (by cbv) (by
      rintro ⟨index, bound⟩
      have small : index < 1 := by simpa only [function_count] using bound
      have zero : index = 0 := by omega
      subst index
      cbv) (by cbv)
  refine {
    functions := functions
    main := ⟨0, by rw [function_count]; decide⟩
    entry := by cbv
    initializers := by cbv
    arrays := ?arrays
    arrayEq := ?arrayEq
    program := ?program
    restored := ?restored
    accepted := ?accepted }
  case arrayEq => cbv <;> exact Eq.refl _
  case restored => cbv <;> exact Eq.refl _
  case accepted => cbv

private def checkedCompilation : {result : Compiled text // compile text = .ok result} :=
  compiledResult compiledHeader compiledBody

private theorem global_count : compiledHeader.unit.globs.length = 1 := by cbv

private theorem global_alignment (g : Fin compiledHeader.unit.globs.length) :
    Senke.globAlign compiledHeader.unit g = 16 := by
  rcases g with ⟨index, bound⟩
  have small : index < 1 := by simpa only [global_count] using bound
  have zero : index = 0 := by omega
  subst index
  cbv

-- Geometry comes from the accepted canonical builder, independently of
-- native arithmetic, concrete emitted bytes or the selected function body.
private theorem emitted_base_grid {src : String} {K : Nat}
    (emitted : Emitted src K) (grid : Nat)
    (divides : grid ∣ Senke.bodenAusrichtung emitted.compiled.unit) :
    grid ∣ emitted.image.Y.lo := by
  have builder := emitted.emission
  generalize chosen : emitted.image = image at builder ⊢
  simp only [Senke.bild] at builder
  split at builder
  · cases builder
  · next preliminary preliminaryEq =>
    split at builder
    · cases builder
    · next actual actualEq =>
      split at builder
      · next accepted =>
        simp only [Except.ok.injEq] at builder
        rw [← builder]
        exact Nat.dvd_trans divides (Senke.alignUp_dvd _ _ (Senke.boden_pos _))
      · exfalso
        revert builder
        repeat' split
        all_goals intro builder; cases builder

private theorem compilation_source : checkedCompilation.val.source = compiledHeader.source :=
  compiledResult_source compiledHeader compiledBody

private theorem compilation_unit : checkedCompilation.val.unit = compiledHeader.unit :=
  compiledResult_unit compiledHeader compiledBody

-- Fix every complete phase value before projecting a finite carrier or
-- layout field. These are results of the existing producers, not snapshots.
private theorem image_target : validateTargetFor ({} : Profil.Options).arch
    ({} : Profil.Options).target (uMembers (pre108 checkedCompilation.val.source.items)) = .ok () := by
  rw [compilation_source]
  cbv

private theorem image_bindings : toreVonFor ({} : Profil.Options).arch
    ({} : Profil.Options).target (uMembers (pre108 checkedCompilation.val.source.items)) = .ok [] := by
  rw [compilation_source]
  cbv

private theorem image_foreigns : checkedCompilation.val.unit.axs = [] := by
  rw [compilation_unit]
  cbv

private def imageTor : (declOf checkedCompilation.val.unit).Ax → Option Senke.TorB :=
  fun _ => none

private def imagePlan : {plan : StartArgument.Plan checkedCompilation.val.unit
      (uMembers (pre108 checkedCompilation.val.source.prepared.elaborierbar)) checkedCompilation.val.main //
    StartArgument.plan checkedCompilation.val.unit
      (uMembers (pre108 checkedCompilation.val.source.prepared.elaborierbar)) checkedCompilation.val.main =
      .ok plan} := by
  refine ⟨?plan, ?made⟩
  case made => cbv <;> exact Eq.refl _

private theorem image_initial : GabbroV.sp0OkB checkedCompilation.val.unit = true := by
  rw [compilation_unit]
  cbv

private def imageArgs : {args : Env (declOf checkedCompilation.val.unit)
      ((declOf checkedCompilation.val.unit).params checkedCompilation.val.main) //
    Senke.mainEnv ((declOf checkedCompilation.val.unit).params checkedCompilation.val.main) = some args} := by
  refine ⟨?args, ?made⟩
  case made => cbv <;> exact Eq.refl _

private def imageEmission : {image : Senke.Bild (declOf checkedCompilation.val.unit) //
    Senke.bild irDurchlaeufe checkedCompilation.val.program (Senke.layU checkedCompilation.val.unit imageTor)
      (List.finRange checkedCompilation.val.unit.fns.length) Fin.val
      (fun g => (checkedCompilation.val.unit.fns[g.val]?.map (·.name)).getD "?")
      checkedCompilation.val.main imageArgs.val
      (imagePlan.val.starts (Senke.initialWorld checkedCompilation.val.unit image_initial))
      64 (Senke.bodenAusrichtung checkedCompilation.val.unit) = .ok image} := by
  refine ⟨?image, ?made⟩
  case made => cbv <;> exact Eq.refl _

-- The shared theorem replays the original emitter with exactly these
-- constructors, retaining its profile, initial world and complete frames.
private def checkedImage : {image : Emitted text 64 // emit text 64 = .ok image} := by
  refine ⟨{
    compiled := checkedCompilation.val
    tor := imageTor
    startPlan := imagePlan.val
    initialValid := image_initial
    args := imageArgs.val
    pointers := imageArgs.property
    image := imageEmission.val
    emission := imageEmission.property }, ?_⟩
  exact ImagePhases.emit_from_phases checkedCompilation.val checkedCompilation.property
    image_target [] image_bindings image_foreigns imageTor rfl imagePlan.val imagePlan.property
    image_initial imageArgs.val imageArgs.property imageEmission.val imageEmission.property

def candidate : Except String (Emitted text 64) := emit text 64

/-- An aligned static elaborates to an image: alignment without a section is
    laid out on the common grid, not refused. -/
theorem candidate_present : candidate.toOption.isSome = true := by
  change (emit text 64).toOption.isSome = true
  rw [checkedImage.property] <;> rfl

def output : Emitted text 64 := candidate.toOption.get candidate_present

private theorem output_selected : output = checkedImage.val := by
  have selected : candidate = .ok output := except_ok_get candidate_present
  have certified : candidate = .ok checkedImage.val := checkedImage.property
  exact Except.ok.inj (selected.symm.trans certified)

theorem globs_one : output.compiled.unit.globs.length = 1 := by
  rw [output_selected]
  change compiledHeader.unit.globs.length = 1
  exact global_count

def g0 : Fin output.compiled.unit.globs.length := ⟨0, by rw [globs_one]; decide⟩

/-- The elaborated static keeps its declared alignment of sixteen. -/
theorem align_sixteen : Senke.globAlign output.compiled.unit g0 = 16 := by
  have aligned : ∀ g : Fin output.compiled.unit.globs.length,
      Senke.globAlign output.compiled.unit g = 16 := by
    rw [output_selected]
    change ∀ g : Fin compiledHeader.unit.globs.length, Senke.globAlign compiledHeader.unit g = 16
    exact global_alignment
  exact aligned g0

/-- The built image base lies on the combined sixteen-grid: the builder aligned it
    up to the required base alignment, which the sixteen-grid divides. -/
theorem base_grid : Nat.lcm 8 16 ∣ output.image.Y.lo := by
  have positive : 0 < Senke.globAlign output.compiled.unit g0 := by
    rw [align_sixteen]
    decide
  have divides := Senke.boden_teilt output.compiled.unit g0 positive
  rw [align_sixteen] at divides
  exact emitted_base_grid output (Nat.lcm 8 16) divides

/-- The aligned global's absolute address is divisible by sixteen (and eight):
    `placed` holds unconditionally for every successfully built image. -/
theorem addr_aligned : 16 ∣ output.image.Y.ga g0 ∧ 8 ∣ output.image.Y.ga g0 := by
  have hpos : 0 < Senke.globAlign output.compiled.unit g0 := by
    rw [align_sixteen]; decide
  have h := output.placed g0 hpos
  rw [align_sixteen] at h
  exact h

/-- The same image satisfies the inherited execution correctness. -/
theorem image_correct [Runner.IR.Kern] [Senke.CloneOK] : output.Correct := output.correct

end Gabbro.Stage0.AlignedStaticWitness
