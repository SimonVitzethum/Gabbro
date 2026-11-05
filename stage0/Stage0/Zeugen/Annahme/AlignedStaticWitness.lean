module
public import Stage0.IRBild
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
    items := items
    lexed := lexed
    parsed := by exact except_ok_get parsed
    prepared := ?prepared
    preparation := ?preparation
    visibility := ?visibility
    compileTime := ?compileTime }
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

private theorem compilation :
    ∃ result : Compiled text, compile text = .ok result ∧ result.unit = compiledHeader.unit :=
  compiled compiledHeader compiledBody

def candidate : Except String (Emitted text 64) := emit text 64

/-- An aligned static elaborates to an image: alignment without a section is
    laid out on the common grid, not refused. -/
theorem candidate_present : candidate.toOption.isSome = true := by decide +kernel

def output : Emitted text 64 := candidate.toOption.get candidate_present

theorem globs_one : output.compiled.unit.globs.length = 1 := by decide +kernel

def g0 : Fin output.compiled.unit.globs.length := ⟨0, by rw [globs_one]; decide⟩

/-- The elaborated static keeps its declared alignment of sixteen. -/
theorem align_sixteen : Senke.globAlign output.compiled.unit g0 = 16 := by decide +kernel

/-- The built image base lies on the combined sixteen-grid: the builder aligned it
    up to the required base alignment, which the sixteen-grid divides. -/
theorem base_grid : Nat.lcm 8 16 ∣ output.image.Y.lo := by decide +kernel

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
