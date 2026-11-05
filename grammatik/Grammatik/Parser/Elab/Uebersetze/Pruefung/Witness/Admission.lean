module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Phases
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Phases
import all Grammatik.Parser.Lex.Lexer.Teil1
import all Grammatik.Parser.Elab.Uebersetze.Folds.Expressions
import all Grammatik.Parser.Elab.Uebersetze.Folds.Expansion
import all Grammatik.Parser.Elab.Uebersetze.Folds.FloatLiterals
import all Grammatik.Parser.Elab.Uebersetze.Branches
import all Grammatik.Parser.Elab.Uebersetze.LoopHeaders
import all Grammatik.Parser.Elab.Uebersetze.Records.Records
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil3
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil4
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil5
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil5Rest
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil7
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil8
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil9
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil10
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil1
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil2
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil3
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil3Values
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil4
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
import all Grammatik.Parser.Elab.UebersetzeAllg3.Ende
import all Grammatik.Parser.Elab.UebersetzeAllg3.Kopf
import all Grammatik.Parser.Elab.UebersetzeAllg3.Seq
import all Grammatik.Parser.Elab.UebersetzeAllg3.Stufe
import all Grammatik.Parser.Elab.UebersetzeAllg3.Struct
import all Grammatik.Parser.Elab.UebersetzeAllg3.Transition
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Export
import all Grammatik.Parser.Elab.Generic.Signatures
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Init.Data.Repr
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
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
import all Init.Data.String.ToSlice
import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.String.Extra
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Legacy
import all Init.Data.String.Termination
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Export
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Ableitung
import all Grammatik.Parser.Elab.Uebersetze.Einheit.Elaboration
import all Grammatik.Parser.Elab.Uebersetze.Einheit.Signatures
import all Grammatik.Parser.Elab.Uebersetze.Akku.ProbenPhases

public section
namespace Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

-- The emitted source stays unchanged; these proof equations select its real callbacks.
attribute [local cbv_opaque] uFloatLimit uAnwReihe uAnwReiheCore
  uAkkuBinder uZeigerAnw uStartNamen elabKlauseln expandReturnCall expandFoldEnd
  recordCheckCode recordCheckStatements checkSampleSubstitute lowStufe lowSeqL lowStructL
  Measures.checkedProgram
attribute [local cbv_eval] row_nil row_cons core_bind core_call core_set core_cond
  bound_names_select pointer_source_select start_source_select
  clauses_nil return_none return_empty return_variable
  fold_end_none fold_end_empty fold_end_variable
  recording_block recording_bind recording_nil recording_cons
  sample_binary sample_variable sample_literal
  check_sequence_select check_structure_select lowStufe_seq lowStufe_struct

-- Infer this exact unit from canonical elaboration, once, before dependent indices.
private def admissionUnitMade : {unit : UProg // elabU (textItems "c" "g") = .ok unit} := by
  refine ⟨?unit, ?made⟩
  case made => cbv <;> exact Eq.refl _

private theorem admission_unit : elabU (textItems "c" "g") = .ok admissionUnitMade.val :=
  admissionUnitMade.property

-- Each function gets a typed success certificate before the whole program is assembled.
private def admissionFunctions (index : Fin admissionUnitMade.val.fns.length) :
    {result : EnsTy admissionUnitMade.val index × RumpTy admissionUnitMade.val index ×
      ReqTy admissionUnitMade.val index // lowerFnAt admissionUnitMade.val index = .ok result} := by
  rcases index with ⟨n, bound⟩
  change n < 4 at bound
  rcases n with _ | n
  · refine ⟨?result, ?made⟩
    case made => cbv <;> exact Eq.refl _
  rcases n with _ | n
  · refine ⟨?result, ?made⟩
    case made => cbv <;> exact Eq.refl _
  rcases n with _ | n
  · refine ⟨?result, ?made⟩
    case made => cbv <;> exact Eq.refl _
  rcases n with _ | n
  · refine ⟨?result, ?made⟩
    case made => cbv <;> exact Eq.refl _
  omega

private theorem admission_function (index : Fin admissionUnitMade.val.fns.length) :
    lowerFnAt admissionUnitMade.val index = .ok (admissionFunctions index).val :=
  (admissionFunctions index).property

private def admissionMeasures :
    {exported : Measures.Export admissionUnitMade.val //
      Measures.lowerMeasures admissionUnitMade.val = .ok exported} := by
  refine ⟨?exported, ?made⟩
  case made => cbv <;> exact Eq.refl _

private theorem admission_measure_gate (P : Programm (declOf admissionUnitMade.val)) :
    Measures.checkedProgram admissionUnitMade.val P =
      .ok (P, List.finRange admissionUnitMade.val.fns.length) := by
  apply check_measure_gate _ admissionMeasures.val admissionMeasures.property
  have all : admissionUnitMade.val.fns.all (fun fn => decide (fn.decreases = none)) = true := by cbv
  intro fn member
  exact of_decide_eq_true (List.all_eq_true.mp all fn member)

attribute [local cbv_eval] admission_function admission_measure_gate

private def admissionProgram :
    {result : Programm (declOf admissionUnitMade.val) × List (declOf admissionUnitMade.val).Fn //
      lowerAllg admissionUnitMade.val = .ok result} := by
  refine ⟨?result, ?made⟩
  case made => cbv <;> exact Eq.refl _

private theorem admission_program :
    lowerAllg admissionUnitMade.val = .ok admissionProgram.val := admissionProgram.property

private def admissionChecks :
    {checks : List (CheckDecl (declOf admissionUnitMade.val)) //
      uCheckDecls admissionUnitMade.val = .ok checks} := by
  refine ⟨?checks, ?made⟩
  case made => cbv <;> exact Eq.refl _

private theorem admission_checks :
    uCheckDecls admissionUnitMade.val = .ok admissionChecks.val := admissionChecks.property

attribute [local cbv_eval] admission_program admission_checks

-- These are computed only on the certified unit/program/check results above.
private theorem admission_facts : CheckWitness admissionUnitMade.val 0 := by
  constructor <;> cbv

private theorem admission_wrapper_refused :
    uCheckDecls {admissionUnitMade.val with
      fns := admissionUnitMade.val.fns.filter fun f => !(strEq f.name "p#tor#g")} =
      .error "function unknown: p#tor#g" := by cbv

private theorem admission_gives_refused :
    (lowerAllg {admissionUnitMade.val with fns := admissionUnitMade.val.fns.map fun f =>
      if strEq f.name "p#probe" then {f with gibt := []} else f}).toOption.isNone = true := by cbv

end Gabbro.Grammatik.Parser.Uebersetze
