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

import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Text

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
private def floorPassingUnitMade : {unit : UProg // elabU (floorItems 2 true true) = .ok unit} := by
  refine ⟨?unit, ?made⟩
  case made => cbv <;> exact Eq.refl _

private theorem floorPassing_unit : elabU (floorItems 2 true true) = .ok floorPassingUnitMade.val :=
  floorPassingUnitMade.property

-- Fix every actual function index before inferring a dependent lowered value.
private abbrev floorPassingFunctionType (index : Fin floorPassingUnitMade.val.fns.length) :=
  EnsTy floorPassingUnitMade.val index × RumpTy floorPassingUnitMade.val index × ReqTy floorPassingUnitMade.val index

private def floorPassingGateIndex : Fin floorPassingUnitMade.val.fns.length :=
  ⟨0, by change 0 < 4; decide⟩

private def floorPassingGateFunction :
    {result : floorPassingFunctionType floorPassingGateIndex //
      lowerFnAt floorPassingUnitMade.val floorPassingGateIndex = .ok result} := by
  refine ⟨?result, ?made⟩
  case made => cbv <;> exact Eq.refl _

private def floorPassingProbeIndex : Fin floorPassingUnitMade.val.fns.length :=
  ⟨1, by change 1 < 4; decide⟩

private def floorPassingProbeFunction :
    {result : floorPassingFunctionType floorPassingProbeIndex //
      lowerFnAt floorPassingUnitMade.val floorPassingProbeIndex = .ok result} := by
  refine ⟨?result, ?made⟩
  case made => cbv <;> exact Eq.refl _

private def floorPassingReportIndex : Fin floorPassingUnitMade.val.fns.length :=
  ⟨2, by change 2 < 4; decide⟩

private def floorPassingReportFunction :
    {result : floorPassingFunctionType floorPassingReportIndex //
      lowerFnAt floorPassingUnitMade.val floorPassingReportIndex = .ok result} := by
  refine ⟨?result, ?made⟩
  case made => cbv <;> exact Eq.refl _

private def floorPassingWrapperIndex : Fin floorPassingUnitMade.val.fns.length :=
  ⟨3, by change 3 < 4; decide⟩

private def floorPassingWrapperFunction :
    {result : floorPassingFunctionType floorPassingWrapperIndex //
      lowerFnAt floorPassingUnitMade.val floorPassingWrapperIndex = .ok result} := by
  refine ⟨?result, ?made⟩
  case made => cbv <;> exact Eq.refl _

-- All four certificates are already closed when this dependent selector is formed.
private def floorPassingFunctions (index : Fin floorPassingUnitMade.val.fns.length) :
    {result : floorPassingFunctionType index // lowerFnAt floorPassingUnitMade.val index = .ok result} :=
  Fin.cases floorPassingGateFunction
    (Fin.cases floorPassingProbeFunction
      (Fin.cases floorPassingReportFunction
        (Fin.cases floorPassingWrapperFunction (fun i => Fin.elim0 i)))) index

private theorem floorPassing_function (index : Fin floorPassingUnitMade.val.fns.length) :
    lowerFnAt floorPassingUnitMade.val index = .ok (floorPassingFunctions index).val :=
  (floorPassingFunctions index).property

private theorem floorPassing_each :
    lowerEach floorPassingUnitMade.val (List.finRange floorPassingUnitMade.val.fns.length) = .ok () := by
  change lowerEach floorPassingUnitMade.val
    [floorPassingGateIndex, floorPassingProbeIndex, floorPassingReportIndex, floorPassingWrapperIndex] = .ok ()
  simp only [lowerEach, floorPassing_function]

private theorem floorPassing_pair (index : Fin floorPassingUnitMade.val.fns.length)
    (success : ∃ result, lowerFnAt floorPassingUnitMade.val index = .ok result) :
    lowerAtPair floorPassingUnitMade.val index success = (floorPassingFunctions index).val := by
  simp only [lowerAtPair, floorPassing_function]

private def floorPassingMeasures :
    {exported : Measures.Export floorPassingUnitMade.val //
      Measures.lowerMeasures floorPassingUnitMade.val = .ok exported} := by
  refine ⟨?exported, ?made⟩
  case made => cbv <;> exact Eq.refl _

private theorem floorPassing_measure_gate (P : Programm (declOf floorPassingUnitMade.val)) :
    @Eq (Except String (Programm (declOf floorPassingUnitMade.val) × List (declOf floorPassingUnitMade.val).Fn))
      (Measures.checkedProgram floorPassingUnitMade.val P)
      (.ok (P, List.finRange floorPassingUnitMade.val.fns.length)) := by
  apply check_measure_gate _ floorPassingMeasures.val floorPassingMeasures.property
  have all : floorPassingUnitMade.val.fns.all (fun fn => decide (fn.decreases = none)) = true := by cbv
  intro fn member
  exact of_decide_eq_true (List.all_eq_true.mp all fn member)

section floorPassingAssembly
attribute [local cbv_opaque] lowerFnAt lowerEach lowerAtPair
attribute [local cbv_eval] floorPassing_function floorPassing_each floorPassing_pair floorPassing_measure_gate

private def floorPassingProgram :
    {result : Programm (declOf floorPassingUnitMade.val) × List (declOf floorPassingUnitMade.val).Fn //
      lowerAllg floorPassingUnitMade.val = .ok result} := by
  refine ⟨?result, ?made⟩
  case made => cbv <;> exact Eq.refl _

private theorem floorPassing_program :
    lowerAllg floorPassingUnitMade.val = .ok floorPassingProgram.val := floorPassingProgram.property

private def floorPassingChecks :
    {checks : List (CheckDecl (declOf floorPassingUnitMade.val)) //
      uCheckDecls floorPassingUnitMade.val = .ok checks} := by
  refine ⟨?checks, ?made⟩
  case made => cbv <;> exact Eq.refl _

private theorem floorPassing_checks :
    uCheckDecls floorPassingUnitMade.val = .ok floorPassingChecks.val := floorPassingChecks.property

attribute [local cbv_eval] floorPassing_program floorPassing_checks

-- These are computed only on the certified unit/program/check results above.
private theorem floorPassing_facts : CheckWitness floorPassingUnitMade.val 1 := by
  constructor <;> cbv

end floorPassingAssembly

-- Infer this exact unit from canonical elaboration, once, before dependent indices.
private def floorFailingUnitMade : {unit : UProg // elabU (floorItems 4 true true) = .ok unit} := by
  refine ⟨?unit, ?made⟩
  case made => cbv <;> exact Eq.refl _

private theorem floorFailing_unit : elabU (floorItems 4 true true) = .ok floorFailingUnitMade.val :=
  floorFailingUnitMade.property

-- Fix every actual function index before inferring a dependent lowered value.
private abbrev floorFailingFunctionType (index : Fin floorFailingUnitMade.val.fns.length) :=
  EnsTy floorFailingUnitMade.val index × RumpTy floorFailingUnitMade.val index × ReqTy floorFailingUnitMade.val index

private def floorFailingGateIndex : Fin floorFailingUnitMade.val.fns.length :=
  ⟨0, by change 0 < 4; decide⟩

private def floorFailingGateFunction :
    {result : floorFailingFunctionType floorFailingGateIndex //
      lowerFnAt floorFailingUnitMade.val floorFailingGateIndex = .ok result} := by
  refine ⟨?result, ?made⟩
  case made => cbv <;> exact Eq.refl _

private def floorFailingProbeIndex : Fin floorFailingUnitMade.val.fns.length :=
  ⟨1, by change 1 < 4; decide⟩

private def floorFailingProbeFunction :
    {result : floorFailingFunctionType floorFailingProbeIndex //
      lowerFnAt floorFailingUnitMade.val floorFailingProbeIndex = .ok result} := by
  refine ⟨?result, ?made⟩
  case made => cbv <;> exact Eq.refl _

private def floorFailingReportIndex : Fin floorFailingUnitMade.val.fns.length :=
  ⟨2, by change 2 < 4; decide⟩

private def floorFailingReportFunction :
    {result : floorFailingFunctionType floorFailingReportIndex //
      lowerFnAt floorFailingUnitMade.val floorFailingReportIndex = .ok result} := by
  refine ⟨?result, ?made⟩
  case made => cbv <;> exact Eq.refl _

private def floorFailingWrapperIndex : Fin floorFailingUnitMade.val.fns.length :=
  ⟨3, by change 3 < 4; decide⟩

private def floorFailingWrapperFunction :
    {result : floorFailingFunctionType floorFailingWrapperIndex //
      lowerFnAt floorFailingUnitMade.val floorFailingWrapperIndex = .ok result} := by
  refine ⟨?result, ?made⟩
  case made => cbv <;> exact Eq.refl _

-- All four certificates are already closed when this dependent selector is formed.
private def floorFailingFunctions (index : Fin floorFailingUnitMade.val.fns.length) :
    {result : floorFailingFunctionType index // lowerFnAt floorFailingUnitMade.val index = .ok result} :=
  Fin.cases floorFailingGateFunction
    (Fin.cases floorFailingProbeFunction
      (Fin.cases floorFailingReportFunction
        (Fin.cases floorFailingWrapperFunction (fun i => Fin.elim0 i)))) index

private theorem floorFailing_function (index : Fin floorFailingUnitMade.val.fns.length) :
    lowerFnAt floorFailingUnitMade.val index = .ok (floorFailingFunctions index).val :=
  (floorFailingFunctions index).property

private theorem floorFailing_each :
    lowerEach floorFailingUnitMade.val (List.finRange floorFailingUnitMade.val.fns.length) = .ok () := by
  change lowerEach floorFailingUnitMade.val
    [floorFailingGateIndex, floorFailingProbeIndex, floorFailingReportIndex, floorFailingWrapperIndex] = .ok ()
  simp only [lowerEach, floorFailing_function]

private theorem floorFailing_pair (index : Fin floorFailingUnitMade.val.fns.length)
    (success : ∃ result, lowerFnAt floorFailingUnitMade.val index = .ok result) :
    lowerAtPair floorFailingUnitMade.val index success = (floorFailingFunctions index).val := by
  simp only [lowerAtPair, floorFailing_function]

private def floorFailingMeasures :
    {exported : Measures.Export floorFailingUnitMade.val //
      Measures.lowerMeasures floorFailingUnitMade.val = .ok exported} := by
  refine ⟨?exported, ?made⟩
  case made => cbv <;> exact Eq.refl _

private theorem floorFailing_measure_gate (P : Programm (declOf floorFailingUnitMade.val)) :
    @Eq (Except String (Programm (declOf floorFailingUnitMade.val) × List (declOf floorFailingUnitMade.val).Fn))
      (Measures.checkedProgram floorFailingUnitMade.val P)
      (.ok (P, List.finRange floorFailingUnitMade.val.fns.length)) := by
  apply check_measure_gate _ floorFailingMeasures.val floorFailingMeasures.property
  have all : floorFailingUnitMade.val.fns.all (fun fn => decide (fn.decreases = none)) = true := by cbv
  intro fn member
  exact of_decide_eq_true (List.all_eq_true.mp all fn member)

section floorFailingAssembly
attribute [local cbv_opaque] lowerFnAt lowerEach lowerAtPair
attribute [local cbv_eval] floorFailing_function floorFailing_each floorFailing_pair floorFailing_measure_gate

private def floorFailingProgram :
    {result : Programm (declOf floorFailingUnitMade.val) × List (declOf floorFailingUnitMade.val).Fn //
      lowerAllg floorFailingUnitMade.val = .ok result} := by
  refine ⟨?result, ?made⟩
  case made => cbv <;> exact Eq.refl _

private theorem floorFailing_program :
    lowerAllg floorFailingUnitMade.val = .ok floorFailingProgram.val := floorFailingProgram.property

private def floorFailingChecks :
    {checks : List (CheckDecl (declOf floorFailingUnitMade.val)) //
      uCheckDecls floorFailingUnitMade.val = .ok checks} := by
  refine ⟨?checks, ?made⟩
  case made => cbv <;> exact Eq.refl _

private theorem floorFailing_checks :
    uCheckDecls floorFailingUnitMade.val = .ok floorFailingChecks.val := floorFailingChecks.property

attribute [local cbv_eval] floorFailing_program floorFailing_checks

-- These are computed only on the certified unit/program/check results above.
private theorem floorFailing_facts : CheckWitness floorFailingUnitMade.val 1 := by
  constructor <;> cbv

end floorFailingAssembly

private theorem floor_absent_refused : (elabU (floorItems 2 false false)).toOption.isNone = true := by cbv

private def floorBypassUnit : {unit : UProg // elabU (floorItems 4 true false) = .ok unit} := by
  refine ⟨?unit, ?made⟩
  case made => cbv <;> exact Eq.refl _

private theorem floor_bypass_report :
    (floorBypassUnit.val.fns.find? (fun f => strEq f.name "p#report#0")).map (·.ret) =
      some (.bool (.and (.var "v") (.var "f0"))) := by cbv

end Gabbro.Grammatik.Parser.Uebersetze
