module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Phases
import Grammatik.Parser.Elab.UebersetzeAllg3.TransitionCert
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
  recordCheckCode recordCheckStatements checkSampleSubstitute lowStufe lowSeqL lowStructL lowEndL
  Measures.checkedProgram
attribute [local cbv_eval] row_nil row_cons core_bind core_call core_set core_cond
  bound_names_select pointer_source_select start_source_select
  clauses_nil return_none return_empty return_variable
  fold_end_none fold_end_empty fold_end_variable
  recording_block recording_bind recording_nil recording_cons
  sample_binary sample_variable sample_literal
  check_sequence_select check_structure_select lowEndL_succ
  lowStufe_seq lowStufe_struct lowStufe_ende

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

-- Fix the raw body result before transporting it into the declaration's function triple.
private def floorPassingProbeBody :
    {body : Endblock (declOf floorPassingUnitMade.val) (verOf floorPassingUnitMade.val floorPassingProbeIndex) false
      (ctxOf floorPassingUnitMade.val floorPassingProbeIndex) (resOf floorPassingUnitMade.val floorPassingProbeIndex) //
      lowBody floorPassingUnitMade.val floorPassingProbeIndex (fnAt floorPassingUnitMade.val floorPassingProbeIndex).body
        (fnAt floorPassingUnitMade.val floorPassingProbeIndex).ret = .ok body} := by
  refine ⟨?body, ?made⟩
  case made => cbv <;> exact Eq.refl _

private theorem floorPassing_probe_body :
    lowBody floorPassingUnitMade.val floorPassingProbeIndex (fnAt floorPassingUnitMade.val floorPassingProbeIndex).body
      (fnAt floorPassingUnitMade.val floorPassingProbeIndex).ret = .ok floorPassingProbeBody.val :=
  floorPassingProbeBody.property
attribute [local cbv_eval] floorPassing_probe_body

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

-- The wrapper's actual entry call is certified before constructing its statement/body.
private def floorPassingWrapperHead :
    {head : RufKopf floorPassingUnitMade.val floorPassingWrapperIndex
      (ctxOf floorPassingUnitMade.val floorPassingWrapperIndex) (resOf floorPassingUnitMade.val floorPassingWrapperIndex) //
      lowRufKopf floorPassingUnitMade.val floorPassingWrapperIndex (ctxOf floorPassingUnitMade.val floorPassingWrapperIndex)
        (fnAt floorPassingUnitMade.val floorPassingWrapperIndex) (resOf floorPassingUnitMade.val floorPassingWrapperIndex) "g" [] = .ok head} := by
  refine ⟨?head, ?made⟩
  case made => cbv <;> exact Eq.refl _
private theorem floorPassing_wrapper_head :
    lowRufKopf floorPassingUnitMade.val floorPassingWrapperIndex (ctxOf floorPassingUnitMade.val floorPassingWrapperIndex)
      (fnAt floorPassingUnitMade.val floorPassingWrapperIndex) (resOf floorPassingUnitMade.val floorPassingWrapperIndex) "g" [] =
        .ok floorPassingWrapperHead.val := floorPassingWrapperHead.property
attribute [local cbv_eval] floorPassing_wrapper_head

-- Fix the raw body result before transporting it into the declaration's function triple.
private def floorPassingWrapperBody :
    {body : Endblock (declOf floorPassingUnitMade.val) (verOf floorPassingUnitMade.val floorPassingWrapperIndex) false
      (ctxOf floorPassingUnitMade.val floorPassingWrapperIndex) (resOf floorPassingUnitMade.val floorPassingWrapperIndex) //
      lowBody floorPassingUnitMade.val floorPassingWrapperIndex (fnAt floorPassingUnitMade.val floorPassingWrapperIndex).body
        (fnAt floorPassingUnitMade.val floorPassingWrapperIndex).ret = .ok body} := by
  refine ⟨?body, ?made⟩
  case made => cbv <;> exact Eq.refl _

private theorem floorPassing_wrapper_body :
    lowBody floorPassingUnitMade.val floorPassingWrapperIndex (fnAt floorPassingUnitMade.val floorPassingWrapperIndex).body
      (fnAt floorPassingUnitMade.val floorPassingWrapperIndex).ret = .ok floorPassingWrapperBody.val :=
  floorPassingWrapperBody.property
attribute [local cbv_eval] floorPassing_wrapper_body

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
  exact lowerAtPair_of_ok floorPassingUnitMade.val index success (floorPassing_function index)

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

private theorem floorPassing_invariants :
    lowerInvs floorPassingUnitMade.val (List.finRange floorPassingUnitMade.val.invs.length) = .ok () := by cbv
private theorem floorPassing_contracts : contractGate floorPassingUnitMade.val = true := by cbv
attribute [local cbv_eval] floorPassing_invariants floorPassing_contracts

-- This is the canonical assembler with the already certified complete fields.
-- Pin the whole pair before proving its production equality.
private def floorPassingImage :
    Programm (declOf floorPassingUnitMade.val) × List (declOf floorPassingUnitMade.val).Fn :=
  (progOfFn floorPassingUnitMade.val
    (fun f => (floorPassingFunctions f).val.1)
    (fun f => (floorPassingFunctions f).val.2.1)
    (fun f => (floorPassingFunctions f).val.2.2)
    (fun i => lowerInvGut floorPassingUnitMade.val i
      (lowerInvs_all_ok floorPassingUnitMade.val _ i (List.mem_finRange i) floorPassing_invariants))
    (ptrVertragOf floorPassingUnitMade.val)
    (fun a => axVertragOf floorPassingUnitMade.val a (Bool.and_eq_true_iff.mp floorPassing_contracts).2),
    List.finRange floorPassingUnitMade.val.fns.length)

private def floorPassingProgram :
    {result : Programm (declOf floorPassingUnitMade.val) × List (declOf floorPassingUnitMade.val).Fn //
      lowerAllg floorPassingUnitMade.val = .ok result} :=
  ⟨floorPassingImage, by cbv⟩

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

-- Fix the raw body result before transporting it into the declaration's function triple.
private def floorFailingProbeBody :
    {body : Endblock (declOf floorFailingUnitMade.val) (verOf floorFailingUnitMade.val floorFailingProbeIndex) false
      (ctxOf floorFailingUnitMade.val floorFailingProbeIndex) (resOf floorFailingUnitMade.val floorFailingProbeIndex) //
      lowBody floorFailingUnitMade.val floorFailingProbeIndex (fnAt floorFailingUnitMade.val floorFailingProbeIndex).body
        (fnAt floorFailingUnitMade.val floorFailingProbeIndex).ret = .ok body} := by
  refine ⟨?body, ?made⟩
  case made => cbv <;> exact Eq.refl _

private theorem floorFailing_probe_body :
    lowBody floorFailingUnitMade.val floorFailingProbeIndex (fnAt floorFailingUnitMade.val floorFailingProbeIndex).body
      (fnAt floorFailingUnitMade.val floorFailingProbeIndex).ret = .ok floorFailingProbeBody.val :=
  floorFailingProbeBody.property
attribute [local cbv_eval] floorFailing_probe_body

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

-- The wrapper's actual entry call is certified before constructing its statement/body.
private def floorFailingWrapperHead :
    {head : RufKopf floorFailingUnitMade.val floorFailingWrapperIndex
      (ctxOf floorFailingUnitMade.val floorFailingWrapperIndex) (resOf floorFailingUnitMade.val floorFailingWrapperIndex) //
      lowRufKopf floorFailingUnitMade.val floorFailingWrapperIndex (ctxOf floorFailingUnitMade.val floorFailingWrapperIndex)
        (fnAt floorFailingUnitMade.val floorFailingWrapperIndex) (resOf floorFailingUnitMade.val floorFailingWrapperIndex) "g" [] = .ok head} := by
  refine ⟨?head, ?made⟩
  case made => cbv <;> exact Eq.refl _
private theorem floorFailing_wrapper_head :
    lowRufKopf floorFailingUnitMade.val floorFailingWrapperIndex (ctxOf floorFailingUnitMade.val floorFailingWrapperIndex)
      (fnAt floorFailingUnitMade.val floorFailingWrapperIndex) (resOf floorFailingUnitMade.val floorFailingWrapperIndex) "g" [] =
        .ok floorFailingWrapperHead.val := floorFailingWrapperHead.property
attribute [local cbv_eval] floorFailing_wrapper_head

-- Fix the raw body result before transporting it into the declaration's function triple.
private def floorFailingWrapperBody :
    {body : Endblock (declOf floorFailingUnitMade.val) (verOf floorFailingUnitMade.val floorFailingWrapperIndex) false
      (ctxOf floorFailingUnitMade.val floorFailingWrapperIndex) (resOf floorFailingUnitMade.val floorFailingWrapperIndex) //
      lowBody floorFailingUnitMade.val floorFailingWrapperIndex (fnAt floorFailingUnitMade.val floorFailingWrapperIndex).body
        (fnAt floorFailingUnitMade.val floorFailingWrapperIndex).ret = .ok body} := by
  refine ⟨?body, ?made⟩
  case made => cbv <;> exact Eq.refl _

private theorem floorFailing_wrapper_body :
    lowBody floorFailingUnitMade.val floorFailingWrapperIndex (fnAt floorFailingUnitMade.val floorFailingWrapperIndex).body
      (fnAt floorFailingUnitMade.val floorFailingWrapperIndex).ret = .ok floorFailingWrapperBody.val :=
  floorFailingWrapperBody.property
attribute [local cbv_eval] floorFailing_wrapper_body

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
  exact lowerAtPair_of_ok floorFailingUnitMade.val index success (floorFailing_function index)

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

private theorem floorFailing_invariants :
    lowerInvs floorFailingUnitMade.val (List.finRange floorFailingUnitMade.val.invs.length) = .ok () := by cbv
private theorem floorFailing_contracts : contractGate floorFailingUnitMade.val = true := by cbv
attribute [local cbv_eval] floorFailing_invariants floorFailing_contracts

-- This is the canonical assembler with the already certified complete fields.
-- Pin the whole pair before proving its production equality.
private def floorFailingImage :
    Programm (declOf floorFailingUnitMade.val) × List (declOf floorFailingUnitMade.val).Fn :=
  (progOfFn floorFailingUnitMade.val
    (fun f => (floorFailingFunctions f).val.1)
    (fun f => (floorFailingFunctions f).val.2.1)
    (fun f => (floorFailingFunctions f).val.2.2)
    (fun i => lowerInvGut floorFailingUnitMade.val i
      (lowerInvs_all_ok floorFailingUnitMade.val _ i (List.mem_finRange i) floorFailing_invariants))
    (ptrVertragOf floorFailingUnitMade.val)
    (fun a => axVertragOf floorFailingUnitMade.val a (Bool.and_eq_true_iff.mp floorFailing_contracts).2),
    List.finRange floorFailingUnitMade.val.fns.length)

private def floorFailingProgram :
    {result : Programm (declOf floorFailingUnitMade.val) × List (declOf floorFailingUnitMade.val).Fn //
      lowerAllg floorFailingUnitMade.val = .ok result} :=
  ⟨floorFailingImage, by cbv⟩

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
