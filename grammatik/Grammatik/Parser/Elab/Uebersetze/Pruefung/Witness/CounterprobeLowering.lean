module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.CounterprobeUnits
import Grammatik.Parser.Elab.UebersetzeAllg3.TransitionCert
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Phases
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Calls
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Units
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Heads
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Assembly
import all Init.Data.List.MapIdx
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

import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.CounterprobeText
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.CounterprobeUnits
import Grammatik.Parser.Elab.UebersetzeAllg3.FunctionResults
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.CounterprobeBodies

public section
namespace Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

-- The emitted source stays unchanged; these proof equations select its real callbacks.
attribute [local cbv_opaque] uFloatLimit uAnwReihe uAnwReiheCore
  uAkkuBinder uZeigerAnw uStartNamen elabKlauseln expandReturnCall expandFoldEnd
  recordCheckCode recordCheckStatements checkSampleSubstitute lowStufe lowSeqL lowStructL lowEndL
  Measures.checkedProgram lowRufKopf lowCallArgOneL lowCallArgsAuxL withErg lowErg lowEnd
attribute [local cbv_eval] row_nil row_cons core_bind core_call core_set core_cond
  bound_names_select pointer_source_select start_source_select
  clauses_nil return_none return_empty return_variable
  fold_end_none fold_end_empty fold_end_variable
  recording_block recording_bind recording_nil recording_cons
  sample_binary sample_variable sample_literal
  check_sequence_select check_structure_select lowEndL_succ
  lowStufe_seq lowStufe_struct lowStufe_ende
  check_argument_bool check_argument_integer check_arguments_nil check_arguments_cons
  check_result_select check_return_empty check_return_bool check_end_empty check_end_bool

attribute [local cbv_eval] admission_name_self admission_mark_self

-- These are the three actual mutual branches used below: numeric parameter /
-- literal, comparison, and Bool variable. Select their canonical equations
-- rather than reducing the well-founded mutual implementation at a concrete unit.
attribute [local cbv_eval] lowWertE.eq_def lowCmp.eq_def lowEns.eq_def

-- Construct the complete return at abstract carriers, before any fixture Fn is
-- substituted. Keep both the real result-type equality and resource permutation.
private def counterprobe_boolean_end (u : UProg) (caller : Fin u.fns.length)
    (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (source : UEns)
    (result : (fnAt u caller).ergTy = some .bool)
    (read : {term : Expr (declOf u) Γ Λ .bool // lowEns u Γ Λ fn none source = .ok term})
    (ready : decide (Λ.Perm (verOf u caller).ende) = true) :
    {ending : Endblock (declOf u) (verOf u caller) false Γ Λ //
      lowEnd u caller Γ Λ fn (.bool source) = .ok ending} := by
have returned : ∃ value : ErgExpr (declOf u) Γ Λ (verOf u caller).erg,
    lowErg u caller Γ Λ fn (.bool source) = .ok value := by
  rw [check_return_bool]
  split <;> simp_all [read.property]
obtain ⟨value, produced⟩ := returned
refine ⟨Endblock.ret value (of_decide_eq_true ready), ?_⟩
rw [check_end_bool, produced]
simp only [dif_pos ready]

private def sondeIndex0 : Fin sondeUnitMade.val.fns.length :=
  ⟨0, by rw [sonde_function_count]; decide⟩
private def sondeIndex1 : Fin sondeUnitMade.val.fns.length :=
  ⟨1, by rw [sonde_function_count]; decide⟩
private def sondeIndex2 : Fin sondeUnitMade.val.fns.length :=
  ⟨2, by rw [sonde_function_count]; decide⟩
private def sondeIndex3 : Fin sondeUnitMade.val.fns.length :=
  ⟨3, by rw [sonde_function_count]; decide⟩
private def sondeIndex4 : Fin sondeUnitMade.val.fns.length :=
  ⟨4, by rw [sonde_function_count]; decide⟩
private def sondeIndex5 : Fin sondeUnitMade.val.fns.length :=
  ⟨5, by rw [sonde_function_count]; decide⟩

private theorem sonde_call_data : CheckCallUnit sondeUnitMade.val := by
  have headers : sondeUnitMade.val.fns.all (fun fn =>
      decide (fn.boden = none ∧ fn.leiht = [] ∧ fn.bewegt = [] ∧ fn.praegt = [])) = true := by cbv
  exact ⟨rfl, rfl, rfl, fun fn member =>
    of_decide_eq_true (List.all_eq_true.mp headers fn member)⟩

private theorem sonde_call_ready (caller callee : Fin sondeUnitMade.val.fns.length)
    (Λ : List (Res (declOf sondeUnitMade.val))) (takes : (fnAt sondeUnitMade.val callee).nimmt = []) :
    CheckCallGuards sondeUnitMade.val caller callee Λ :=
  check_unit_call_ready sondeUnitMade.val sonde_call_data caller callee Λ takes

private theorem sonde_gate_call (caller : Fin sondeUnitMade.val.fns.length)
    (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf sondeUnitMade.val))) (source : List UArg) :
    lowRufKopf sondeUnitMade.val caller Γ fn Λ "g" source =
      (lowCallArgsAuxL sondeUnitMade.val caller Γ fn Λ (fnAt sondeUnitMade.val sondeIndex0).kinds
        ((fnAt sondeUnitMade.val sondeIndex0).params.map (·.2)) source).map
        (fun arguments => check_call_head sondeUnitMade.val caller sondeIndex0 Γ Λ
          (check_arguments_cast sondeUnitMade.val Γ Λ (params_eq sondeUnitMade.val sondeIndex0) arguments)
          (sonde_call_ready caller sondeIndex0 Λ rfl)) := by
  have found : fnIdx sondeUnitMade.val.fns "g" = .ok sondeIndex0 := by cbv
  exact check_call_phase sondeUnitMade.val caller sondeIndex0 Γ fn Λ "g" source found
    (sonde_call_ready caller sondeIndex0 Λ rfl)

private theorem sonde_report_call (caller : Fin sondeUnitMade.val.fns.length)
    (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf sondeUnitMade.val))) (source : List UArg) :
    lowRufKopf sondeUnitMade.val caller Γ fn Λ "p#report#0" source =
      (lowCallArgsAuxL sondeUnitMade.val caller Γ fn Λ (fnAt sondeUnitMade.val sondeIndex3).kinds
        ((fnAt sondeUnitMade.val sondeIndex3).params.map (·.2)) source).map
        (fun arguments => check_call_head sondeUnitMade.val caller sondeIndex3 Γ Λ
          (check_arguments_cast sondeUnitMade.val Γ Λ (params_eq sondeUnitMade.val sondeIndex3) arguments)
          (sonde_call_ready caller sondeIndex3 Λ rfl)) := by
  have found : fnIdx sondeUnitMade.val.fns "p#report#0" = .ok sondeIndex3 := by cbv
  exact check_call_phase sondeUnitMade.val caller sondeIndex3 Γ fn Λ "p#report#0" source found
    (sonde_call_ready caller sondeIndex3 Λ rfl)

private theorem sonde_external_call (caller : Fin sondeUnitMade.val.fns.length)
    (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf sondeUnitMade.val))) (source : List UArg) :
    lowRufKopf sondeUnitMade.val caller Γ fn Λ "ext" source =
      (lowCallArgsAuxL sondeUnitMade.val caller Γ fn Λ (fnAt sondeUnitMade.val sondeIndex1).kinds
        ((fnAt sondeUnitMade.val sondeIndex1).params.map (·.2)) source).map
        (fun arguments => check_call_head sondeUnitMade.val caller sondeIndex1 Γ Λ
          (check_arguments_cast sondeUnitMade.val Γ Λ (params_eq sondeUnitMade.val sondeIndex1) arguments)
          (sonde_call_ready caller sondeIndex1 Λ rfl)) := by
  have found : fnIdx sondeUnitMade.val.fns "ext" = .ok sondeIndex1 := by cbv
  exact check_call_phase sondeUnitMade.val caller sondeIndex1 Γ fn Λ "ext" source found
    (sonde_call_ready caller sondeIndex1 Λ rfl)

attribute [local cbv_eval] sonde_gate_call sonde_report_call sonde_external_call

private theorem sonde_header0 : PlainFunctionHeader sondeUnitMade.val sondeIndex0 := by
  constructor <;> cbv

private def sondeBody0 : {body : PlainFunctionBody sondeUnitMade.val sondeIndex0 //
    lowBody sondeUnitMade.val sondeIndex0 (fnAt sondeUnitMade.val sondeIndex0).body
      (fnAt sondeUnitMade.val sondeIndex0).ret = .ok body} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private def sondeFunction0 := lowerFnAt_from_body sonde_header0 sondeBody0

private theorem sonde_header1 : PlainFunctionHeader sondeUnitMade.val sondeIndex1 := by
  constructor <;> cbv

private def sondeBody1 : {body : PlainFunctionBody sondeUnitMade.val sondeIndex1 //
    lowBody sondeUnitMade.val sondeIndex1 (fnAt sondeUnitMade.val sondeIndex1).body
      (fnAt sondeUnitMade.val sondeIndex1).ret = .ok body} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private def sondeFunction1 := lowerFnAt_from_body sonde_header1 sondeBody1

-- Split the actual probe at each binding before the dependent call continuation.
private abbrev sondeProbeFn0 := fnAt sondeUnitMade.val sondeIndex2
private abbrev sondeProbeCtx0 := ctxOf sondeUnitMade.val sondeIndex2
private abbrev sondeProbeResources := resOf sondeUnitMade.val sondeIndex2
private def sondeProbeReturn : URet := .bool (.var "#checkReport")
private def sondeProbeCall : UStmt := .bindCall "#checkReport" "p#report#0"
  [.val (.param "#checkSample#0"), .bval (.var "#checkVerdict")]
private def sondeProbeSample : UStmt := .bind "#checkSample#0" none (.param "x")
private def sondeProbeVerdict : UStmt := .bindB "#checkVerdict" (.cmp "<" (.param "x") (.lit 0))
private def sondeProbeAnnotation : Option (Int × Int) := some (0, 18446744073709551615)

private theorem sonde_probe_body : sondeProbeFn0.body =
    [.bind "x" sondeProbeAnnotation (.lit 3), sondeProbeVerdict, sondeProbeSample, sondeProbeCall] := by cbv
private theorem sonde_probe_return : sondeProbeFn0.ret = sondeProbeReturn := by cbv

private def sondeProbeInput : {side : LowSide sondeUnitMade.val sondeProbeCtx0 sondeProbeResources //
    lowBindWert sondeUnitMade.val sondeProbeCtx0 sondeProbeResources sondeProbeFn0
      sondeProbeAnnotation (.lit 3) = .ok side} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private abbrev sondeProbeCtx1 := .int sondeProbeInput.val.range.1 sondeProbeInput.val.range.2 :: sondeProbeCtx0
private abbrev sondeProbeFn1 := sondeProbeFn0.mitBindung "x" sondeProbeInput.val.range

private def sondeProbePredicate : {term : Expr (declOf sondeUnitMade.val) sondeProbeCtx1 sondeProbeResources .bool //
    lowEns sondeUnitMade.val sondeProbeCtx1 sondeProbeResources sondeProbeFn1 none
      (.cmp "<" (.param "x") (.lit 0)) = .ok term} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private abbrev sondeProbeCtx2 := .bool :: sondeProbeCtx1
private abbrev sondeProbeFn2 := sondeProbeFn1.mitBindungB "#checkVerdict"

private def sondeProbeSampleValue : {side : LowSide sondeUnitMade.val sondeProbeCtx2 sondeProbeResources //
    lowBindWert sondeUnitMade.val sondeProbeCtx2 sondeProbeResources sondeProbeFn2 none (.param "x") = .ok side} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private abbrev sondeProbeCtx3 := .int sondeProbeSampleValue.val.range.1 sondeProbeSampleValue.val.range.2 :: sondeProbeCtx2
private abbrev sondeProbeFn3 := sondeProbeFn2.mitBindung "#checkSample#0" sondeProbeSampleValue.val.range

-- Certify the complete recorded argument list before transporting it to the
-- declaration's parameter type or constructing the call permission proof.
private def sondeProbeArguments : {arguments : Args (declOf sondeUnitMade.val)
      sondeProbeCtx3 sondeProbeResources ((fnAt sondeUnitMade.val sondeIndex3).params.map (·.2)) //
    lowCallArgsAuxL sondeUnitMade.val sondeIndex2 sondeProbeCtx3 sondeProbeFn3 sondeProbeResources
      (fnAt sondeUnitMade.val sondeIndex3).kinds ((fnAt sondeUnitMade.val sondeIndex3).params.map (·.2))
      [.val (.param "#checkSample#0"), .bval (.var "#checkVerdict")] = .ok arguments} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private def sondeProbeHead : {head : RufKopf sondeUnitMade.val sondeIndex2 sondeProbeCtx3 sondeProbeResources //
    lowRufKopf sondeUnitMade.val sondeIndex2 sondeProbeCtx3 sondeProbeFn3 sondeProbeResources
      "p#report#0" [.val (.param "#checkSample#0"), .bval (.var "#checkVerdict")] = .ok head} := by
  refine ⟨check_call_head sondeUnitMade.val sondeIndex2 sondeIndex3 sondeProbeCtx3 sondeProbeResources
    (check_arguments_cast sondeUnitMade.val sondeProbeCtx3 sondeProbeResources
      (params_eq sondeUnitMade.val sondeIndex3) sondeProbeArguments.val)
    (sonde_call_ready sondeIndex2 sondeIndex3 sondeProbeResources rfl), ?_⟩
  simp only [sonde_report_call, sondeProbeArguments.property, Except.map]
private theorem sonde_probe_result : (declOf sondeUnitMade.val).erg sondeProbeHead.val.callee = some .bool := by cbv
private theorem sonde_probe_reason : (declOf sondeUnitMade.val).gruende sondeProbeHead.val.callee = 0 := by cbv

private def sondeProbeAnswer : {term : Expr (declOf sondeUnitMade.val) (.bool :: sondeProbeCtx3)
      (nach (declOf sondeUnitMade.val) sondeProbeHead.val.callee sondeProbeResources) .bool //
    lowEns sondeUnitMade.val (.bool :: sondeProbeCtx3)
      (nach (declOf sondeUnitMade.val) sondeProbeHead.val.callee sondeProbeResources)
      (sondeProbeFn3.mitTy "#checkReport" .bool) none (.var "#checkReport") = .ok term} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private theorem sonde_probe_return_type : (fnAt sondeUnitMade.val sondeIndex2).ergTy = some .bool := by cbv
private theorem sonde_probe_return_ready :
    decide ((nach (declOf sondeUnitMade.val) sondeProbeHead.val.callee sondeProbeResources).Perm
      (verOf sondeUnitMade.val sondeIndex2).ende) = true := by cbv

private def sondeProbeEnding : {ending : Endblock (declOf sondeUnitMade.val) (verOf sondeUnitMade.val sondeIndex2)
      false (.bool :: sondeProbeCtx3) (nach (declOf sondeUnitMade.val) sondeProbeHead.val.callee sondeProbeResources) //
    lowEnd sondeUnitMade.val sondeIndex2 (.bool :: sondeProbeCtx3)
      (nach (declOf sondeUnitMade.val) sondeProbeHead.val.callee sondeProbeResources)
      (sondeProbeFn3.mitTy "#checkReport" .bool) sondeProbeReturn = .ok ending} :=
  counterprobe_boolean_end sondeUnitMade.val sondeIndex2 (.bool :: sondeProbeCtx3)
    (nach (declOf sondeUnitMade.val) sondeProbeHead.val.callee sondeProbeResources)
    (sondeProbeFn3.mitTy "#checkReport" .bool) (.var "#checkReport")
    sonde_probe_return_type sondeProbeAnswer sonde_probe_return_ready

private def sondeProbeCallBody := counterprobe_body_call sondeUnitMade.val sondeIndex2
  sondeProbeCtx3 sondeProbeFn3 sondeProbeResources "#checkReport" "p#report#0"
  [.val (.param "#checkSample#0"), .bval (.var "#checkVerdict")] sondeProbeReturn
  sondeProbeHead sonde_probe_result sonde_probe_reason sondeProbeEnding
private def sondeProbeSampleBody := counterprobe_body_integer sondeUnitMade.val sondeIndex2
  sondeProbeCtx2 sondeProbeFn2 2 sondeProbeResources "#checkSample#0" none (.param "x")
  [sondeProbeCall] sondeProbeReturn sondeProbeSampleValue sondeProbeCallBody
private def sondeProbeVerdictBody := counterprobe_body_boolean sondeUnitMade.val sondeIndex2
  sondeProbeCtx1 sondeProbeFn1 3 sondeProbeResources "#checkVerdict" (.cmp "<" (.param "x") (.lit 0))
  [sondeProbeSample, sondeProbeCall] sondeProbeReturn sondeProbePredicate sondeProbeSampleBody
private def sondeProbeCompleteBody := counterprobe_body_integer sondeUnitMade.val sondeIndex2
  sondeProbeCtx0 sondeProbeFn0 4 sondeProbeResources "x" sondeProbeAnnotation (.lit 3)
  [sondeProbeVerdict, sondeProbeSample, sondeProbeCall] sondeProbeReturn sondeProbeInput sondeProbeVerdictBody

private theorem sonde_header2 : PlainFunctionHeader sondeUnitMade.val sondeIndex2 := by
  constructor <;> cbv

private def sondeBody2 : {body : PlainFunctionBody sondeUnitMade.val sondeIndex2 //
    lowBody sondeUnitMade.val sondeIndex2 (fnAt sondeUnitMade.val sondeIndex2).body
      (fnAt sondeUnitMade.val sondeIndex2).ret = .ok body} := by
  refine ⟨sondeProbeCompleteBody.val, ?_⟩
  simpa only [lowBody, sonde_probe_body, sonde_probe_return, List.length_cons, List.length_nil] using
    sondeProbeCompleteBody.property

private def sondeFunction2 := lowerFnAt_from_body sonde_header2 sondeBody2

private theorem sonde_header3 : PlainFunctionHeader sondeUnitMade.val sondeIndex3 := by
  constructor <;> cbv

private def sondeBody3 : {body : PlainFunctionBody sondeUnitMade.val sondeIndex3 //
    lowBody sondeUnitMade.val sondeIndex3 (fnAt sondeUnitMade.val sondeIndex3).body
      (fnAt sondeUnitMade.val sondeIndex3).ret = .ok body} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private def sondeFunction3 := lowerFnAt_from_body sonde_header3 sondeBody3

-- The ordinary external adapter has a separately certified head and return.
private abbrev sondeAdapterCtx := ctxOf sondeUnitMade.val sondeIndex4
private abbrev sondeAdapterFn := fnAt sondeUnitMade.val sondeIndex4
private abbrev sondeAdapterResources := resOf sondeUnitMade.val sondeIndex4
private def sondeAdapterReturn : URet := .bool (.var "ans")
private theorem sonde_adapter_body : sondeAdapterFn.body = [.bindCall "ans" "ext" []] := by cbv
private theorem sonde_adapter_return : sondeAdapterFn.ret = sondeAdapterReturn := by cbv
private def sondeAdapterHead : {head : RufKopf sondeUnitMade.val sondeIndex4 sondeAdapterCtx sondeAdapterResources //
    lowRufKopf sondeUnitMade.val sondeIndex4 sondeAdapterCtx sondeAdapterFn sondeAdapterResources "ext" [] = .ok head} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private theorem sonde_adapter_result : (declOf sondeUnitMade.val).erg sondeAdapterHead.val.callee = some .bool := by cbv
private theorem sonde_adapter_reason : (declOf sondeUnitMade.val).gruende sondeAdapterHead.val.callee = 0 := by cbv
private def sondeAdapterAnswer : {term : Expr (declOf sondeUnitMade.val) (.bool :: sondeAdapterCtx)
      (nach (declOf sondeUnitMade.val) sondeAdapterHead.val.callee sondeAdapterResources) .bool //
    lowEns sondeUnitMade.val (.bool :: sondeAdapterCtx)
      (nach (declOf sondeUnitMade.val) sondeAdapterHead.val.callee sondeAdapterResources)
      (sondeAdapterFn.mitTy "ans" .bool) none (.var "ans") = .ok term} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private theorem sonde_adapter_return_type : (fnAt sondeUnitMade.val sondeIndex4).ergTy = some .bool := by cbv
private theorem sonde_adapter_return_ready :
    decide ((nach (declOf sondeUnitMade.val) sondeAdapterHead.val.callee sondeAdapterResources).Perm
      (verOf sondeUnitMade.val sondeIndex4).ende) = true := by cbv
private def sondeAdapterEnding : {ending : Endblock (declOf sondeUnitMade.val) (verOf sondeUnitMade.val sondeIndex4)
      false (.bool :: sondeAdapterCtx) (nach (declOf sondeUnitMade.val) sondeAdapterHead.val.callee sondeAdapterResources) //
    lowEnd sondeUnitMade.val sondeIndex4 (.bool :: sondeAdapterCtx)
      (nach (declOf sondeUnitMade.val) sondeAdapterHead.val.callee sondeAdapterResources)
      (sondeAdapterFn.mitTy "ans" .bool) sondeAdapterReturn = .ok ending} :=
  counterprobe_boolean_end sondeUnitMade.val sondeIndex4 (.bool :: sondeAdapterCtx)
    (nach (declOf sondeUnitMade.val) sondeAdapterHead.val.callee sondeAdapterResources)
    (sondeAdapterFn.mitTy "ans" .bool) (.var "ans")
    sonde_adapter_return_type sondeAdapterAnswer sonde_adapter_return_ready
private def sondeAdapterBody := counterprobe_body_call sondeUnitMade.val sondeIndex4
  sondeAdapterCtx sondeAdapterFn sondeAdapterResources "ans" "ext" [] sondeAdapterReturn
  sondeAdapterHead sonde_adapter_result sonde_adapter_reason sondeAdapterEnding

private theorem sonde_header4 : PlainFunctionHeader sondeUnitMade.val sondeIndex4 := by
  constructor <;> cbv

private def sondeBody4 : {body : PlainFunctionBody sondeUnitMade.val sondeIndex4 //
    lowBody sondeUnitMade.val sondeIndex4 (fnAt sondeUnitMade.val sondeIndex4).body
      (fnAt sondeUnitMade.val sondeIndex4).ret = .ok body} := by
  refine ⟨sondeAdapterBody.val, ?_⟩
  simpa only [lowBody, sonde_adapter_body, sonde_adapter_return, List.length_cons, List.length_nil] using
    sondeAdapterBody.property

private def sondeFunction4 := lowerFnAt_from_body sonde_header4 sondeBody4

private theorem sonde_header5 : PlainFunctionHeader sondeUnitMade.val sondeIndex5 := by
  constructor <;> cbv

private def sondeBody5 : {body : PlainFunctionBody sondeUnitMade.val sondeIndex5 //
    lowBody sondeUnitMade.val sondeIndex5 (fnAt sondeUnitMade.val sondeIndex5).body
      (fnAt sondeUnitMade.val sondeIndex5).ret = .ok body} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private def sondeFunction5 := lowerFnAt_from_body sonde_header5 sondeBody5

private def sondeFunctions (index : Fin sondeUnitMade.val.fns.length) :
    {result : EnsTy sondeUnitMade.val index × RumpTy sondeUnitMade.val index ×
      ReqTy sondeUnitMade.val index // lowerFnAt sondeUnitMade.val index = .ok result} :=
  Fin.cases sondeFunction0 (Fin.cases sondeFunction1 (Fin.cases sondeFunction2
    (Fin.cases sondeFunction3 (Fin.cases sondeFunction4
      (Fin.cases sondeFunction5 (fun i => Fin.elim0 i)))))) index

private theorem sonde_function (index : Fin sondeUnitMade.val.fns.length) :
    lowerFnAt sondeUnitMade.val index = .ok (sondeFunctions index).val :=
  (sondeFunctions index).property

private theorem sonde_each :
    lowerEach sondeUnitMade.val (List.finRange sondeUnitMade.val.fns.length) = .ok () := by
  change lowerEach sondeUnitMade.val
    [sondeIndex0, sondeIndex1, sondeIndex2, sondeIndex3, sondeIndex4, sondeIndex5] = .ok ()
  simp only [lowerEach, sonde_function]

private def sondeMeasures : {exported : Measures.Export sondeUnitMade.val //
    Measures.lowerMeasures sondeUnitMade.val = .ok exported} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private theorem sonde_measure_gate (P : Programm (declOf sondeUnitMade.val)) :
    Measures.checkedProgram sondeUnitMade.val P =
      .ok (P, List.finRange sondeUnitMade.val.fns.length) := by
  apply check_measure_gate _ sondeMeasures.val sondeMeasures.property
  have all : sondeUnitMade.val.fns.all (fun fn => decide (fn.decreases = none)) = true := by cbv
  intro fn member
  exact of_decide_eq_true (List.all_eq_true.mp all fn member)

private theorem sonde_invariants :
    lowerInvs sondeUnitMade.val (List.finRange sondeUnitMade.val.invs.length) = .ok () := by cbv
private theorem sonde_contracts : contractGate sondeUnitMade.val = true := by cbv

private def sondeImage : Programm (declOf sondeUnitMade.val) × List (declOf sondeUnitMade.val).Fn :=
  (progOfFn sondeUnitMade.val
    (fun f => (sondeFunctions f).val.1)
    (fun f => (sondeFunctions f).val.2.1)
    (fun f => (sondeFunctions f).val.2.2)
    (fun i => lowerInvGut sondeUnitMade.val i
      (lowerInvs_all_ok sondeUnitMade.val _ i (List.mem_finRange i) sonde_invariants))
    (ptrVertragOf sondeUnitMade.val)
    (fun a => axVertragOf sondeUnitMade.val a (Bool.and_eq_true_iff.mp sonde_contracts).2),
    List.finRange sondeUnitMade.val.fns.length)

private theorem sonde_program : lowerAllg sondeUnitMade.val = .ok sondeImage :=
  check_assembly sondeUnitMade.val (fun f => (sondeFunctions f).val)
    sonde_function sonde_invariants sonde_each sonde_contracts sonde_measure_gate

private def sondeChecks : {checks : List (CheckDecl (declOf sondeUnitMade.val)) //
    uCheckDecls sondeUnitMade.val = .ok checks} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private theorem sonde_checks : uCheckDecls sondeUnitMade.val = .ok sondeChecks.val :=
  sondeChecks.property

end Gabbro.Grammatik.Parser.Uebersetze
