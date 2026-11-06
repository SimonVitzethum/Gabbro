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

private theorem sonde_header2 : PlainFunctionHeader sondeUnitMade.val sondeIndex2 := by
  constructor <;> cbv

private def sondeBody2 : {body : PlainFunctionBody sondeUnitMade.val sondeIndex2 //
    lowBody sondeUnitMade.val sondeIndex2 (fnAt sondeUnitMade.val sondeIndex2).body
      (fnAt sondeUnitMade.val sondeIndex2).ret = .ok body} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private def sondeFunction2 := lowerFnAt_from_body sonde_header2 sondeBody2

private theorem sonde_header3 : PlainFunctionHeader sondeUnitMade.val sondeIndex3 := by
  constructor <;> cbv

private def sondeBody3 : {body : PlainFunctionBody sondeUnitMade.val sondeIndex3 //
    lowBody sondeUnitMade.val sondeIndex3 (fnAt sondeUnitMade.val sondeIndex3).body
      (fnAt sondeUnitMade.val sondeIndex3).ret = .ok body} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private def sondeFunction3 := lowerFnAt_from_body sonde_header3 sondeBody3

private theorem sonde_header4 : PlainFunctionHeader sondeUnitMade.val sondeIndex4 := by
  constructor <;> cbv

private def sondeBody4 : {body : PlainFunctionBody sondeUnitMade.val sondeIndex4 //
    lowBody sondeUnitMade.val sondeIndex4 (fnAt sondeUnitMade.val sondeIndex4).body
      (fnAt sondeUnitMade.val sondeIndex4).ret = .ok body} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

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
