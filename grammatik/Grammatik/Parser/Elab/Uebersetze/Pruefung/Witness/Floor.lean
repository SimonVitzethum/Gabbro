module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Phases
import Grammatik.Parser.Elab.UebersetzeAllg3.TransitionCert
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Phases
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Calls
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

import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Text

public section
namespace Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

-- The emitted source stays unchanged; these proof equations select its real callbacks.
attribute [local cbv_opaque] uFloatLimit uAnwReihe uAnwReiheCore
  uAkkuBinder uZeigerAnw uStartNamen elabKlauseln expandReturnCall expandFoldEnd
  recordCheckCode recordCheckStatements checkSampleSubstitute lowStufe lowSeqL lowStructL lowEndL
  Measures.checkedProgram lowCallArgOneL lowCallArgsAuxL withErg lowErg lowEnd
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

-- Normalize the actual function fields before forming any dependent code type.
-- Whole-function equality below certifies the headers, code and retained reporter metadata.
private def floorMetadataFn (bound : Int) (index : Nat) (fn : UFn) : UFn :=
  let header : UFn := {fn with
    params := []
    kinds := []
    res := none
    resBool := false
    resOpt := none
    resSum := none
    resWhy := none
    resTy := none
    gruende := 0
    held := []
    puts := []
    gputs := []
    gives := []
    needs := []
    boden := none
    decreases := none
    measureConstants := []
    measureTypes := []
    leiht := []
    bewegt := []
    praegt := []}
  match index with
  | 0 => {header with name := "g", nimmt := [], gibt := [], body := [], ret := .empty}
  | 1 => {header with
    name := "p#probe", resBool := true, nimmt := ["p#duty"], gibt := ["p#duty"],
    body := [.bind "x" (some (0, 18446744073709551615)) (.lit 3),
      .bindB "#checkVerdict" (.cmp ">=" (.param "x") (.lit bound)),
      .bind "#checkSample#0" none (.param "x"),
      .bindCall "#checkReport" "p#report#0" [.val (.param "#checkSample#0"),
        .bval (.cmp ">=" (.param "#checkSample#0") (.lit bound)), .bval (.var "#checkVerdict")]],
    ret := .bool (.var "#checkReport")}
  | 2 => {header with
    name := "p#report#0", resBool := true, nimmt := [], gibt := [],
    params := [("s0", .int 0 18446744073709551615), ("f0", .bool), ("v", .bool)],
    kinds := [.int, .bool, .bool], body := [], ret := .bool (.and (.var "v") (.var "f0"))}
  | 3 => {header with
    name := "p#tor#g", nimmt := ["p#duty"], gibt := ["p#duty"],
    body := [.call "g" []], ret := .empty}
  | _ => fn
private def floorMetadataCheck (check : UCheck) : UCheck :=
  {check with name := "p", tore := ["g"], probe := "p#probe", duty := "p#duty"}
private def floorMetadataUnit (bound : Int) (unit : UProg) : UProg :=
  {unit with
    marken := ["p#duty"]
    fns := unit.fns.mapIdx (floorMetadataFn bound)
    checks := unit.checks.map floorMetadataCheck
    tabs := []
    locks := []
    globs := []
    axs := []
    invs := []
    regs := []
    ptrs := []
    eigner := []
    markOrders := []}

private theorem floor_name_self (name : String) : strEq name name = true := by
  simp [strEq]

-- Resolve the canonical singleton without decoding the same UTF-8 name at every use.
private theorem floor_mark_self (name : String) :
    markFin [name] name = some (⟨0, by decide⟩ : Fin 1) := by
  simp [markFin, List.finRange_succ, floor_name_self]
attribute [local cbv_eval] floor_name_self floor_mark_self

-- Infer this exact unit from canonical elaboration, once, before dependent indices.
private def floorPassingUnitRead : {unit : UProg // elabU (floorItems 2 true true) = .ok unit} := by
  refine ⟨?unit, ?made⟩
  case made => cbv <;> exact Eq.refl _

-- Nondependent field equalities are proved before any declaration/code index exists.
private theorem floorPassing_metadata : floorMetadataUnit 2 floorPassingUnitRead.val = floorPassingUnitRead.val := by
  have marks : floorPassingUnitRead.val.marken = ["p#duty"] := by cbv
  have tables : floorPassingUnitRead.val.tabs = [] := by cbv
  have locks : floorPassingUnitRead.val.locks = [] := by cbv
  have globals : floorPassingUnitRead.val.globs = [] := by cbv
  have foreignBodies : floorPassingUnitRead.val.axs = [] := by cbv
  have invariants : floorPassingUnitRead.val.invs = [] := by cbv
  have registers : floorPassingUnitRead.val.regs = [] := by cbv
  have pointers : floorPassingUnitRead.val.ptrs = [] := by cbv
  have owners : floorPassingUnitRead.val.eigner = [] := by cbv
  have orders : floorPassingUnitRead.val.markOrders = [] := by cbv
  have functions : floorPassingUnitRead.val.fns.mapIdx (floorMetadataFn 2) = floorPassingUnitRead.val.fns := by cbv
  have checks : floorPassingUnitRead.val.checks.map floorMetadataCheck = floorPassingUnitRead.val.checks := by cbv
  generalize source : floorPassingUnitRead.val = actualUnit at *
  cases actualUnit
  simp_all only [floorMetadataUnit]

private def floorPassingUnitMade : {unit : UProg // elabU (floorItems 2 true true) = .ok unit} :=
  ⟨floorMetadataUnit 2 floorPassingUnitRead.val, floorPassingUnitRead.property.trans
    (congrArg (fun unit : UProg => (Except.ok unit : Except String UProg)) floorPassing_metadata.symm)⟩

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
private def floorFailingUnitRead : {unit : UProg // elabU (floorItems 4 true true) = .ok unit} := by
  refine ⟨?unit, ?made⟩
  case made => cbv <;> exact Eq.refl _

-- Nondependent field equalities are proved before any declaration/code index exists.
private theorem floorFailing_metadata : floorMetadataUnit 4 floorFailingUnitRead.val = floorFailingUnitRead.val := by
  have marks : floorFailingUnitRead.val.marken = ["p#duty"] := by cbv
  have tables : floorFailingUnitRead.val.tabs = [] := by cbv
  have locks : floorFailingUnitRead.val.locks = [] := by cbv
  have globals : floorFailingUnitRead.val.globs = [] := by cbv
  have foreignBodies : floorFailingUnitRead.val.axs = [] := by cbv
  have invariants : floorFailingUnitRead.val.invs = [] := by cbv
  have registers : floorFailingUnitRead.val.regs = [] := by cbv
  have pointers : floorFailingUnitRead.val.ptrs = [] := by cbv
  have owners : floorFailingUnitRead.val.eigner = [] := by cbv
  have orders : floorFailingUnitRead.val.markOrders = [] := by cbv
  have functions : floorFailingUnitRead.val.fns.mapIdx (floorMetadataFn 4) = floorFailingUnitRead.val.fns := by cbv
  have checks : floorFailingUnitRead.val.checks.map floorMetadataCheck = floorFailingUnitRead.val.checks := by cbv
  generalize source : floorFailingUnitRead.val = actualUnit at *
  cases actualUnit
  simp_all only [floorMetadataUnit]

private def floorFailingUnitMade : {unit : UProg // elabU (floorItems 4 true true) = .ok unit} :=
  ⟨floorMetadataUnit 4 floorFailingUnitRead.val, floorFailingUnitRead.property.trans
    (congrArg (fun unit : UProg => (Except.ok unit : Except String UProg)) floorFailing_metadata.symm)⟩

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
