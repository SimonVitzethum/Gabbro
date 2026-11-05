module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Phases
import Grammatik.Parser.Elab.UebersetzeAllg3.TransitionCert
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Phases
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

-- A proof-only record update: no body, type, contract, range or source obligation is rebuilt.
-- The equations below certify all replacements against the actual elaborator result.
private def admissionMetadataFn : Nat → UFn → UFn
  | 0, fn => {fn with name := "g", nimmt := [], gibt := []}
  | 1, fn => {fn with name := "p#probe", nimmt := ["p#duty"], gibt := ["p#duty"]}
  | 2, fn => {fn with name := "p#report#0", nimmt := [], gibt := []}
  | 3, fn => {fn with name := "p#tor#g", nimmt := ["p#duty"], gibt := ["p#duty"]}
  | _, fn => fn
private def admissionMetadataCheck (check : UCheck) : UCheck :=
  {check with name := "p", tore := ["g"], probe := "p#probe", duty := "p#duty"}
private def admissionMetadataUnit (unit : UProg) : UProg :=
  {unit with
    marken := ["p#duty"]
    fns := unit.fns.mapIdx admissionMetadataFn
    checks := unit.checks.map admissionMetadataCheck
    tabs := []
    locks := []
    globs := []
    axs := []
    invs := []
    regs := []
    ptrs := []
    eigner := []
    markOrders := []}

private theorem admission_name_self (name : String) : strEq name name = true := by
  simp [strEq]

-- Resolve the canonical singleton without decoding the same UTF-8 name at every use.
private theorem admission_mark_self (name : String) :
    markFin [name] name = some (⟨0, by decide⟩ : Fin 1) := by
  simp [markFin, List.finRange_succ, admission_name_self]
attribute [local cbv_eval] admission_name_self admission_mark_self

-- Infer this exact unit from canonical elaboration, once, before dependent indices.
private def admissionUnitRead : {unit : UProg // elabU (textItems "c" "g") = .ok unit} := by
  refine ⟨?unit, ?made⟩
  case made => cbv <;> exact Eq.refl _

-- Nondependent field equalities are proved before any declaration/code index exists.
private theorem admission_metadata : admissionMetadataUnit admissionUnitRead.val = admissionUnitRead.val := by
  have marks : admissionUnitRead.val.marken = ["p#duty"] := by cbv
  have tables : admissionUnitRead.val.tabs = [] := by cbv
  have locks : admissionUnitRead.val.locks = [] := by cbv
  have globals : admissionUnitRead.val.globs = [] := by cbv
  have foreignBodies : admissionUnitRead.val.axs = [] := by cbv
  have invariants : admissionUnitRead.val.invs = [] := by cbv
  have registers : admissionUnitRead.val.regs = [] := by cbv
  have pointers : admissionUnitRead.val.ptrs = [] := by cbv
  have owners : admissionUnitRead.val.eigner = [] := by cbv
  have orders : admissionUnitRead.val.markOrders = [] := by cbv
  have functions : admissionUnitRead.val.fns.mapIdx admissionMetadataFn = admissionUnitRead.val.fns := by cbv
  have checks : admissionUnitRead.val.checks.map admissionMetadataCheck = admissionUnitRead.val.checks := by cbv
  generalize source : admissionUnitRead.val = actualUnit at *
  cases actualUnit
  simp_all only [admissionMetadataUnit]

private def admissionUnitMade : {unit : UProg // elabU (textItems "c" "g") = .ok unit} :=
  ⟨admissionMetadataUnit admissionUnitRead.val, admissionUnitRead.property.trans
    (congrArg (fun unit : UProg => (Except.ok unit : Except String UProg)) admission_metadata.symm)⟩

private theorem admission_unit : elabU (textItems "c" "g") = .ok admissionUnitMade.val :=
  admissionUnitMade.property

-- Fix every actual function index before inferring a dependent lowered value.
private abbrev admissionFunctionType (index : Fin admissionUnitMade.val.fns.length) :=
  EnsTy admissionUnitMade.val index × RumpTy admissionUnitMade.val index × ReqTy admissionUnitMade.val index

private def admissionGateIndex : Fin admissionUnitMade.val.fns.length :=
  ⟨0, by change 0 < 4; decide⟩

private def admissionGateFunction :
    {result : admissionFunctionType admissionGateIndex //
      lowerFnAt admissionUnitMade.val admissionGateIndex = .ok result} := by
  refine ⟨?result, ?made⟩
  case made => cbv <;> exact Eq.refl _

private def admissionProbeIndex : Fin admissionUnitMade.val.fns.length :=
  ⟨1, by change 1 < 4; decide⟩

private def admissionProbeFunction :
    {result : admissionFunctionType admissionProbeIndex //
      lowerFnAt admissionUnitMade.val admissionProbeIndex = .ok result} := by
  refine ⟨?result, ?made⟩
  case made => cbv <;> exact Eq.refl _

private def admissionReportIndex : Fin admissionUnitMade.val.fns.length :=
  ⟨2, by change 2 < 4; decide⟩

private def admissionReportFunction :
    {result : admissionFunctionType admissionReportIndex //
      lowerFnAt admissionUnitMade.val admissionReportIndex = .ok result} := by
  refine ⟨?result, ?made⟩
  case made => cbv <;> exact Eq.refl _

private def admissionWrapperIndex : Fin admissionUnitMade.val.fns.length :=
  ⟨3, by change 3 < 4; decide⟩

private def admissionWrapperFunction :
    {result : admissionFunctionType admissionWrapperIndex //
      lowerFnAt admissionUnitMade.val admissionWrapperIndex = .ok result} := by
  refine ⟨?result, ?made⟩
  case made => cbv <;> exact Eq.refl _

-- All four certificates are already closed when this dependent selector is formed.
private def admissionFunctions (index : Fin admissionUnitMade.val.fns.length) :
    {result : admissionFunctionType index // lowerFnAt admissionUnitMade.val index = .ok result} :=
  Fin.cases admissionGateFunction
    (Fin.cases admissionProbeFunction
      (Fin.cases admissionReportFunction
        (Fin.cases admissionWrapperFunction (fun i => Fin.elim0 i)))) index

private theorem admission_function (index : Fin admissionUnitMade.val.fns.length) :
    lowerFnAt admissionUnitMade.val index = .ok (admissionFunctions index).val :=
  (admissionFunctions index).property

private theorem admission_each :
    lowerEach admissionUnitMade.val (List.finRange admissionUnitMade.val.fns.length) = .ok () := by
  change lowerEach admissionUnitMade.val
    [admissionGateIndex, admissionProbeIndex, admissionReportIndex, admissionWrapperIndex] = .ok ()
  simp only [lowerEach, admission_function]

private theorem admission_pair (index : Fin admissionUnitMade.val.fns.length)
    (success : ∃ result, lowerFnAt admissionUnitMade.val index = .ok result) :
    lowerAtPair admissionUnitMade.val index success = (admissionFunctions index).val := by
  exact lowerAtPair_of_ok admissionUnitMade.val index success (admission_function index)

private def admissionMeasures :
    {exported : Measures.Export admissionUnitMade.val //
      Measures.lowerMeasures admissionUnitMade.val = .ok exported} := by
  refine ⟨?exported, ?made⟩
  case made => cbv <;> exact Eq.refl _

private theorem admission_measure_gate (P : Programm (declOf admissionUnitMade.val)) :
    @Eq (Except String (Programm (declOf admissionUnitMade.val) × List (declOf admissionUnitMade.val).Fn))
      (Measures.checkedProgram admissionUnitMade.val P)
      (.ok (P, List.finRange admissionUnitMade.val.fns.length)) := by
  apply check_measure_gate _ admissionMeasures.val admissionMeasures.property
  have all : admissionUnitMade.val.fns.all (fun fn => decide (fn.decreases = none)) = true := by cbv
  intro fn member
  exact of_decide_eq_true (List.all_eq_true.mp all fn member)

section admissionAssembly
attribute [local cbv_opaque] lowerFnAt lowerEach lowerAtPair
attribute [local cbv_eval] admission_function admission_each admission_pair admission_measure_gate

private theorem admission_invariants :
    lowerInvs admissionUnitMade.val (List.finRange admissionUnitMade.val.invs.length) = .ok () := by cbv
private theorem admission_contracts : contractGate admissionUnitMade.val = true := by cbv
attribute [local cbv_eval] admission_invariants admission_contracts

-- This is the canonical assembler with the already certified complete fields.
-- Pin the whole pair before proving its production equality.
private def admissionImage :
    Programm (declOf admissionUnitMade.val) × List (declOf admissionUnitMade.val).Fn :=
  (progOfFn admissionUnitMade.val
    (fun f => (admissionFunctions f).val.1)
    (fun f => (admissionFunctions f).val.2.1)
    (fun f => (admissionFunctions f).val.2.2)
    (fun i => lowerInvGut admissionUnitMade.val i
      (lowerInvs_all_ok admissionUnitMade.val _ i (List.mem_finRange i) admission_invariants))
    (ptrVertragOf admissionUnitMade.val)
    (fun a => axVertragOf admissionUnitMade.val a (Bool.and_eq_true_iff.mp admission_contracts).2),
    List.finRange admissionUnitMade.val.fns.length)

private def admissionProgram :
    {result : Programm (declOf admissionUnitMade.val) × List (declOf admissionUnitMade.val).Fn //
      lowerAllg admissionUnitMade.val = .ok result} :=
  ⟨admissionImage, by cbv⟩

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

end admissionAssembly

-- Normalize the actual metadata update before introducing any dependent check index.
private def admissionWithoutWrappersMade : {unit : UProg //
    ({admissionUnitMade.val with
      fns := admissionUnitMade.val.fns.filter fun f => !(strEq f.name "p#tor#g")} : UProg) = unit} := by
  refine ⟨?unit, ?made⟩
  case made => cbv <;> exact Eq.refl _

private theorem admission_wrapper_refused :
    @Eq (Except String (List (CheckDecl (declOf admissionWithoutWrappersMade.val))))
      (uCheckDecls admissionWithoutWrappersMade.val)
      (.error "function unknown: p#tor#g") := by cbv

private def admissionWithoutGivesMade : {unit : UProg //
    ({admissionUnitMade.val with fns := admissionUnitMade.val.fns.map fun f =>
      (if strEq f.name "p#probe" then {f with gibt := []} else f)} : UProg) = unit} := by
  refine ⟨?unit, ?made⟩
  case made => cbv <;> exact Eq.refl _

private def admissionWithoutGivesGateIndex : Fin admissionWithoutGivesMade.val.fns.length :=
  ⟨0, by change 0 < 4; decide⟩

private def admissionWithoutGivesProbeIndex : Fin admissionWithoutGivesMade.val.fns.length :=
  ⟨1, by change 1 < 4; decide⟩

private def admissionWithoutGivesGate :
    {result : EnsTy admissionWithoutGivesMade.val admissionWithoutGivesGateIndex ×
      RumpTy admissionWithoutGivesMade.val admissionWithoutGivesGateIndex ×
      ReqTy admissionWithoutGivesMade.val admissionWithoutGivesGateIndex //
      lowerFnAt admissionWithoutGivesMade.val admissionWithoutGivesGateIndex = .ok result} := by
  refine ⟨?result, ?made⟩
  case made => cbv <;> exact Eq.refl _

-- The ordinary probe lowering produces this error; no replacement refusal is introduced.
private def admissionWithoutGivesProbe : {error : String //
    lowerFnAt admissionWithoutGivesMade.val admissionWithoutGivesProbeIndex = .error error} := by
  refine ⟨?error, ?made⟩
  case made => cbv <;> exact Eq.refl _

private theorem admissionWithoutGives_each :
    lowerEach admissionWithoutGivesMade.val (List.finRange admissionWithoutGivesMade.val.fns.length) =
      .error admissionWithoutGivesProbe.val := by
  change lowerEach admissionWithoutGivesMade.val
    [admissionWithoutGivesGateIndex, admissionWithoutGivesProbeIndex,
      ⟨2, by change 2 < 4; decide⟩, ⟨3, by change 3 < 4; decide⟩] = _
  simp only [lowerEach, admissionWithoutGivesGate.property, admissionWithoutGivesProbe.property]

private theorem refused_functions (unit : UProg) (error : String)
    (failed : lowerEach unit (List.finRange unit.fns.length) = .error error) :
    (lowerAllg unit).toOption.isNone = true := by
  unfold lowerAllg
  split
  · rfl
  · split
    · rfl
    · rename_i made
      rw [failed] at made
      cases made

private theorem admission_gives_refused :
    (lowerAllg admissionWithoutGivesMade.val).toOption.isNone = true :=
  refused_functions _ _ admissionWithoutGives_each

end Gabbro.Grammatik.Parser.Uebersetze
