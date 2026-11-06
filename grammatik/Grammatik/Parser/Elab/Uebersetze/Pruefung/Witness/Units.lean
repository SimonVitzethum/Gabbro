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

/-- The actual constructor-valued unit retained by the passing-floor source certificate. -/
@[expose] def uBodenWahr : UProg := floorPassingUnitMade.val

-- Normalize the actual function fields before forming any dependent code type.
-- Whole-function equality below certifies the headers, code and retained reporter metadata.
private def admissionMetadataFn (index : Nat) (fn : UFn) : UFn :=
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
    body := [.bindB "#checkVerdict" .tru,
      .bindCall "#checkReport" "p#report#0" [.bval (.var "#checkVerdict")]],
    ret := .bool (.var "#checkReport")}
  | 2 => {header with
    name := "p#report#0", params := [("v", .bool)], kinds := [.bool],
    resBool := true, nimmt := [], gibt := [], body := [], ret := .bool (.var "v")}
  | 3 => {header with
    name := "p#tor#g", nimmt := ["p#duty"], gibt := ["p#duty"],
    body := [.call "g" []], ret := .empty}
  | _ => fn
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

/-- The actual constructor-valued unit retained by the failing-floor source certificate. -/
@[expose] def uBodenFalsch : UProg := floorFailingUnitMade.val

end Gabbro.Grammatik.Parser.Uebersetze
