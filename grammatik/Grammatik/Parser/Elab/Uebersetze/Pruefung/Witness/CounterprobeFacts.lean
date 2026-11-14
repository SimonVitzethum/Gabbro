module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.CounterprobeLowering
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
import all Grammatik.Parser.Elab.Uebersetze.Loops.Headers
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

import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.CounterprobeLowering
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.CounterprobeBodies
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Admission
public import Grammatik.Kern.Syntax.Satz.PruefungArtefakt
public import Grammatik.Kern.Syntax.Satz.PruefungMessung
public import Grammatik.Zielsatz.Kern.Akzeptiert.CheckProof

@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Zielsatz

/-- The negative report of the counterprobe run: the sample was read, no floor
    was declared, the verdict records the failure. -/
def berichtSondeFalsch : CheckReport :=
  { proben := [{ ort := "x", punkt := 0, wert := 3, gelesen := true }],
    boeden := [], urteil := false }

/-- The matching artifact: the shipping image under the bound name. -/
def artefaktSonde : SondenArtefakt := ⟨"ext", false, "ship"⟩

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
local instance counterprobeAxiomEquality (u : UProg) : DecidableEq (declOf u).Ax :=
  inferInstanceAs (DecidableEq (Fin u.axs.length))

attribute [local cbv_opaque] lowerAllg uCheckDecls
attribute [local cbv_eval] sonde_program sonde_checks

-- Observation is independent of how a typed return was transported: when
-- both carrier types are empty, its actual footprint cannot contain a cell.
-- Keep the result index and expression arbitrary instead of reducing Eq.mpr
-- inside the dependent ErgExpr matcher at a concrete function signature.
private theorem counterprobe_return_orte_empty (unit : UProg)
    (tables : unit.tabs = []) (globals : unit.globs = [])
    {Γ : Ctx} {Λ : List (Res (declOf unit))} {result : Option Ty}
    (value : ErgExpr (declOf unit) Γ Λ result) : value.orte = [] := by
  cases observed : value.orte with
  | nil => rfl
  | cons cell rest =>
    cases cell with
    | inl table =>
      have empty : unit.tabs.length = 0 := by rw [tables]; rfl
      have actual : Fin unit.tabs.length := table
      exact Fin.elim0 (empty ▸ actual)
    | inr global =>
      have empty : unit.globs.length = 0 := by rw [globals]; rfl
      have actual : Fin unit.globs.length := global
      exact Fin.elim0 (empty ▸ actual)

private theorem sonde_tables_empty : sondeUnitMade.val.tabs = [] := by cbv
private theorem sonde_globals_empty : sondeUnitMade.val.globs = [] := by cbv

private theorem sonde_return_orte_empty {Γ : Ctx}
    {Λ : List (Res (declOf sondeUnitMade.val))} {result : Option Ty}
    (value : ErgExpr (declOf sondeUnitMade.val) Γ Λ result) : value.orte = [] :=
  counterprobe_return_orte_empty sondeUnitMade.val sonde_tables_empty sonde_globals_empty value

attribute [local cbv_eval] sonde_return_orte_empty

private theorem sonde_common : CheckWitness sondeUnitMade.val 0 := by
  constructor <;> cbv

-- All declaration-indexed observations are packaged before the public getter
-- is substituted. The final transport changes the entire proposition at once.
private structure CounterprobeFacts (unit : UProg) : Prop where
  common : CheckWitness unit 0
  sourceIdentity : unit.checks.map (·.sonde) = [some ("ext", "ext text")]
  retained : ((uCheckDecls unit).toOption.get common.derived).map CheckDecl.sonde =
    [some ("ext", "ext text")]
  testBuild : ((uCheckDecls unit).toOption.get common.derived).map CheckDecl.testbau = [false]
  unique : sondenEindeutigB ((uCheckDecls unit).toOption.get common.derived) = true
  gateDuty : ((uCheckDecls unit).toOption.get common.derived).all (fun d =>
    d.gates.all fun g => decide (d.duty ∈ ((declOf unit).signatur g).konsumiert)) = true
  adapter : (unit.fns.find? (fun f => strEq f.name "p#sonde#ext")).map
      (fun f => (f.body, f.ret, f.nimmt, f.gibt)) =
    some ([.bindCall "ans" "ext" []], .bool (.var "ans"), [], [])
  measured : ((uCheckDecls unit).toOption.get common.derived).all (fun d =>
    sondenNachweisB ((uCheckDecls unit).toOption.get common.derived) d "ship" artefaktSonde
      .durchgefallen berichtSondeFalsch) = true
  stale : ((uCheckDecls unit).toOption.get common.derived).all (fun d =>
    !(sondenArtefaktB d "ship" ⟨"ext", false, "old-image"⟩
      .durchgefallen berichtSondeFalsch)) = true

private theorem sonde_facts : CounterprobeFacts sondeUnitMade.val := by
  refine ⟨sonde_common, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> cbv

-- This is the actual metadata edit from the refusal witness, certified before
-- its dependent descriptor reader is entered.
private def sondeWithoutBindingMade : {unit : UProg //
    ({sondeUnitMade.val with
      fns := sondeUnitMade.val.fns.filter (fun f => !strEq f.name "p#sonde#ext")} : UProg) = unit} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private def sondeWithoutBindingError : {error : String //
    uCheckDecls sondeWithoutBindingMade.val = .error error} := by
  refine ⟨?error, ?made⟩
  -- Here only descriptor derivation is active, not the whole source pipeline.
  case made =>
    unfold uCheckDecls
    cbv <;> exact Eq.refl _

private theorem sonde_without_binding_refused :
    (uCheckDecls ({sondeUnitMade.val with
      fns := sondeUnitMade.val.fns.filter (fun f => !strEq f.name "p#sonde#ext")} : UProg)).toOption.isNone = true := by
  rw [sondeWithoutBindingMade.property, sondeWithoutBindingError.property]
  rfl

-- Reuse the already checked ordinary admission packet for the no-sonde leg.
private def NoSonde (unit : UProg) : Prop :=
  ∀ success : (uCheckDecls unit).toOption.isSome = true,
    ((uCheckDecls unit).toOption.get success).map CheckDecl.sonde = [none]

private theorem admission_no_sonde : NoSonde admissionUnitMade.val := by
  intro success
  have actual : (uCheckDecls admissionUnitMade.val).toOption.get success = admissionChecks.val :=
    Except.ok.inj ((except_ok_get (x := uCheckDecls admissionUnitMade.val) success).symm.trans
      admission_checks)
  rw [actual]
  cbv

end Gabbro.Grammatik.Parser.Uebersetze
