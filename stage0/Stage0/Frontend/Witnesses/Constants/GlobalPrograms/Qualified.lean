module
public import Stage0.Frontend.Witnesses.Constants.GlobalPrograms.Ordinary
import all Stage0.Frontend.Witnesses.Constants.GlobalPrograms.Ordinary
public import Stage0.Frontend.Witnesses.Constants.ProgramPackets
public import Stage0.Frontend.Witnesses.Constants.GlobalSources
import all Stage0.Frontend.Witnesses.Constants.GlobalSources
import Grammatik.Parser.Elab.Konst.Values.WitnessReaders
import Init.Data.String.Lemmas.Intercalate
import Grammatik.Parser.Elab.UebersetzeAllg3.FunctionResults
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

@[expose] public section
namespace Gabbro.Stage0.Frontend.ConstPhases
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

-- These are the existing generic typed reader equations used by the green const witnesses.
attribute [local cbv_eval] Konst.Values.expression.eq_def Konst.Values.payloadExpression.eq_def
attribute [local cbv_eval] Konst.Values.reify.eq_def Konst.Values.reifyPayload.eq_def
attribute [local cbv_eval]
  Konst.Values.WitnessReaders.reader_bool Konst.Values.WitnessReaders.reader_int
  Konst.Values.WitnessReaders.reader_text Konst.Values.WitnessReaders.reader_sum
  Konst.Values.WitnessReaders.reader_payload Konst.Values.WitnessReaders.reader_empty
  Konst.Values.WitnessReaders.reader_missing

-- Select a used field of the actual fuel record instead of expanding its unused operations.
attribute [local cbv_opaque] lowStufe lowSeqL lowStructL uFloatLimit Frontend.normalize
attribute [local cbv_eval]
  Gabbro.Grammatik.Parser.UebersetzeProben2.seq_select
  Gabbro.Grammatik.Parser.UebersetzeProben2.struct_select
  lowStufe_seq lowStufe_struct
  uKonstZeile.eq_def uKonstZeilen.eq_def lowLit.eq_def

-- Use the source owner's successful metadata and closed qualified-name equation.
attribute [local cbv_eval] globalText_metadata qualifiedText_metadata String.intercalate_singleton

attribute [local cbv_eval] qualified_scope_types qualified_scope_functions qualified_scope_values

-- Select complete canonical data before the module and elaboration consumers inspect it.
private def qualifiedPreparedData :
    { actual : List SItemTief × List SItemTief //
      qualifiedTextInput.prepared.elaborierbar = actual.1 ∧ pre108 actual.1 = actual.2 } := by
  refine ⟨(?elaborierbar, ?preprocessed), ?prepared, ?processed⟩
  case prepared => cbv <;> exact Eq.refl _
  case processed => cbv <;> exact Eq.refl _

private theorem qualified_preprocessed :
    pre108 qualifiedTextInput.prepared.elaborierbar = qualifiedPreparedData.val.2 :=
  (congrArg pre108 qualifiedPreparedData.property.1).trans qualifiedPreparedData.property.2

private def qualifiedExpansion :
    { actual : List SItemTief × List (STyp × String) //
      Modules.prepare qualifiedPreparedData.val.2 = .ok actual } := by
  refine ⟨?actual, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

private def qualifiedElaboration :
    { actual : UProg //
      ((Frontend.elabWithScopes qualifiedPreparedData.val.2
        qualifiedScopesPacket.val.scope.values qualifiedScopesPacket.val.scope.types
        qualifiedScopesPacket.val.scope.functions (Frontend.tableWithEmpty
          qualifiedScopesPacket.val.scope.values qualifiedScopesPacket.val.scope.types)).bind
            (Profil.selectUnit {})) = .ok actual } := by
  refine ⟨?actual, ?produced⟩
  case produced =>
    unfold Frontend.elabWithScopes
    rw [show expandU qualifiedPreparedData.val.2 = .ok qualifiedExpansion.val from
      qualifiedExpansion.property]
    dsimp only [bind, Except.bind]
    cbv <;> exact Eq.refl _

-- Transport the whole UProg result; scope indices never become rewrite motives.
private theorem qualified_elaborated :
    ((Frontend.elabWithScopes (pre108 qualifiedTextInput.prepared.elaborierbar)
      qualifiedTextTail.derived.scope.values qualifiedTextTail.derived.scope.types
      qualifiedTextTail.derived.scope.functions (Frontend.tableWithEmpty
        qualifiedTextTail.derived.scope.values qualifiedTextTail.derived.scope.types)).bind
          (Profil.selectUnit {})) = .ok qualifiedElaboration.val := by
  have inputEq := congrArg (fun items : List SItemTief =>
    (Frontend.elabWithScopes items qualifiedScopesPacket.val.scope.values
      qualifiedScopesPacket.val.scope.types qualifiedScopesPacket.val.scope.functions
      (Frontend.tableWithEmpty qualifiedScopesPacket.val.scope.values
        qualifiedScopesPacket.val.scope.types)).bind (Profil.selectUnit {})) qualified_preprocessed
  have scopesEq := congrArg
    (fun data : List (String × (Int × Int)) × List UKonstFn × List (String × Int) =>
      (Frontend.elabWithScopes (pre108 qualifiedTextInput.prepared.elaborierbar)
        data.2.2 data.1 data.2.1 (Frontend.tableWithEmpty data.2.2 data.1)).bind
          (Profil.selectUnit {})) qualified_scope_data
  exact scopesEq.trans (inputEq.trans qualifiedElaboration.property)

private theorem qualified_constant_gate :
    Konst.checkSourceConstants qualifiedTextInput.original = .ok () := by
  unfold Konst.checkSourceConstants
  split
  · exact qualifiedTextTail.metadata
  · rfl

private theorem qualified_ordinary_gate :
    qualifiedTextInput.original.any Frontend.expansionHeader = false := by
  rw [qualifiedOriginalPacket.property]
  cbv

private def qualifiedTextHeader : Header Gabbro.Stage0.Frontend.ConstValuesWitness.qualifiedText where
  source := sourceFrom qualifiedTextInput qualifiedTextTail
  sourceEq := sourceFrom_eq qualifiedTextInput qualifiedTextTail
  expanded := qualifiedExpansion.val.1
  requirements := qualifiedExpansion.val.2
  expansion := (congrArg Modules.prepare qualified_preprocessed).trans qualifiedExpansion.property
  constants := qualified_constant_gate
  ordinary := qualified_ordinary_gate
  metadata := qualifiedTextTail.metadata
  candidate := qualifiedElaboration.val
  elaborated := qualified_elaborated

@[local cbv_eval] private theorem qualified_unit_data :
    qualifiedTextHeader.unit = { qualifiedElaboration.val with exportGate := .ok () } := by
  exact congrArg (fun gate => { qualifiedElaboration.val with exportGate := gate })
    qualifiedTextHeader.metadata

-- Let the proved unit equation fire before cbv traverses the complete Source record.
attribute [local cbv_opaque] qualifiedTextHeader

private theorem qualifiedText_count : qualifiedTextHeader.unit.fns.length = 1 := by
  change qualifiedElaboration.val.fns.length = 1
  rfl
private def qualifiedTextMain : Fin qualifiedTextHeader.unit.fns.length :=
  ⟨0, by have count := qualifiedText_count; omega⟩
private theorem qualifiedText_only_main (f : Fin qualifiedTextHeader.unit.fns.length) :
    f = qualifiedTextMain := by
  apply Fin.ext
  have small : f.val < 1 := by simpa only [qualifiedText_count] using f.isLt
  change f.val = 0
  omega

-- The data is the actual elaboration result, with exactly the gate justified by qualified_unit_data.
private def qualifiedUnit : UProg := { qualifiedElaboration.val with exportGate := .ok () }

private def qualifiedUnitMain : Fin qualifiedUnit.fns.length :=
  ⟨0, by change (0 : Nat) < 1; decide⟩

private theorem qualifiedText_function_header :
    PlainFunctionHeader qualifiedUnit qualifiedUnitMain := by
  constructor <;> cbv

private def qualifiedTextLoweredBody :
    { actual : PlainFunctionBody qualifiedUnit qualifiedUnitMain //
      lowBody qualifiedUnit qualifiedUnitMain (fnAt qualifiedUnit qualifiedUnitMain).body
        (fnAt qualifiedUnit qualifiedUnitMain).ret = .ok actual } := by
  refine ⟨?actual, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

private def qualifiedTextCode :
    { value : EnsTy qualifiedUnit qualifiedUnitMain ×
        RumpTy qualifiedUnit qualifiedUnitMain × ReqTy qualifiedUnit qualifiedUnitMain //
      lowerFnAt qualifiedUnit qualifiedUnitMain = .ok value } :=
  lowerFnAt_from_body qualifiedText_function_header qualifiedTextLoweredBody

@[local cbv_eval] private theorem qualifiedText_code_eq :
    lowerFnAt qualifiedUnit qualifiedUnitMain = .ok qualifiedTextCode.val := qualifiedTextCode.property

private def qualifiedUnitFunctions : Functions qualifiedUnit :=
  Functions.of_success (by
    apply Fin.forall_fin_one.mpr
    change (lowerFnAt qualifiedUnit qualifiedUnitMain).toOption.isSome = true
    rw [qualifiedText_code_eq]
    rfl) (by cbv) (by apply Fin.forall_fin_one.mpr; cbv) (by cbv)

private theorem qualifiedUnit_accepted :
    OldSource.accepts qualifiedUnit qualifiedUnitFunctions.program = .ok true := by
  apply accepts_function_results qualifiedUnitFunctions
  intro invariants pointers foreigns
  cbv

-- Transport the entire family and its checker result, before projecting any function or program.
private def qualifiedFunctionCertificate :
    { functions : Functions qualifiedTextHeader.unit //
      OldSource.accepts qualifiedTextHeader.unit functions.program = .ok true } :=
  Eq.mpr (congrArg (fun unit : UProg =>
    { functions : Functions unit // OldSource.accepts unit functions.program = .ok true })
      qualified_unit_data) ⟨qualifiedUnitFunctions, qualifiedUnit_accepted⟩

private def qualifiedTextFunctions : Functions qualifiedTextHeader.unit :=
  qualifiedFunctionCertificate.val

-- Obtain the original item spine from the producer; only its scalar leaf is fixed here.
private theorem qualifiedText_arrays_ready :
    (Frontend.checkArrays qualifiedTextHeader.unit qualifiedTextHeader.source.scopes
      qualifiedTextInput.original).toOption.isSome = true := by
  have typed : uTypIn qualifiedTextHeader.source.scopes.types []
      (uRecordConstantTypes qualifiedTextHeader.unit.records) [] [] (.atom "u8") =
      .ok (.int 0 255) := by
    change uTypIn qualifiedTextTail.derived.scope.types []
      (uRecordConstantTypes qualifiedTextHeader.unit.records) [] [] (.atom "u8") = .ok (.int 0 255)
    rw [qualified_scope_types]
    cbv
  have itemSpine : ∃ name firstSig firstBody lastSig lastBody,
      qualifiedTextInput.original = [.constT name (.atom "u8") (.one (.lit 5)),
        .fnT firstSig firstBody, .fnT lastSig lastBody] := by
    rw [qualifiedOriginalPacket.property]
    refine ⟨?name, ?firstSig, ?firstBody, ?lastSig, ?lastBody, ?origin⟩
    case origin => cbv <;> exact Eq.refl _
  obtain ⟨name, firstSig, firstBody, lastSig, lastBody, origin⟩ := itemSpine
  have meanings : qualifiedTextInput.original.all
      (Frontend.checkConstantMeaning qualifiedTextHeader.source.scopes.types
        qualifiedTextHeader.source.scopes.functions qualifiedTextHeader.source.scopes.values) = true :=
    qualifiedTextTail.constants
  apply checked_array_items
  intro item member
  have meaning := List.all_eq_true.mp meanings item member
  rw [origin] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact checked_u8_five qualifiedTextHeader.unit qualifiedTextHeader.source.scopes name meaning typed
  · rfl
  · rfl

private theorem qualifiedText_entry_free (f : Fin qualifiedTextHeader.unit.fns.length) :
    (OldSource.clauses qualifiedTextHeader.expanded (fnAt qualifiedTextHeader.unit f).name).any
      OldSource.hasEntry = false := by
  have same := qualifiedText_only_main f
  subst f
  change (OldSource.clauses qualifiedExpansion.val.1
    (fnAt qualifiedTextHeader.unit qualifiedTextMain).name).any OldSource.hasEntry = false
  cbv

private theorem qualifiedText_restored :
    OldSource.restore (pre108 qualifiedTextHeader.source.prepared.elaborierbar)
      qualifiedTextHeader.unit qualifiedTextFunctions.program = .ok qualifiedTextFunctions.program :=
  restore_entry_free _ qualifiedTextHeader.expanded qualifiedTextHeader.requirements
    qualifiedTextHeader.unit qualifiedTextFunctions.program qualifiedTextHeader.expansion qualifiedText_entry_free

private theorem qualifiedText_accepted :
    OldSource.accepts qualifiedTextHeader.unit qualifiedTextFunctions.program = .ok true :=
  qualifiedFunctionCertificate.property

private def qualifiedTextBody : Body qualifiedTextHeader where
  functions := qualifiedTextFunctions
  main := qualifiedTextMain
  entry := by cbv
  initializers := by
    change Frontend.checkInitializers qualifiedTextInput.original qualifiedTextHeader.unit = .ok ()
    rw [qualifiedOriginalPacket.property]
    cbv
  arrays := (Frontend.checkArrays qualifiedTextHeader.unit qualifiedTextHeader.source.scopes
    qualifiedTextInput.original).toOption.get qualifiedText_arrays_ready
  arrayEq := Gabbro.Grammatik.except_ok_get qualifiedText_arrays_ready
  program := qualifiedTextFunctions.program
  restored := qualifiedText_restored
  accepted := qualifiedText_accepted

private theorem qualifiedText_program_packet :
    ∃ header : Header Gabbro.Stage0.Frontend.ConstValuesWitness.qualifiedText,
      header.unit.fns.length = 1 ∧ Nonempty (Body header) :=
  ⟨qualifiedTextHeader, qualifiedText_count, ⟨qualifiedTextBody⟩⟩

theorem qualifiedText_compiled :
    ∃ result : Compiled Gabbro.Stage0.Frontend.ConstValuesWitness.qualifiedText,
      compile Gabbro.Stage0.Frontend.ConstValuesWitness.qualifiedText = .ok result ∧
      result.unit.fns.length = 1 := by
  obtain ⟨header, count, ⟨body⟩⟩ := qualifiedText_program_packet
  obtain ⟨result, origin, unitEq⟩ := compiled header body
  exact ⟨result, origin, (congrArg (fun unit => unit.fns.length) unitEq).trans count⟩

end Gabbro.Stage0.Frontend.ConstPhases
