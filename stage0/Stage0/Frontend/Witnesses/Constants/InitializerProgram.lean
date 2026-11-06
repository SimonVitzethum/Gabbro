module
public import Stage0.Frontend.Witnesses.Constants.ProgramPackets
public import Stage0.Frontend.Witnesses.Constants.IntegerSources
import all Stage0.Frontend.Witnesses.Constants.IntegerSources
import Grammatik.Parser.Elab.Konst.Values.WitnessReaders
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

/-- Transport all scalar scope projections together from the certified collector preparation. -/
private theorem initializer_scope_data
    (P : List (String × (Int × Int)) → List UKonstFn → List (String × Int) → Prop)
    (proved : P
      (initializerScopePreparation.val.env ++ initializerScalarFold.val.map
        (fun c => (c.1, (c.2, c.2))))
      initializerScopePreparation.val.fns initializerScalarFold.val) :
    P initializerConservative.scope.types initializerConservative.scope.functions
      initializerConservative.scope.values := by
  dsimp only [initializerConservative, Frontend.evaluatedScopes, Frontend.Scopes.types]
  exact Eq.mpr (congrArg (fun prepared : Frontend.Prepared =>
    P (prepared.env ++ initializerScalarFold.val.map (fun c => (c.1, (c.2, c.2))))
      prepared.fns initializerScalarFold.val) initializerScopePreparation.property) proved

/-- Infer the complete numeric result from the actual evaluator in the already certified scope. -/
private theorem initializer_numeric_value :
    ∃ value : Int,
      uKonstWert 0 255 initializerConservative.scope.functions
        initializerConservative.scope.values 64 (.call "increment" [.lit 3]) = some value ∧
      0 ≤ value ∧ value ≤ 255 := by
  have packet : ∃ value : Int,
      uKonstWert 0 255 initializerScopePreparation.val.fns initializerScalarFold.val
        64 (.call "increment" [.lit 3]) = some value ∧ 0 ≤ value ∧ value ≤ 255 := by
    refine ⟨?value, ?evaluated, ?lower, ?upper⟩
    case evaluated => cbv <;> exact Eq.refl _
    case lower => cbv <;> exact Int.NonNeg.mk _
    case upper => cbv <;> exact Int.NonNeg.mk _
  obtain ⟨value, evaluated, lower, upper⟩ := packet
  exact ⟨value, initializer_scope_data (fun _ fns values =>
    uKonstWert 0 255 fns values 64 (.call "increment" [.lit 3]) = some value) evaluated,
    lower, upper⟩

/-- Select the actual constant-item checker through all of its original typed gates. -/
private theorem checked_constant_item {original : List SItemTief}
    (u : UProg) (scope : Frontend.Scopes original)
    (name : String) (sourceType : STyp) (payload : SKonstWert)
    (ty : Ty) (raw : USide) (term : Expr (declOf u) [] [] ty)
    (meaning : Frontend.checkConstantMeaning scope.types scope.functions scope.values
      (.constT name sourceType payload) = true)
    (typed : uTypIn scope.types [] (uRecordConstantTypes u.records) [] [] sourceType = .ok ty)
    (evaluated : uKonstZeile scope.types scope.functions scope.values ty payload
      (uRecordConstant u.records scope.types scope.functions scope.values) = some raw)
    (lowered : lowLit (u := u) (Γ := []) (Λ := []) ty raw = .ok term) :
    (Frontend.checkArrayItem u scope (.constT name sourceType payload)).toOption.isSome = true := by
  unfold Frontend.checkArrayItem
  dsimp only [Frontend.arrayInput]
  split
  · split
    · rename_i error rejected
      cases rejected.symm.trans typed
    · rename_i actual selected
      have same : actual = ty := Except.ok.inj (selected.symm.trans typed)
      subst actual
      split
      · rename_i rejected
        cases rejected.symm.trans evaluated
      · rename_i actual selected
        have same : actual = raw := Option.some.inj (selected.symm.trans evaluated)
        subst actual
        split
        · rename_i error rejected
          cases rejected.symm.trans lowered
        · rfl
  · rename_i rejected
    exact False.elim (rejected meaning)

/-- Select the actual profile/name data before expansion or elaboration inspects
    it. The two lists are inferred from the unchanged producer equations. -/
private def initializerPreparedData :
    { actual : List SItemTief × List SItemTief //
      initializerInput.prepared.elaborierbar = actual.1 ∧ pre108 actual.1 = actual.2 } := by
  refine ⟨(?elaborierbar, ?preprocessed), ?prepared, ?processed⟩
  case prepared => cbv <;> exact Eq.refl _
  case processed => cbv <;> exact Eq.refl _

private theorem initializer_preprocessed :
    pre108 initializerInput.prepared.elaborierbar = initializerPreparedData.val.2 :=
  (congrArg pre108 initializerPreparedData.property.1).trans initializerPreparedData.property.2

/-- Reuse the certified scalar fold, retaining the complete ordered scope data
    before it becomes an argument of the runtime elaborator. -/
private def initializerScopeData :
    { actual : List (String × (Int × Int)) × List UKonstFn × List (String × Int) //
      (initializerConservative.scope.types, initializerConservative.scope.functions,
        initializerConservative.scope.values) = actual } := by
  refine ⟨?actual, ?origin⟩
  case origin =>
    exact initializer_scope_data (fun types functions values => (types, functions, values) = _)
      (by cbv <;> exact Eq.refl _)

-- These are the source owner's actual checked call/replacement packets. Keep
-- the cost and contract checks, but do not recompute their discovery graph.
@[local cbv_eval] private theorem initializer_metadata_on_items :
    Konst.checkSourceMetadata initializerMetadataItems.val = .ok () :=
  (congrArg Konst.checkSourceMetadata initializerMetadataItems.property).symm.trans
    initializerTail.metadata

@[local cbv_eval] private theorem initializer_pipeline_on_items :
    Konst.konstErsetzePipeline initializerMetadataItems.val = .ok initializerMetadataRewritten.val := by
  let remaining (items : List SItemTief)
      (data : List (String × Int) × List (String × (Int × Int))) :=
    (Konst.collectFunctionsWith items data.1 data.2).bind
      (fun functions => Konst.ersetzeItems functions items)
  have present : initializerInput.original.any
      (fun | .fnT signature _ => strEq signature.art "const" | _ => false) = true := by
    have kept : initializerMetadataItems.val.any
        (fun | .fnT signature _ => strEq signature.art "const" | _ => false) = true := by cbv
    exact (congrArg (fun items : List SItemTief => items.any
      (fun | .fnT signature _ => strEq signature.art "const" | _ => false))
      initializerMetadataItems.property).trans kept
  have origin := Konst.konstErsetzePipeline_from_scopes initializerInput.original
    initializerConservative present initializer_scope_origin
  have scopes := congrArg (remaining initializerInput.original) initializerMetadataScope.property
  have items := congrArg (fun items => remaining items initializerMetadataScope.val)
    initializerMetadataItems.property
  have produced : remaining initializerMetadataItems.val initializerMetadataScope.val =
      .ok initializerMetadataRewritten.val := by
    simpa only [remaining, initializerMetadataFunctions.property, bind, Except.bind] using
      initializerMetadataRewritten.property
  have original := origin.trans (scopes.trans (items.trans produced))
  exact (congrArg Konst.konstErsetzePipeline initializerMetadataItems.property).symm.trans original

attribute [local cbv_eval] initializer_rewritten_metadata

private def initializerExpansion :
    { actual : List SItemTief × List (STyp × String) //
      Modules.prepare initializerPreparedData.val.2 = .ok actual } := by
  refine ⟨?actual, ?origin⟩
  case origin => cbv <;> exact Eq.refl _

/-- Infer the whole canonical UProg on normalized producer data before the
    Header's dependent fields or function indices can force its source graph. -/
private def initializerElaboration :
    { actual : UProg //
      ((Frontend.elabWithScopes initializerPreparedData.val.2
        initializerScopeData.val.2.2 initializerScopeData.val.1 initializerScopeData.val.2.1
        (Frontend.tableWithEmpty initializerScopeData.val.2.2 initializerScopeData.val.1)).bind
          (Profil.selectUnit {})) = .ok actual } := by
  refine ⟨?actual, ?origin⟩
  case origin =>
    unfold Frontend.elabWithScopes
    rw [show expandU initializerPreparedData.val.2 = .ok initializerExpansion.val from
      initializerExpansion.property]
    dsimp only [bind, Except.bind]
    cbv <;> exact Eq.refl _

private theorem initializer_elaborated :
    ((Frontend.elabWithScopes (pre108 initializerInput.prepared.elaborierbar)
      initializerConservative.scope.values initializerConservative.scope.types
      initializerConservative.scope.functions (Frontend.tableWithEmpty
        initializerConservative.scope.values initializerConservative.scope.types)).bind
          (Profil.selectUnit {})) = .ok initializerElaboration.val := by
  let run (items : List SItemTief)
      (data : List (String × (Int × Int)) × List UKonstFn × List (String × Int)) :=
    (Frontend.elabWithScopes items data.2.2 data.1 data.2.1
      (Frontend.tableWithEmpty data.2.2 data.1)).bind (Profil.selectUnit {})
  have scopes := congrArg (run (pre108 initializerInput.prepared.elaborierbar)) initializerScopeData.property
  have items := congrArg (fun items => run items initializerScopeData.val) initializer_preprocessed
  exact scopes.trans (items.trans initializerElaboration.property)

private theorem initializer_constant_gate :
    Konst.checkSourceConstants initializerInput.original = .ok () := by
  unfold Konst.checkSourceConstants
  split
  · exact initializerTail.metadata
  · rfl

private theorem initializer_ordinary_gate :
    initializerInput.original.any Frontend.expansionHeader = false := by
  exact (congrArg (fun items : List SItemTief => items.any Frontend.expansionHeader)
    initializerMetadataItems.property).trans (by cbv)

/-- The same canonical Header, assembled only from complete producer packets. -/
private def initializerHeader : Header Gabbro.Stage0.Frontend.ConstWitness.initializerText where
    source := sourceFrom initializerInput initializerTail
    sourceEq := by exact sourceFrom_eq initializerInput initializerTail
    expanded := initializerExpansion.val.1
    requirements := initializerExpansion.val.2
    expansion := by exact (congrArg Modules.prepare initializer_preprocessed).trans initializerExpansion.property
    constants := by exact initializer_constant_gate
    ordinary := by exact initializer_ordinary_gate
    metadata := by exact initializerTail.metadata
    candidate := initializerElaboration.val
    elaborated := by exact initializer_elaborated

@[local cbv_eval] private theorem initializer_unit_data :
    initializerHeader.unit = { initializerElaboration.val with exportGate := .ok () } := by
  exact congrArg (fun gate => { initializerElaboration.val with exportGate := gate })
    initializerHeader.metadata

-- Let the whole proved unit equation select its data before cbv visits Source.
attribute [local cbv_opaque] initializerHeader

private theorem initializer_count : initializerHeader.unit.fns.length = 1 := by
  change initializerElaboration.val.fns.length = 1
  rfl

private def initializerMain : Fin initializerHeader.unit.fns.length :=
  ⟨0, by have count := initializer_count; omega⟩

/-- This is the same produced unit with exactly the gate proved above. Build
    dependent function data here and transport the complete certificate once. -/
private def initializerUnit : UProg := { initializerElaboration.val with exportGate := .ok () }

private def initializerUnitMain : Fin initializerUnit.fns.length :=
  ⟨0, by change (0 : Nat) < 1; decide⟩

private theorem initializerUnit_only_main (f : Fin initializerUnit.fns.length) :
    f = initializerUnitMain := by
  apply Fin.ext
  have bound := f.isLt
  change f.val < 1 at bound
  change f.val = 0
  omega

/-- The complete triple is inferred only from the actual lowering equation. -/
private def initializerCode :
    { code : EnsTy initializerUnit initializerUnitMain ×
        RumpTy initializerUnit initializerUnitMain × ReqTy initializerUnit initializerUnitMain //
      lowerFnAt initializerUnit initializerUnitMain = .ok code } := by
  refine ⟨?code, ?origin⟩
  case origin => cbv <;> exact Eq.refl _

private theorem initializer_code_eq :
    lowerFnAt initializerUnit initializerUnitMain = .ok initializerCode.val :=
  initializerCode.property

private theorem initializer_only_main (f : Fin initializerHeader.unit.fns.length) :
    f = initializerMain := by
  apply Fin.ext
  have small : f.val < 1 := by simpa only [initializer_count] using f.isLt
  change f.val = 0
  omega

private def initializerUnitFunctions : Functions initializerUnit :=
  Functions.of_success (fun f => by
    have same := initializerUnit_only_main f
    subst f
    rw [initializer_code_eq]
    rfl) (by cbv) (fun f => by
      have same := initializerUnit_only_main f
      subst f
      cbv) (by cbv)

-- The successful checker proof remains unchanged, but is an opaque proof
-- constant instead of a large local let inside the final Body constructor.
private theorem initializerUnit_accepted :
    OldSource.accepts initializerUnit initializerUnitFunctions.program = .ok true := by
  apply accepts_function_results initializerUnitFunctions
  intro invariants pointers foreigns
  cbv

private def initializerFunctionCertificate :
    { functions : Functions initializerHeader.unit //
      OldSource.accepts initializerHeader.unit functions.program = .ok true } :=
  Eq.mpr (congrArg (fun unit : UProg =>
    { functions : Functions unit // OldSource.accepts unit functions.program = .ok true })
      initializer_unit_data) ⟨initializerUnitFunctions, initializerUnit_accepted⟩

private def initializerFunctions : Functions initializerHeader.unit := initializerFunctionCertificate.val

private theorem initializer_accepted :
    OldSource.accepts initializerHeader.unit initializerFunctions.program = .ok true :=
  initializerFunctionCertificate.property

/-- Resolve the scalar collector and literal path before the dependent array fold. -/
private theorem initializer_arrays_ready :
    (Frontend.checkArrays initializerHeader.unit initializerHeader.source.scopes
      initializerInput.original).toOption.isSome = true := by
  let header := initializerHeader
  obtain ⟨value, evaluated, lower, upper⟩ := initializer_numeric_value
  have typed : uTypIn header.source.scopes.types [] (uRecordConstantTypes header.unit.records)
      [] [] (.atom "u8") = .ok (.int 0 255) := by
    change uTypIn initializerConservative.scope.types []
      (uRecordConstantTypes header.unit.records) [] [] (.atom "u8") = .ok (.int 0 255)
    apply initializer_scope_data
      (fun types _ _ => uTypIn types [] (uRecordConstantTypes header.unit.records)
        [] [] (.atom "u8") = .ok (.int 0 255))
    cbv
  have actualEvaluation : uKonstWert 0 255 header.source.scopes.functions
      header.source.scopes.values 64 (.call "increment" [.lit 3]) = some value := by
    change uKonstWert 0 255 initializerConservative.scope.functions
      initializerConservative.scope.values 64 (.call "increment" [.lit 3]) = some value
    exact evaluated
  have literal : uKonstZeile header.source.scopes.types header.source.scopes.functions
      header.source.scopes.values (.int 0 255) (.one (.call "increment" [.lit 3]))
      (uRecordConstant header.unit.records header.source.scopes.types
        header.source.scopes.functions header.source.scopes.values) = some (.lit value) := by
    rw [uKonstZeile_int, actualEvaluation]
    rfl
  have lowered : lowLit (u := header.unit) (Γ := []) (Λ := [])
      (.int 0 255) (.lit value) =
      .ok (.widen lower upper (.lit value)) := by
    simp only [lowLit, dite_eq_left lower, dite_eq_left upper]
  have itemSpine : ∃ firstSig firstBody lastSig lastBody,
      initializerInput.original = [.fnT firstSig firstBody,
        .constT "ANSWER" (.atom "u8") (.one (.call "increment" [.lit 3])),
        .fnT lastSig lastBody] := by
    refine ⟨?firstSig, ?firstBody, ?lastSig, ?lastBody, ?origin⟩
    case origin => cbv <;> exact Eq.refl _
  obtain ⟨firstSig, firstBody, lastSig, lastBody, origin⟩ := itemSpine
  have checked : ∀ item ∈ initializerInput.original,
      (Frontend.checkArrayItem header.unit header.source.scopes item).toOption.isSome = true := by
    have meanings : initializerInput.original.all
        (Frontend.checkConstantMeaning header.source.scopes.types
          header.source.scopes.functions header.source.scopes.values) = true := by
      change initializerInput.original.all
        (Frontend.checkConstantMeaning initializerConservative.scope.types
          initializerConservative.scope.functions initializerConservative.scope.values) = true
      exact initializerTail.constants
    intro item member
    have meaning : Frontend.checkConstantMeaning header.source.scopes.types
        header.source.scopes.functions header.source.scopes.values item = true :=
      List.all_eq_true.mp meanings item member
    rw [origin] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · rfl
    · exact checked_constant_item header.unit header.source.scopes "ANSWER" (.atom "u8")
        (.one (.call "increment" [.lit 3])) (.int 0 255) (.lit value)
        (.widen lower upper (.lit value)) meaning typed literal lowered
    · rfl
  exact checked_array_items header.unit header.source.scopes initializerInput.original checked

private theorem initializer_entry_free (f : Fin initializerHeader.unit.fns.length) :
    (OldSource.clauses initializerHeader.expanded (fnAt initializerHeader.unit f).name).any
      OldSource.hasEntry = false := by
  have same := initializer_only_main f
  subst f
  change (OldSource.clauses initializerExpansion.val.1
    (fnAt initializerHeader.unit initializerMain).name).any OldSource.hasEntry = false
  cbv

private theorem initializer_restored :
    OldSource.restore (pre108 initializerHeader.source.prepared.elaborierbar)
      initializerHeader.unit initializerFunctions.program = .ok initializerFunctions.program :=
  restore_entry_free _ initializerHeader.expanded initializerHeader.requirements
    initializerHeader.unit initializerFunctions.program initializerHeader.expansion initializer_entry_free

private theorem initializer_entry :
    fnIdx initializerHeader.unit.fns (Profil.entryName {}) = .ok initializerMain := by cbv

private theorem initializer_initializers :
    Frontend.checkInitializers (uMembers (pre108 initializerHeader.source.prepared.elaborierbar))
      initializerHeader.unit = .ok () := by
  have transported := congrArg (fun items : List SItemTief =>
    Frontend.checkInitializers (uMembers items) initializerHeader.unit) initializer_preprocessed
  exact transported.trans (by cbv)

/-- Assemble only the already certified fields; no source or checker rerun occurs here. -/
private def initializerBody : Body initializerHeader where
  functions := initializerFunctions
  main := initializerMain
  entry := initializer_entry
  initializers := initializer_initializers
  arrays := (Frontend.checkArrays initializerHeader.unit initializerHeader.source.scopes
    initializerInput.original).toOption.get initializer_arrays_ready
  arrayEq := Gabbro.Grammatik.except_ok_get initializer_arrays_ready
  program := initializerFunctions.program
  restored := initializer_restored
  accepted := initializer_accepted

private theorem initializer_program_packet :
    ∃ header : Header Gabbro.Stage0.Frontend.ConstWitness.initializerText,
      header.unit.fns.length = 1 ∧ Nonempty (Body header) :=
  ⟨initializerHeader, initializer_count, ⟨initializerBody⟩⟩

theorem initializer_compiled :
    ∃ result : Compiled Gabbro.Stage0.Frontend.ConstWitness.initializerText, compile Gabbro.Stage0.Frontend.ConstWitness.initializerText = .ok result ∧
      result.unit.fns.length = 1 := by
  obtain ⟨header, count, ⟨body⟩⟩ := initializer_program_packet
  obtain ⟨result, origin, unitEq⟩ := compiled header body
  exact ⟨result, origin, (congrArg (fun unit => unit.fns.length) unitEq).trans count⟩

end Gabbro.Stage0.Frontend.ConstPhases
