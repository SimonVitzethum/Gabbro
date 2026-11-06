module
public import Stage0.SourceWitness.InputScopes
import all Stage0.SourceWitness.InputScopes
import all Stage0.SourceWitness.Owners

@[expose] public section
namespace Gabbro.Stage0.SourceWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Frontend.ConstPhases
set_option maxRecDepth 2000
set_option maxHeartbeats 100000

attribute [local cbv_opaque] uFloatLimit Frontend.normalize
attribute [local cbv_eval] Konst.Values.expression.eq_def Konst.Values.payloadExpression.eq_def
  Konst.Values.reify.eq_def Konst.Values.reifyPayload.eq_def
  Konst.Values.WitnessReaders.reader_bool Konst.Values.WitnessReaders.reader_int
  Konst.Values.WitnessReaders.reader_text Konst.Values.WitnessReaders.reader_sum
  Konst.Values.WitnessReaders.reader_payload Konst.Values.WitnessReaders.reader_empty
  Konst.Values.WitnessReaders.reader_missing

-- Local rules do not cross a module boundary. Reinstall the exact certified
-- preparation/dependency equations and the integration collector cache here.
attribute [local cbv_opaque] Frontend.prepare Frontend.dependencyDeclarations Konst.collectFunctions
attribute [local cbv_eval] source_preparation source_dependencies source_collection

-- Keep substitution at its canonical producer too. The collector result
-- enters this traversal directly, before a stored descriptor is projected.
private theorem source_pipeline_selected :
    Konst.konstErsetzePipeline sourceOriginal.val =
      Konst.ersetzeItems sourceCollectionOutput.val sourceOriginal.val :=
  congrArg (fun produced : Except String (List UKonstFn) =>
    produced.bind (fun functions => Konst.ersetzeItems functions sourceOriginal.val))
    sourceCollectionOutput.property

private def sourceReplacementOutput : {actual : List SItemTief //
    Konst.konstErsetzePipeline sourceOriginal.val = .ok actual} := by
  refine ⟨?_, by
    rw [source_pipeline_selected]
    cbv <;> exact Eq.refl _⟩

private def sourceReplaced : {actual : List SItemTief //
    Konst.ersetzeItems sourceCollected.val sourceOriginal.val = .ok actual} := by
  refine ⟨sourceReplacementOutput.val, ?_⟩
  exact source_pipeline_selected.symm.trans sourceReplacementOutput.property

private theorem source_runtime_metadata :
    ExportMetadata.check (Konst.ohneKonst sourceOriginal.val) = .ok () := by cbv

private theorem source_replaced_metadata :
    Konst.checkErsetzt sourceOriginal.val sourceReplaced.val = .ok () := by cbv

private theorem source_pipeline :
    Konst.konstErsetzePipeline sourceOriginal.val = .ok sourceReplaced.val :=
  sourceReplacementOutput.property

private theorem source_metadata : Konst.checkSourceMetadata sourceOriginal.val = .ok () := by
  rw [Konst.checkSourceMetadata_from_scopes sourceOriginal.val sourceScopes.val
    source_has_const sourceScopes.property]
  simp only [source_values, source_types, sourceCollected.property, bind, Except.bind,
    sourceReplaced.property, source_runtime_metadata, source_replaced_metadata]

private theorem source_aliases :
    sourceOriginal.val.all (Frontend.checkAliasMeaning sourceScopes.val.scope.types) = true :=
  (Bool.and_eq_true_iff.mp (checked_scope_meaning _ _ sourceScopes.property)).1
private theorem source_constants : sourceOriginal.val.all (Frontend.checkConstantMeaning
    sourceScopes.val.scope.types sourceScopes.val.scope.functions sourceScopes.val.scope.values) = true :=
  (Bool.and_eq_true_iff.mp (checked_scope_meaning _ _ sourceScopes.property)).2

private def sourceTail : SourceTail sourceInput :=
  SourceTail.ofOriginal sourceInput sourceOriginal.val sourceOriginal.property
    source_metadata sourceOrder.val sourceOrder.property sourceScopes.val sourceScopes.property
    source_aliases source_constants

end Gabbro.Stage0.SourceWitness
