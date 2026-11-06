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

-- Normalize the one actual descriptor before its result type becomes a
-- Scalar declaration index. Its fields are inferred from the checked
-- collector result, not copied from the expected source or from prepare.
private def negativeDescriptor : {actual : UKonstFn //
    sourceCollectionOutput.val = [actual]} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private def negativeFunction :
    {actual : (Sigma fun lo : Int => Sigma fun hi : Int =>
      Konst.Scalar.SourceFunction negativeDescriptor.val lo hi) //
      Konst.Scalar.elaborate negativeDescriptor.val = .ok actual} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

-- The canonical call retains argument meaning, both contracts, the candidate
-- agreement, exact range, operation costs and the ordinary G-call certificate.
private def negativeCall :
    {actual : Konst.Scalar.CheckedCall negativeDescriptor.val [negativeDescriptor.val]
      negativeDescriptor.val.constants [] //
      Konst.Scalar.checkCall negativeDescriptor.val [negativeDescriptor.val]
        negativeDescriptor.val.constants [] = .ok actual} := by
  refine ⟨?_, ?_⟩
  unfold Konst.Scalar.checkCall
  rw [negativeFunction.property]
  dsimp only [bind, Except.bind]
  cbv <;> exact Eq.refl _

-- Select just the delivered source literal before the statement traversal
-- needs it; no final source or compiler outcome is assumed here.
private def negativeSyntax : {actual : SExpr //
    (Konst.Scalar.checkCall negativeDescriptor.val [negativeDescriptor.val]
      negativeDescriptor.val.constants []).map
        (fun checked => Konst.literalVonInt checked.value) = .ok actual} := by
  refine ⟨?_, ?_⟩
  rw [negativeCall.property]
  cbv <;> exact Eq.refl _

private theorem negative_replaced :
    Konst.ersetzeSExprIn [] [negativeDescriptor.val] (.call "negative" []) =
      .ok negativeSyntax.val := by
  have quoted : (Except.ok (Konst.literalVonInt negativeCall.val.value) :
      Except String SExpr) = .ok negativeSyntax.val := by
    simpa only [negativeCall.property, Except.map] using negativeSyntax.property
  have named : negativeDescriptor.val.name = "negative" := by cbv
  have arguments : Konst.ersetzeSExprListIn [] [negativeDescriptor.val] [] = .ok [] := rfl
  have found : [negativeDescriptor.val].find? (fun k => strEq k.name "negative") =
      some negativeDescriptor.val := by simp [named, strEq]
  have globals : negativeDescriptor.val.constants.filter
      (fun entry => !([] : List String).contains entry.1) =
      negativeDescriptor.val.constants := by simp
  simp only [Konst.ersetzeSExprIn, arguments, found, globals, List.map_nil,
    Konst.geschlossenSExprListB, Bool.not_true, Bool.false_eq_true, ite_false]
  have integer : ∃ lo hi, negativeDescriptor.val.erg = .int lo hi := by
    refine ⟨?_, ?_, ?_⟩
    cbv <;> exact Eq.refl _
  obtain ⟨lo, hi, result⟩ := integer
  simpa only [Konst.checkReplacement, result, negativeCall.property, bind, Except.bind,
    pure, Except.pure] using quoted

section replacementTraversal
-- Keep the certified descriptor at a stable name while the existing traversal
-- runs. This prevents its successful call equation from being lost after the
-- evaluator has independently expanded the descriptor's type environment.
attribute [local cbv_opaque] negativeDescriptor
attribute [local cbv_eval] negative_replaced

private def sourceReplacementOutput : {actual : List SItemTief //
    Konst.konstErsetzePipeline sourceOriginal.val = .ok actual} := by
  refine ⟨?_, by
    rw [source_pipeline_selected, negativeDescriptor.property]
    cbv <;> exact Eq.refl _⟩

end replacementTraversal

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
