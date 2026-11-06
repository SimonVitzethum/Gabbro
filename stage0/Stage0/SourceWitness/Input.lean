module
public import Stage0.SourceWitness.InputScopes
public import Stage0.SourceWitness.InputMetadata
import all Stage0.SourceWitness.InputScopes
import all Stage0.SourceWitness.InputMetadata
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

-- Eliminate the original-list equality at a symbolic input first. Successful
-- discovery is deterministic, so the complete tail retains these same fields.
-- No concrete cast or SourceTail proof is unfolded by a later projection.
private theorem original_scope_fields {text : String} (input : SourceInput text)
    (items : List SItemTief) (origin : input.original = items) (tail : SourceTail input)
    (derived : Frontend.DerivedScopes items)
    (produced : Frontend.elaborateConstantScopes items = .ok derived) :
    ((sourceFrom input tail).scopes.values, (sourceFrom input tail).scopes.types,
      (sourceFrom input tail).scopes.functions) =
    (derived.scope.values, derived.scope.types, derived.scope.functions) := by
  cases origin
  have same : tail.derived = derived := Except.ok.inj (tail.elaborated.symm.trans produced)
  cases same
  rfl

private theorem source_scope_fields :
    ((sourceFrom sourceInput sourceTail).scopes.values,
      (sourceFrom sourceInput sourceTail).scopes.types,
      (sourceFrom sourceInput sourceTail).scopes.functions) = sourceScopeData.val :=
  (original_scope_fields sourceInput sourceOriginal.val sourceOriginal.property
    sourceTail sourceScopes.val sourceScopes.property).trans sourceScopeData.property

private def sourcePrepared : {actual : List SItemTief //
    pre108 sourceInput.prepared.elaborierbar = actual} := by
  refine ⟨?actual, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

private abbrev HeaderData := List SItemTief × ScopeData
private def sourceHeaderData : HeaderData := (sourcePrepared.val, sourceScopeData.val)

private theorem source_header_data :
    (pre108 (sourceFrom sourceInput sourceTail).prepared.elaborierbar,
      (sourceFrom sourceInput sourceTail).scopes.values,
      (sourceFrom sourceInput sourceTail).scopes.types,
      (sourceFrom sourceInput sourceTail).scopes.functions) = sourceHeaderData :=
  (congrArg (fun prepared : List SItemTief =>
    (prepared, ((sourceFrom sourceInput sourceTail).scopes.values,
      (sourceFrom sourceInput sourceTail).scopes.types,
      (sourceFrom sourceInput sourceTail).scopes.functions))) sourcePrepared.property).trans
    (congrArg (fun fields : ScopeData => (sourcePrepared.val, fields)) source_scope_fields)

-- Infer the complete expansion pair and complete selected UProg independently
-- before Header introduces any dependent fields or synthetic result metavariables.
-- The expansion has no scope input. Compose the actual profile and module
-- producers so reducing it cannot inspect the unrelated HeaderData scope half.
private def sourceExpansionOutput : {actual : List SItemTief × List (STyp × String) //
    ((Profil.prepareItems {} sourceInput.items).bind fun prepared =>
      Modules.prepare (pre108 prepared.elaborierbar)) = .ok actual} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private def sourceExpansion : {actual : List SItemTief × List (STyp × String) //
    Modules.prepare sourceHeaderData.1 = .ok actual} := by
  refine ⟨sourceExpansionOutput.val, ?_⟩
  have selected : ((Profil.prepareItems {} sourceInput.items).bind fun prepared =>
      Modules.prepare (pre108 prepared.elaborierbar)) =
      Modules.prepare (pre108 sourceInput.prepared.elaborierbar) :=
    congrArg (fun produced : Except String (Profil.Prepared {} sourceInput.items) =>
      produced.bind fun prepared => Modules.prepare (pre108 prepared.elaborierbar))
      sourceInput.preparation
  exact (congrArg Modules.prepare sourcePrepared.property).symm.trans
    (selected.symm.trans sourceExpansionOutput.property)

-- The canonical elaborator revisits the original const pass. Reuse its exact
-- checked result instead of reopening the dependency/scope discovery graph.
attribute [local cbv_opaque] Konst.konstErsetzePipeline Konst.checkSourceMetadata
attribute [local cbv_eval] source_pipeline source_metadata

-- Replay these actual stages with a fixed UProg result before inspecting
-- HeaderData. No source scopes are supplied independently of discovery.
private def sourceElaborationOutput : {actual : UProg //
    ((Profil.prepareItems {} sourceInput.items).bind fun prepared =>
      (Frontend.elaborateConstantScopes (uMembers (pre108 prepared.elaborierbar))).bind
        fun derived =>
          (Frontend.elabWithScopes (pre108 prepared.elaborierbar)
            derived.scope.values derived.scope.types derived.scope.functions
            (Frontend.tableWithEmpty derived.scope.values derived.scope.types)).bind
              (Profil.selectUnit {})) = .ok actual} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

-- Establish the complete equality at a symbolic input/tail. The concrete
-- ofOriginal cast never becomes an elaborator argument or rewrite motive.
private theorem prepared_elaboration {text : String} (input : SourceInput text)
    (tail : SourceTail input) :
    ((Profil.prepareItems {} input.items).bind fun prepared =>
      (Frontend.elaborateConstantScopes (uMembers (pre108 prepared.elaborierbar))).bind
        fun derived =>
          (Frontend.elabWithScopes (pre108 prepared.elaborierbar)
            derived.scope.values derived.scope.types derived.scope.functions
            (Frontend.tableWithEmpty derived.scope.values derived.scope.types)).bind
              (Profil.selectUnit {})) =
    ((Frontend.elabWithScopes (pre108 (sourceFrom input tail).prepared.elaborierbar)
      (sourceFrom input tail).scopes.values (sourceFrom input tail).scopes.types
      (sourceFrom input tail).scopes.functions
      (Frontend.tableWithEmpty (sourceFrom input tail).scopes.values
        (sourceFrom input tail).scopes.types)).bind (Profil.selectUnit {})) := by
  rw [input.preparation]
  dsimp only [bind, Except.bind]
  change ((Frontend.elaborateConstantScopes input.original).bind fun derived =>
    (Frontend.elabWithScopes (pre108 input.prepared.elaborierbar)
      derived.scope.values derived.scope.types derived.scope.functions
      (Frontend.tableWithEmpty derived.scope.values derived.scope.types)).bind
        (Profil.selectUnit {})) =
    ((Frontend.elabWithScopes (pre108 input.prepared.elaborierbar)
      tail.derived.scope.values tail.derived.scope.types tail.derived.scope.functions
      (Frontend.tableWithEmpty tail.derived.scope.values tail.derived.scope.types)).bind
        (Profil.selectUnit {}))
  rw [tail.elaborated]
  rfl

private def sourceElaboration : {actual : UProg //
    ((Frontend.elabWithScopes sourceHeaderData.1 sourceHeaderData.2.1
      sourceHeaderData.2.2.1 sourceHeaderData.2.2.2
      (Frontend.tableWithEmpty sourceHeaderData.2.1 sourceHeaderData.2.2.1)).bind
        (Profil.selectUnit {})) = .ok actual} := by
  refine ⟨sourceElaborationOutput.val, ?_⟩
  have selected := prepared_elaboration sourceInput sourceTail
  have fields := congrArg (fun data : HeaderData =>
    (Frontend.elabWithScopes data.1 data.2.1 data.2.2.1 data.2.2.2
      (Frontend.tableWithEmpty data.2.1 data.2.2.1)).bind (Profil.selectUnit {}))
    source_header_data
  exact fields.symm.trans (selected.symm.trans sourceElaborationOutput.property)

private theorem source_expansion :
    Modules.prepare (pre108 (sourceFrom sourceInput sourceTail).prepared.elaborierbar) =
      .ok sourceExpansion.val :=
  (congrArg (fun data : HeaderData => Modules.prepare data.1) source_header_data).trans
    sourceExpansion.property

private theorem source_elaborated :
    ((Frontend.elabWithScopes (pre108 (sourceFrom sourceInput sourceTail).prepared.elaborierbar)
      (sourceFrom sourceInput sourceTail).scopes.values
      (sourceFrom sourceInput sourceTail).scopes.types
      (sourceFrom sourceInput sourceTail).scopes.functions
      (Frontend.tableWithEmpty (sourceFrom sourceInput sourceTail).scopes.values
        (sourceFrom sourceInput sourceTail).scopes.types)).bind (Profil.selectUnit {})) =
      .ok sourceElaboration.val :=
  (congrArg (fun data : HeaderData =>
    (Frontend.elabWithScopes data.1 data.2.1 data.2.2.1 data.2.2.2
      (Frontend.tableWithEmpty data.2.1 data.2.2.1)).bind (Profil.selectUnit {}))
    source_header_data).trans sourceElaboration.property

private theorem source_constant_gate : Konst.checkSourceConstants sourceInput.original = .ok () := by
  unfold Konst.checkSourceConstants
  split
  · exact sourceTail.metadata
  · rfl

private theorem source_ordinary_gate : sourceInput.original.any Frontend.expansionHeader = false := by
  rw [sourceOriginal.property]
  cbv

private def sourceHeader : Header text where
  source := sourceFrom sourceInput sourceTail
  sourceEq := sourceFrom_eq sourceInput sourceTail
  expanded := sourceExpansion.val.1
  requirements := sourceExpansion.val.2
  expansion := by exact source_expansion
  constants := by exact source_constant_gate
  ordinary := by exact source_ordinary_gate
  metadata := by exact sourceTail.metadata
  candidate := sourceElaboration.val
  elaborated := by exact source_elaborated

end Gabbro.Stage0.SourceWitness
