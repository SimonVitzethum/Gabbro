module
public import Stage0.SourceWitness.Owners
import all Stage0.SourceWitness.Owners

@[expose] public section
namespace Gabbro.Stage0.SourceWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Frontend.ConstPhases
set_option maxRecDepth 2000
set_option maxHeartbeats 100000

/-- The original complete character pin; only its scanner proof is segmented. -/
def characters : List Char := ['t', 'y', 'p', 'e', ' ', 'A', ' ', '=', ' ', 'i', '8', ';', ' ', 't', 'y', 'p', 'e', ' ', 'B', ' ', '=', ' ', 'A', ';', ' ', 'c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 'n', 'e', 'g', 'a', 't', 'i', 'v', 'e', '(', ')', ' ', '-', '>', ' ', 'B', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', '0', ' ', '-', ' ', '1', ';', ' ', '}', ' ', 'c', 'o', 'n', 's', 't', ' ', 'N', 'E', 'G', 'A', 'T', 'I', 'V', 'E', ' ', ':', ' ', 'B', ' ', '=', ' ', 'n', 'e', 'g', 'a', 't', 'i', 'v', 'e', '(', ')', ';', ' ', 'c', 'o', 'n', 's', 't', ' ', 'C', ' ', ':', ' ', 'B', ' ', '=', ' ', 'N', 'E', 'G', 'A', 'T', 'I', 'V', 'E', ' ', '+', ' ', '4', '3', ';', ' ', 't', 'y', 'p', 'e', ' ', 'B', 'o', 'u', 'n', 'd', ' ', '=', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', 'C', ';', ' ', 't', 'y', 'p', 'e', ' ', 'F', 'i', 'n', 'a', 'l', ' ', '=', ' ', 'B', 'o', 'u', 'n', 'd', ';', ' ', 'c', 'o', 'n', 's', 't', ' ', 'A', 'N', 'S', 'W', 'E', 'R', ' ', ':', ' ', 'F', 'i', 'n', 'a', 'l', ' ', '=', ' ', 'C', ';', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'E', 'm', 'p', 't', 'y', ' ', 'c', 'o', 'u', 'n', 't', ' ', '4', '2', '9', '4', '9', '6', '7', '2', '9', '6', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', '}', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'F', 'i', 'n', 'a', 'l', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'A', 'N', 'S', 'W', 'E', 'R', ';', ' ', '}']
def text : String := String.ofList characters

private def sourcePiece0 : ScanPiece ['t', 'y', 'p', 'e', ' ', 'A', ' ', '=', ' ', 'i', '8', ';', ' ', 't', 'y', 'p', 'e', ' ', 'B', ' ', '=', ' ', 'A', ';', ' '] := by
  let tokens := ((lexL ['t', 'y', 'p', 'e', ' ', 'A', ' ', '=', ' ', 'i', '8', ';', ' ', 't', 'y', 'p', 'e', ' ', 'B', ' ', '=', ' ', 'A', ';', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 8, equation := ?_ }
  intro rest fuel
  cbv

private def sourcePiece1 : ScanPiece ['c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 'n', 'e', 'g', 'a', 't', 'i', 'v', 'e', '(', ')', ' ', '-', '>', ' ', 'B', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', '0', ' ', '-', ' ', '1', ';', ' ', '}', ' '] := by
  let tokens := ((lexL ['c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 'n', 'e', 'g', 'a', 't', 'i', 'v', 'e', '(', ')', ' ', '-', '>', ' ', 'B', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', '0', ' ', '-', ' ', '1', ';', ' ', '}', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 11, equation := ?_ }
  intro rest fuel
  cbv

private def sourcePiece2 : ScanPiece ['c', 'o', 'n', 's', 't', ' ', 'N', 'E', 'G', 'A', 'T', 'I', 'V', 'E', ' ', ':', ' ', 'B', ' ', '=', ' ', 'n', 'e', 'g', 'a', 't', 'i', 'v', 'e', '(', ')', ';', ' '] := by
  let tokens := ((lexL ['c', 'o', 'n', 's', 't', ' ', 'N', 'E', 'G', 'A', 'T', 'I', 'V', 'E', ' ', ':', ' ', 'B', ' ', '=', ' ', 'n', 'e', 'g', 'a', 't', 'i', 'v', 'e', '(', ')', ';', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 6, equation := ?_ }
  intro rest fuel
  cbv

private def sourcePiece3 : ScanPiece ['c', 'o', 'n', 's', 't', ' ', 'C', ' ', ':', ' ', 'B', ' ', '=', ' ', 'N', 'E', 'G', 'A', 'T', 'I', 'V', 'E', ' ', '+', ' ', '4', '3', ';', ' '] := by
  let tokens := ((lexL ['c', 'o', 'n', 's', 't', ' ', 'C', ' ', ':', ' ', 'B', ' ', '=', ' ', 'N', 'E', 'G', 'A', 'T', 'I', 'V', 'E', ' ', '+', ' ', '4', '3', ';', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 8, equation := ?_ }
  intro rest fuel
  cbv

private def sourcePiece4 : ScanPiece ['t', 'y', 'p', 'e', ' ', 'B', 'o', 'u', 'n', 'd', ' ', '=', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', 'C', ';', ' ', 't', 'y', 'p', 'e', ' ', 'F', 'i', 'n', 'a', 'l', ' ', '=', ' ', 'B', 'o', 'u', 'n', 'd', ';', ' '] := by
  let tokens := ((lexL ['t', 'y', 'p', 'e', ' ', 'B', 'o', 'u', 'n', 'd', ' ', '=', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', 'C', ';', ' ', 't', 'y', 'p', 'e', ' ', 'F', 'i', 'n', 'a', 'l', ' ', '=', ' ', 'B', 'o', 'u', 'n', 'd', ';', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 12, equation := ?_ }
  intro rest fuel
  cbv

private def sourcePiece5 : ScanPiece ['c', 'o', 'n', 's', 't', ' ', 'A', 'N', 'S', 'W', 'E', 'R', ' ', ':', ' ', 'F', 'i', 'n', 'a', 'l', ' ', '=', ' ', 'C', ';', ' '] := by
  let tokens := ((lexL ['c', 'o', 'n', 's', 't', ' ', 'A', 'N', 'S', 'W', 'E', 'R', ' ', ':', ' ', 'F', 'i', 'n', 'a', 'l', ' ', '=', ' ', 'C', ';', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 6, equation := ?_ }
  intro rest fuel
  cbv

private def sourcePiece6 : ScanPiece ['t', 'a', 'b', 'l', 'e', ' ', 'E', 'm', 'p', 't', 'y', ' ', 'c', 'o', 'u', 'n', 't', ' ', '4', '2', '9', '4', '9', '6', '7', '2', '9', '6', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', '}', ' ', '}', ' '] := by
  let tokens := ((lexL ['t', 'a', 'b', 'l', 'e', ' ', 'E', 'm', 'p', 't', 'y', ' ', 'c', 'o', 'u', 'n', 't', ' ', '4', '2', '9', '4', '9', '6', '7', '2', '9', '6', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', '}', ' ', '}', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 8, equation := ?_ }
  intro rest fuel
  cbv

private def sourcePiece7 : ScanPiece ['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'F', 'i', 'n', 'a', 'l', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'A', 'N', 'S', 'W', 'E', 'R', ';', ' ', '}'] := by
  let tokens := ((lexL ['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'F', 'i', 'n', 'a', 'l', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'A', 'N', 'S', 'W', 'E', 'R', ';', ' ', '}']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 8, equation := ?_ }
  intro rest fuel
  cbv

private def sourceScan : ScanPiece characters := (((((((sourcePiece0).append sourcePiece1).append sourcePiece2).append sourcePiece3).append sourcePiece4).append sourcePiece5).append sourcePiece6).append sourcePiece7

private theorem source_lexed : lex text = .ok (sourceScan.tokens ++ [.ende]) := by
  rw [text, lex_ofList]
  exact sourceScan.lexed (by cbv)

attribute [local cbv_opaque] uFloatLimit Frontend.normalize
attribute [local cbv_eval] Konst.Values.expression.eq_def Konst.Values.payloadExpression.eq_def
  Konst.Values.reify.eq_def Konst.Values.reifyPayload.eq_def
  Konst.Values.WitnessReaders.reader_bool Konst.Values.WitnessReaders.reader_int
  Konst.Values.WitnessReaders.reader_text Konst.Values.WitnessReaders.reader_sum
  Konst.Values.WitnessReaders.reader_payload Konst.Values.WitnessReaders.reader_empty
  Konst.Values.WitnessReaders.reader_missing

private def sourceInput : SourceInput text := by
  refine {
    tokens := sourceScan.tokens ++ [.ende]
    items := ?items
    lexed := source_lexed
    parsed := ?parsed
    prepared := ?prepared
    preparation := ?preparation
    visibility := ?visibility
    compileTime := ?compileTime }
  case parsed => cbv <;> exact Eq.refl _
  case preparation => cbv <;> exact Eq.refl _
  case visibility => cbv
  case compileTime => cbv

private def sourceOriginal : { actual : List SItemTief // sourceInput.original = actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private def sourceOrder : { actual : Frontend.AliasOrder sourceOriginal.val //
    Frontend.orderAliases sourceOriginal.val = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private def sourcePreparation : { actual : Frontend.Prepared //
    Frontend.prepare sourceOriginal.val = actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private def sourceDependencies :
    { actual : List (Frontend.DependencyName × List Frontend.DependencyName) //
      Frontend.dependencyDeclarations sourceOriginal.val = actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private theorem source_preparation : Frontend.prepare sourceOriginal.val = sourcePreparation.val :=
  sourcePreparation.property
private theorem source_dependencies :
    Frontend.dependencyDeclarations sourceOriginal.val = sourceDependencies.val :=
  sourceDependencies.property

-- Discovery revisits the same original declarations. Retain their actual
-- preparation and graph rather than recomputing either inside each callback.
attribute [local cbv_opaque] Frontend.prepare Frontend.dependencyDeclarations
attribute [local cbv_eval] source_preparation source_dependencies

private def sourceScopes : { actual : Frontend.DerivedScopes sourceOriginal.val //
    Frontend.elaborateConstantScopes sourceOriginal.val = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private theorem checked_scope_meaning (items : List SItemTief)
    (result : Frontend.DerivedScopes items)
    (produced : Frontend.elaborateConstantScopes items = .ok result) :
    Frontend.scopeMeaning result = true := by
  have discovery (order : Frontend.ConstantOrder items)
      (accepted : (do
        let aliases ← Frontend.orderAliases items
        let candidate ← Frontend.discoverScopes items (items.length + 1)
          (Frontend.prepare items).initial ⟨aliases.ordered, aliases.permutation⟩
          ⟨order.ordered, order.permutation⟩
        if Frontend.scopeMeaning candidate then pure candidate
        else throw "compile-time declarations do not match their canonical final meaning") = .ok result) :
      Frontend.scopeMeaning result = true := by
    cases aliasesEq : Frontend.orderAliases items with
    | error error =>
      have impossible : (Except.error error : Except String (Frontend.DerivedScopes items)) = .ok result := by
        simpa only [aliasesEq, bind, Except.bind] using accepted
      cases impossible
    | ok aliases =>
      try simp only [aliasesEq, bind, Except.bind] at accepted
      cases candidateEq : Frontend.discoverScopes items (items.length + 1)
          (Frontend.prepare items).initial ⟨aliases.ordered, aliases.permutation⟩
          ⟨order.ordered, order.permutation⟩ with
      | error error =>
        have impossible : (Except.error error : Except String (Frontend.DerivedScopes items)) = .ok result := by
          simpa only [candidateEq, bind, Except.bind] using accepted
        cases impossible
      | ok candidate =>
        try simp only [candidateEq, bind, Except.bind] at accepted
        split at accepted
        · rename_i meaning
          cases Except.ok.inj accepted
          exact meaning
        · cases accepted
  unfold Frontend.elaborateConstantScopes at produced
  cases orderEq : Frontend.orderConstants items with
  | error error =>
    have impossible : (Except.error error : Except String (Frontend.DerivedScopes items)) = .ok result := by
      simpa only [orderEq, bind, Except.bind] using produced
    cases impossible
  | ok order =>
    simp only [orderEq, bind, Except.bind] at produced
    cases previousEq : Frontend.elaborateScopes items with
    | error error =>
      simp only [previousEq] at produced
      exact discovery order produced
    | ok previous =>
      simp only [previousEq] at produced
      split at produced
      · rename_i meaning
        cases Except.ok.inj produced
        exact meaning
      · exact discovery order produced

-- Read only primitive scope fields before any SourceTail equality transport.
-- These are the actual discovery outputs, not a conservative prepare snapshot.
private abbrev ScopeData :=
  List (String × Int) × List (String × (Int × Int)) × List UKonstFn

-- Fix the primitive output type at the actual producer, before inspecting
-- the previously certified proof-carrying DerivedScopes value. The same
-- discovery, dependency and final-meaning guards all run inside this map.
private def sourceScopeOutput : {actual : ScopeData //
    (Frontend.elaborateConstantScopes sourceOriginal.val).map
      (fun result : Frontend.DerivedScopes sourceOriginal.val =>
        (result.scope.values, result.scope.types, result.scope.functions)) = .ok actual} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private def sourceScopeData : {actual : ScopeData //
    (sourceScopes.val.scope.values, sourceScopes.val.scope.types,
      sourceScopes.val.scope.functions) = actual} := by
  refine ⟨sourceScopeOutput.val, ?_⟩
  have selected : (Frontend.elaborateConstantScopes sourceOriginal.val).map
      (fun result : Frontend.DerivedScopes sourceOriginal.val =>
        (result.scope.values, result.scope.types, result.scope.functions)) =
      .ok (sourceScopes.val.scope.values, sourceScopes.val.scope.types,
        sourceScopes.val.scope.functions) :=
    congrArg (fun produced : Except String (Frontend.DerivedScopes sourceOriginal.val) =>
      produced.map (fun result : Frontend.DerivedScopes sourceOriginal.val =>
        (result.scope.values, result.scope.types, result.scope.functions))) sourceScopes.property
  exact Except.ok.inj (selected.symm.trans sourceScopeOutput.property)

private theorem source_values : sourceScopes.val.scope.values = sourceScopeData.val.1 :=
  congrArg Prod.fst sourceScopeData.property
private theorem source_types : sourceScopes.val.scope.types = sourceScopeData.val.2.1 :=
  congrArg (fun data : ScopeData => data.2.1) sourceScopeData.property

private theorem source_has_const : sourceOriginal.val.any
    (fun | .fnT signature _ => strEq signature.art "const" | _ => false) = true := by cbv

-- Close the collector and substitution independently. Both certificates keep
-- the original declarations and all unused/original metadata obligations.
-- Consume the actual scope-producing collector before projecting a stored
-- scope tuple; its fixed result type contains only the function descriptors.
private def sourceCollectionOutput : {actual : List UKonstFn //
    Konst.collectFunctions sourceOriginal.val = .ok actual} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private theorem source_collection :
    Konst.collectFunctions sourceOriginal.val = .ok sourceCollectionOutput.val :=
  sourceCollectionOutput.property

attribute [local cbv_opaque] Konst.collectFunctions
attribute [local cbv_eval] source_collection

private def sourceCollected : {actual : List UKonstFn //
    Konst.collectFunctionsWith sourceOriginal.val sourceScopeData.val.1
      sourceScopeData.val.2.1 = .ok actual} := by
  refine ⟨sourceCollectionOutput.val, ?_⟩
  have selected := Konst.collectFunctions_from_scopes sourceOriginal.val sourceScopes.val
    source_has_const sourceScopes.property
  have fields := congrArg (fun data : ScopeData =>
    Konst.collectFunctionsWith sourceOriginal.val data.1 data.2.1) sourceScopeData.property
  exact fields.symm.trans (selected.symm.trans sourceCollectionOutput.property)

-- Keep substitution at its canonical producer too. The collector result
-- enters this traversal directly, before a stored descriptor is projected.
private def sourceReplacementOutput : {actual : List SItemTief //
    Konst.konstErsetzePipeline sourceOriginal.val = .ok actual} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private def sourceReplaced : {actual : List SItemTief //
    Konst.ersetzeItems sourceCollected.val sourceOriginal.val = .ok actual} := by
  refine ⟨sourceReplacementOutput.val, ?_⟩
  have selected : Konst.konstErsetzePipeline sourceOriginal.val =
      Konst.ersetzeItems sourceCollectionOutput.val sourceOriginal.val := by
    unfold Konst.konstErsetzePipeline
    rw [sourceCollectionOutput.property] <;> rfl
  exact selected.symm.trans sourceReplacementOutput.property

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
