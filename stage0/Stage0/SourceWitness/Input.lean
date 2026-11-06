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
    | error error => cases accepted
    | ok aliases =>
      try simp only [aliasesEq, bind, Except.bind] at accepted
      cases candidateEq : Frontend.discoverScopes items (items.length + 1)
          (Frontend.prepare items).initial ⟨aliases.ordered, aliases.permutation⟩
          ⟨order.ordered, order.permutation⟩ with
      | error error => cases accepted
      | ok candidate =>
        try simp only [candidateEq, bind, Except.bind] at accepted
        split at accepted
        · rename_i meaning
          cases Except.ok.inj accepted
          exact meaning
        · cases accepted
  unfold Frontend.elaborateConstantScopes at produced
  cases orderEq : Frontend.orderConstants items with
  | error error => cases produced
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

private theorem source_metadata : Konst.checkSourceMetadata sourceOriginal.val = .ok () := by
  rw [Konst.checkSourceMetadata_from_scopes sourceOriginal.val sourceScopes.val
    (by cbv) sourceScopes.property]
  cbv
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

private def sourceHeader : Header text := by
  refine {
    source := sourceFrom sourceInput sourceTail
    sourceEq := sourceFrom_eq sourceInput sourceTail
    expanded := ?expanded
    requirements := ?requirements
    expansion := ?expansion
    constants := ?constants
    ordinary := by
      change sourceInput.original.any Frontend.expansionHeader = false
      rw [sourceOriginal.property]
      cbv
    metadata := sourceTail.metadata
    candidate := ?candidate
    elaborated := ?elaborated }
  case expansion => cbv <;> exact Eq.refl _
  case constants =>
    change Konst.checkSourceConstants sourceInput.original = .ok ()
    unfold Konst.checkSourceConstants
    split
    · exact sourceTail.metadata
    · rfl
  case elaborated => cbv <;> exact Eq.refl _

end Gabbro.Stage0.SourceWitness
