module
public import Stage0.Frontend.Witnesses.Constants.SourcePackets
public import Stage0.Frontend.Witnesses.Constants.Lexical
import Grammatik.Parser.Elab.Konst.Values.WitnessReaders
import Init.Data.String.Lemmas.Intercalate
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

import all Stage0.Profil
import all Stage0.Frontend.AliasOrder
import all Stage0.Frontend.Correctness
import all Stage0.Frontend.Environments
import all Stage0.Frontend.EnvironmentsPart1
import all Stage0.Frontend.DependentScopes
import all Stage0.Frontend.DependentScopesa
import all Stage0.Frontend.Functions
import all Stage0.Frontend.Guard
import all Stage0.Frontend.Constants.ConstantScopes
import all Stage0.Frontend.Constants.ConstantMeaning

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

-- Keep the unused float target and the generic normalization proof symbolic.
attribute [local cbv_opaque] uFloatLimit Frontend.normalize
attribute [local cbv_eval] String.intercalate_singleton

/-- The canonical parser still supplies the public selected item list. -/
theorem increment_parsed :
    (parseTopTief (incrementScan.tokens ++ [.ende])).toOption.isSome = true := by cbv

def incrementItems : List SItemTief :=
  (parseTopTief (incrementScan.tokens ++ [.ende])).toOption.get increment_parsed

/-- Infer both complete constructors from their real producer equations before checking any field. -/
def incrementInput : SourceInput Gabbro.Stage0.Frontend.ConstWitness.text := by
  refine {
    tokens := incrementScan.tokens ++ [.ende]
    items := ?items
    lexed := increment_lexed
    parsed := ?parsed
    prepared := ?prepared
    preparation := ?preparation
    visibility := ?visibility
    compileTime := ?compileTime }
  case parsed => cbv <;> exact Eq.refl _
  case preparation => cbv <;> exact Eq.refl _
  case visibility => cbv
  case compileTime => cbv

/-- The public getter receives the already proved whole profile result by exact-domain transport. -/
theorem increment_prepared :
    (Profil.prepareItems {} incrementItems).toOption.isSome = true := by
  obtain ⟨prepared, origin, _, _⟩ :=
    SourceInput.prepared_selected incrementInput increment_lexed
      (items := incrementItems) (by exact Gabbro.Grammatik.except_ok_get increment_parsed)
  rw [origin]
  rfl

/-- Certify whole alias/scope constructor results before their dependent meaning projections. -/
def incrementTail : SourceTail incrementInput := by
  refine {
    metadata := ?metadata
    order := ?order
    ordered := ?ordered
    derived := ?derived
    elaborated := ?elaborated
    aliases := ?aliases
    constants := ?constants }
  case metadata => cbv <;> exact Eq.refl _
  case ordered => cbv <;> exact Eq.refl _
  case elaborated => cbv <;> exact Eq.refl _
  case aliases => cbv
  case constants => cbv

theorem increment_metadata :
    Konst.checkSourceMetadata incrementInput.original = .ok () := incrementTail.metadata

theorem increment_ordered :
    (Frontend.orderAliases incrementInput.original).toOption.isSome = true := by
  rw [incrementTail.ordered]
  rfl

theorem increment_scopes :
    (Frontend.elaborateConstantScopes incrementInput.original).toOption.isSome = true := by
  rw [incrementTail.elaborated]
  rfl

/-- The canonical parser still supplies the public selected item list. -/
theorem initializer_parsed :
    (parseTopTief (initializerScan.tokens ++ [.ende])).toOption.isSome = true := by cbv

def initializerItems : List SItemTief :=
  (parseTopTief (initializerScan.tokens ++ [.ende])).toOption.get initializer_parsed

/-- Infer both complete constructors from their real producer equations before checking any field. -/
def initializerInput : SourceInput Gabbro.Stage0.Frontend.ConstWitness.initializerText := by
  refine {
    tokens := initializerScan.tokens ++ [.ende]
    items := ?items
    lexed := initializer_lexed
    parsed := ?parsed
    prepared := ?prepared
    preparation := ?preparation
    visibility := ?visibility
    compileTime := ?compileTime }
  case parsed => cbv <;> exact Eq.refl _
  case preparation => cbv <;> exact Eq.refl _
  case visibility => cbv
  case compileTime => cbv

/-- The public getter receives the already proved whole profile result by exact-domain transport. -/
theorem initializer_prepared :
    (Profil.prepareItems {} initializerItems).toOption.isSome = true := by
  obtain ⟨prepared, origin, _, _⟩ :=
    SourceInput.prepared_selected initializerInput initializer_lexed
      (items := initializerItems) (by exact Gabbro.Grammatik.except_ok_get initializer_parsed)
  rw [origin]
  rfl

/-- Cache the existing collector result before evaluating its canonical typed scalar fold. -/
def initializerScopePreparation :
    { prepared : Frontend.Prepared // Frontend.prepare initializerInput.original = prepared } := by
  refine ⟨?prepared, ?origin⟩
  case origin => cbv <;> exact Eq.refl _

/-- The entire value list is inferred from the original typed fold, never supplied as a snapshot. -/
def initializerScalarFold :
    { values : List (String × Int) //
      Frontend.typedConstants initializerScopePreparation.val.env
        initializerScopePreparation.val.fns initializerInput.original [] = some values } := by
  refine ⟨?values, ?origin⟩
  case origin => cbv <;> exact Eq.refl _

theorem initializer_scalar_origin :
    Frontend.typedConstants (Frontend.prepare initializerInput.original).env
      (Frontend.prepare initializerInput.original).fns initializerInput.original [] =
        some initializerScalarFold.val := by
  rw [initializerScopePreparation.property]
  exact initializerScalarFold.property

theorem initializer_alias_stability :
    uAliase initializerScalarFold.val (Frontend.prepare initializerInput.original).expanded =
      (Frontend.prepare initializerInput.original).env := by
  rw [initializerScopePreparation.property]
  cbv

/-- Use the canonical conservative constructor, retaining its full original fold certificate. -/
def initializerConservative : Frontend.DerivedScopes initializerInput.original := by
  refine ⟨Frontend.evaluatedScopes initializerInput.original initializerScalarFold.val
    initializer_scalar_origin, ?stable⟩
  case stable =>
    change uAliase initializerScalarFold.val (Frontend.prepare initializerInput.original).expanded =
      (Frontend.prepare initializerInput.original).env
    exact initializer_alias_stability

theorem initializer_derive_origin :
    Frontend.deriveScopes initializerInput.original = .ok initializerConservative := by
  unfold Frontend.deriveScopes
  split
  · rename_i rejected
    cases rejected.symm.trans initializer_scalar_origin
  · rename_i values selected
    have same : values = initializerScalarFold.val :=
      Option.some.inj (selected.symm.trans initializer_scalar_origin)
    subst values
    split
    · rfl
    · rename_i rejected
      exact False.elim (rejected initializer_alias_stability)

/-- Dependency ordering remains the real checked producer, with its complete permutation. -/
def initializerAliasOrder :
    { order : Frontend.AliasOrder initializerInput.original //
      Frontend.orderAliases initializerInput.original = .ok order } := by
  refine ⟨?order, ?origin⟩
  case origin => cbv <;> exact Eq.refl _

def initializerConstantOrder :
    { order : Frontend.ConstantOrder initializerInput.original //
      Frontend.orderConstants initializerInput.original = .ok order } := by
  refine ⟨?order, ?origin⟩
  case origin => cbv <;> exact Eq.refl _

theorem initializer_functions_complete :
    (Frontend.constantFunctions initializerConservative.scope.types initializerInput.original).length =
      initializerConservative.scope.functions.length := by
  dsimp only [initializerConservative, Frontend.evaluatedScopes, Frontend.Scopes.types]
  rw [initializerScopePreparation.property]
  cbv

theorem initializer_aliases_resolved :
    Frontend.aliasesResolved initializerConservative.scope.declared initializerInput.original = true := by
  dsimp only [initializerConservative, Frontend.evaluatedScopes]
  rw [initializerScopePreparation.property]
  cbv

theorem initializer_scope_meaning : Frontend.scopeMeaning initializerConservative = true := by
  dsimp only [Frontend.scopeMeaning, initializerConservative,
    Frontend.evaluatedScopes, Frontend.Scopes.types]
  rw [initializerScopePreparation.property]
  cbv

theorem initializer_conservative_kept :
    Frontend.elaborateScopes initializerInput.original = .ok initializerConservative :=
  Frontend.elaborateScopes_preserves initializerInput.original initializerConservative
    initializerAliasOrder.val initializerAliasOrder.property initializer_derive_origin
    initializer_functions_complete initializer_aliases_resolved
    (Bool.and_eq_true_iff.mp initializer_scope_meaning).1

theorem constant_scopes_preserved {items : List SItemTief}
    (order : Frontend.ConstantOrder items) (result : Frontend.DerivedScopes items)
    (ordered : Frontend.orderConstants items = .ok order)
    (elaborated : Frontend.elaborateScopes items = .ok result)
    (meaning : Frontend.scopeMeaning result = true) :
    Frontend.elaborateConstantScopes items = .ok result := by
  unfold Frontend.elaborateConstantScopes
  rw [ordered]
  dsimp only [bind, Except.bind]
  rw [elaborated]
  simp only [meaning, ↓reduceIte, pure, Except.pure]

/-- Compose the real dependency, scalar, alias, and meaning phases without rerunning their graph. -/
def initializerTail : SourceTail initializerInput where
  metadata := by cbv
  order := initializerAliasOrder.val
  ordered := initializerAliasOrder.property
  derived := initializerConservative
  elaborated := by
    exact constant_scopes_preserved initializerConstantOrder.val initializerConservative
      initializerConstantOrder.property initializer_conservative_kept initializer_scope_meaning
  aliases := (Bool.and_eq_true_iff.mp initializer_scope_meaning).1
  constants := (Bool.and_eq_true_iff.mp initializer_scope_meaning).2

theorem initializer_metadata :
    Konst.checkSourceMetadata initializerInput.original = .ok () := initializerTail.metadata

theorem initializer_ordered :
    (Frontend.orderAliases initializerInput.original).toOption.isSome = true := by
  rw [initializerTail.ordered]
  rfl

theorem initializer_scopes :
    (Frontend.elaborateConstantScopes initializerInput.original).toOption.isSome = true := by
  rw [initializerTail.elaborated]
  rfl

end Gabbro.Stage0.Frontend.ConstPhases
