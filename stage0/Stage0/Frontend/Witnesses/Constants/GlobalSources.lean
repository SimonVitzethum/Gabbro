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
theorem globalText_parsed :
    (parseTopTief (globalTextScan.tokens ++ [.ende])).toOption.isSome = true := by cbv

def globalTextItems : List SItemTief :=
  (parseTopTief (globalTextScan.tokens ++ [.ende])).toOption.get globalText_parsed

/-- Infer both complete constructors from their real producer equations before checking any field. -/
def globalTextInput : SourceInput Gabbro.Stage0.Frontend.ConstValuesWitness.globalText := by
  refine {
    tokens := globalTextScan.tokens ++ [.ende]
    items := ?items
    lexed := globalText_lexed
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
theorem globalText_prepared :
    (Profil.prepareItems {} globalTextItems).toOption.isSome = true := by
  obtain ⟨prepared, origin, _, _⟩ :=
    SourceInput.prepared_selected globalTextInput globalText_lexed
      (items := globalTextItems) (by exact Gabbro.Grammatik.except_ok_get globalText_parsed)
  rw [origin]
  rfl

/-- Certify whole alias/scope constructor results before their dependent meaning projections. -/
def globalTextTail : SourceTail globalTextInput := by
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

theorem globalText_metadata :
    Konst.checkSourceMetadata globalTextInput.original = .ok () := globalTextTail.metadata

theorem globalText_ordered :
    (Frontend.orderAliases globalTextInput.original).toOption.isSome = true := by
  rw [globalTextTail.ordered]
  rfl

theorem globalText_scopes :
    (Frontend.elaborateConstantScopes globalTextInput.original).toOption.isSome = true := by
  rw [globalTextTail.elaborated]
  rfl

/-- The canonical parser still supplies the public selected item list. -/
theorem qualifiedText_parsed :
    (parseTopTief (qualifiedTextScan.tokens ++ [.ende])).toOption.isSome = true := by cbv

def qualifiedTextItems : List SItemTief :=
  (parseTopTief (qualifiedTextScan.tokens ++ [.ende])).toOption.get qualifiedText_parsed

/-- Infer both complete constructors from their real producer equations before checking any field. -/
def qualifiedTextInput : SourceInput Gabbro.Stage0.Frontend.ConstValuesWitness.qualifiedText := by
  refine {
    tokens := qualifiedTextScan.tokens ++ [.ende]
    items := ?items
    lexed := qualifiedText_lexed
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
theorem qualifiedText_prepared :
    (Profil.prepareItems {} qualifiedTextItems).toOption.isSome = true := by
  obtain ⟨prepared, origin, _, _⟩ :=
    SourceInput.prepared_selected qualifiedTextInput qualifiedText_lexed
      (items := qualifiedTextItems) (by exact Gabbro.Grammatik.except_ok_get qualifiedText_parsed)
  rw [origin]
  rfl

-- Normalize the actual prepared/pre108/uMembers output before introducing any
-- AliasOrder or DerivedScopes index. No source declaration is supplied by hand.
def qualifiedOriginalPacket :
    { actual : List SItemTief // qualifiedTextInput.original = actual } := by
  refine ⟨?original, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

-- Infer the complete results at the already normalized, certified source list.
def qualifiedOrderPacket :
    { actual : Frontend.AliasOrder qualifiedOriginalPacket.val //
      Frontend.orderAliases qualifiedOriginalPacket.val = .ok actual } := by
  refine ⟨?actual, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

def qualifiedScopesPacket :
    { actual : Frontend.DerivedScopes qualifiedOriginalPacket.val //
      Frontend.elaborateConstantScopes qualifiedOriginalPacket.val = .ok actual } := by
  refine ⟨?actual, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

private theorem qualified_metadata :
    Konst.checkSourceMetadata qualifiedOriginalPacket.val = .ok () := by cbv

private theorem qualified_aliases :
    qualifiedOriginalPacket.val.all
      (Frontend.checkAliasMeaning qualifiedScopesPacket.val.scope.types) = true := by cbv

private theorem qualified_constants :
    qualifiedOriginalPacket.val.all (Frontend.checkConstantMeaning qualifiedScopesPacket.val.scope.types
      qualifiedScopesPacket.val.scope.functions qualifiedScopesPacket.val.scope.values) = true := by cbv

/-- Reindex the complete checked packet once at the original input. -/
def qualifiedTextTail : SourceTail qualifiedTextInput :=
  SourceTail.ofOriginal qualifiedTextInput qualifiedOriginalPacket.val qualifiedOriginalPacket.property
    (by exact qualified_metadata) qualifiedOrderPacket.val qualifiedOrderPacket.property
    qualifiedScopesPacket.val qualifiedScopesPacket.property
    (by exact qualified_aliases) (by exact qualified_constants)

theorem qualifiedText_metadata :
    Konst.checkSourceMetadata qualifiedTextInput.original = .ok () := qualifiedTextTail.metadata

theorem qualifiedText_ordered :
    (Frontend.orderAliases qualifiedTextInput.original).toOption.isSome = true := by
  rw [qualifiedTextTail.ordered]
  rfl

theorem qualifiedText_scopes :
    (Frontend.elaborateConstantScopes qualifiedTextInput.original).toOption.isSome = true := by
  rw [qualifiedTextTail.elaborated]
  rfl

end Gabbro.Stage0.Frontend.ConstPhases
