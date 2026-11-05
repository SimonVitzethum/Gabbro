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
theorem boolText_parsed :
    (parseTopTief (boolTextScan.tokens ++ [.ende])).toOption.isSome = true := by cbv

def boolTextItems : List SItemTief :=
  (parseTopTief (boolTextScan.tokens ++ [.ende])).toOption.get boolText_parsed

/-- Infer both complete constructors from their real producer equations before checking any field. -/
def boolTextInput : SourceInput Gabbro.Stage0.Frontend.ConstValuesWitness.boolText := by
  refine {
    tokens := boolTextScan.tokens ++ [.ende]
    items := ?items
    lexed := boolText_lexed
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
theorem boolText_prepared :
    (Profil.prepareItems {} boolTextItems).toOption.isSome = true := by
  obtain ⟨prepared, origin, _, _⟩ :=
    SourceInput.prepared_selected boolTextInput boolText_lexed
      (items := boolTextItems) (by exact Gabbro.Grammatik.except_ok_get boolText_parsed)
  rw [origin]
  rfl

/-- Certify whole alias/scope constructor results before their dependent meaning projections. -/
def boolTextTail : SourceTail boolTextInput := by
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

theorem boolText_metadata :
    Konst.checkSourceMetadata boolTextInput.original = .ok () := boolTextTail.metadata

theorem boolText_ordered :
    (Frontend.orderAliases boolTextInput.original).toOption.isSome = true := by
  rw [boolTextTail.ordered]
  rfl

theorem boolText_scopes :
    (Frontend.elaborateConstantScopes boolTextInput.original).toOption.isSome = true := by
  rw [boolTextTail.elaborated]
  rfl

/-- The canonical parser still supplies the public selected item list. -/
theorem optionText_parsed :
    (parseTopTief (optionTextScan.tokens ++ [.ende])).toOption.isSome = true := by cbv

def optionTextItems : List SItemTief :=
  (parseTopTief (optionTextScan.tokens ++ [.ende])).toOption.get optionText_parsed

/-- Infer both complete constructors from their real producer equations before checking any field. -/
def optionTextInput : SourceInput Gabbro.Stage0.Frontend.ConstValuesWitness.optionText := by
  refine {
    tokens := optionTextScan.tokens ++ [.ende]
    items := ?items
    lexed := optionText_lexed
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
theorem optionText_prepared :
    (Profil.prepareItems {} optionTextItems).toOption.isSome = true := by
  obtain ⟨prepared, origin, _, _⟩ :=
    SourceInput.prepared_selected optionTextInput optionText_lexed
      (items := optionTextItems) (by exact Gabbro.Grammatik.except_ok_get optionText_parsed)
  rw [origin]
  rfl

/-- Certify whole alias/scope constructor results before their dependent meaning projections. -/
def optionTextTail : SourceTail optionTextInput := by
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

theorem optionText_metadata :
    Konst.checkSourceMetadata optionTextInput.original = .ok () := optionTextTail.metadata

theorem optionText_ordered :
    (Frontend.orderAliases optionTextInput.original).toOption.isSome = true := by
  rw [optionTextTail.ordered]
  rfl

theorem optionText_scopes :
    (Frontend.elaborateConstantScopes optionTextInput.original).toOption.isSome = true := by
  rw [optionTextTail.elaborated]
  rfl

/-- The canonical parser still supplies the public selected item list. -/
theorem noneText_parsed :
    (parseTopTief (noneTextScan.tokens ++ [.ende])).toOption.isSome = true := by cbv

def noneTextItems : List SItemTief :=
  (parseTopTief (noneTextScan.tokens ++ [.ende])).toOption.get noneText_parsed

/-- Infer both complete constructors from their real producer equations before checking any field. -/
def noneTextInput : SourceInput Gabbro.Stage0.Frontend.ConstValuesWitness.noneText := by
  refine {
    tokens := noneTextScan.tokens ++ [.ende]
    items := ?items
    lexed := noneText_lexed
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
theorem noneText_prepared :
    (Profil.prepareItems {} noneTextItems).toOption.isSome = true := by
  obtain ⟨prepared, origin, _, _⟩ :=
    SourceInput.prepared_selected noneTextInput noneText_lexed
      (items := noneTextItems) (by exact Gabbro.Grammatik.except_ok_get noneText_parsed)
  rw [origin]
  rfl

/-- Certify whole alias/scope constructor results before their dependent meaning projections. -/
def noneTextTail : SourceTail noneTextInput := by
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

theorem noneText_metadata :
    Konst.checkSourceMetadata noneTextInput.original = .ok () := noneTextTail.metadata

theorem noneText_ordered :
    (Frontend.orderAliases noneTextInput.original).toOption.isSome = true := by
  rw [noneTextTail.ordered]
  rfl

theorem noneText_scopes :
    (Frontend.elaborateConstantScopes noneTextInput.original).toOption.isSome = true := by
  rw [noneTextTail.elaborated]
  rfl

end Gabbro.Stage0.Frontend.ConstPhases
