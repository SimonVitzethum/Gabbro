module
public import Stage0.Frontend.Witnesses.Constants.SourcePackets
public import Stage0.Frontend.Witnesses.Constants.Lexical
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

/-- The exact parser output is extracted only after canonical success has been proved. -/
theorem boolText_parsed :
    (parseTopTief (boolTextScan.tokens ++ [.ende])).toOption.isSome = true := by cbv

def boolTextItems : List SItemTief :=
  (parseTopTief (boolTextScan.tokens ++ [.ende])).toOption.get boolText_parsed

theorem boolText_prepared :
    (Profil.prepareItems {} boolTextItems).toOption.isSome = true := by cbv

/-- Profile preparation, visibility, and the original call-hull guard remain actual checks. -/
def boolTextInput : SourceInput Gabbro.Stage0.Frontend.ConstValuesWitness.boolText where
  tokens := boolTextScan.tokens ++ [.ende]
  items := boolTextItems
  lexed := boolText_lexed
  parsed := by exact Gabbro.Grammatik.except_ok_get boolText_parsed
  prepared := (Profil.prepareItems {} boolTextItems).toOption.get boolText_prepared
  preparation := by exact Gabbro.Grammatik.except_ok_get boolText_prepared
  visibility := by cbv
  compileTime := by cbv

theorem boolText_metadata :
    Konst.checkSourceMetadata boolTextInput.original = .ok () := by cbv

theorem boolText_ordered :
    (Frontend.orderAliases boolTextInput.original).toOption.isSome = true := by cbv

theorem boolText_scopes :
    (Frontend.elaborateConstantScopes boolTextInput.original).toOption.isSome = true := by cbv

/-- Bind the complete alias/scope results before asking either final meaning checker. -/
def boolTextTail : SourceTail boolTextInput where
  metadata := boolText_metadata
  order := (Frontend.orderAliases boolTextInput.original).toOption.get boolText_ordered
  ordered := by exact Gabbro.Grammatik.except_ok_get boolText_ordered
  derived := (Frontend.elaborateConstantScopes boolTextInput.original).toOption.get boolText_scopes
  elaborated := by exact Gabbro.Grammatik.except_ok_get boolText_scopes
  aliases := by cbv
  constants := by cbv

/-- The exact parser output is extracted only after canonical success has been proved. -/
theorem optionText_parsed :
    (parseTopTief (optionTextScan.tokens ++ [.ende])).toOption.isSome = true := by cbv

def optionTextItems : List SItemTief :=
  (parseTopTief (optionTextScan.tokens ++ [.ende])).toOption.get optionText_parsed

theorem optionText_prepared :
    (Profil.prepareItems {} optionTextItems).toOption.isSome = true := by cbv

/-- Profile preparation, visibility, and the original call-hull guard remain actual checks. -/
def optionTextInput : SourceInput Gabbro.Stage0.Frontend.ConstValuesWitness.optionText where
  tokens := optionTextScan.tokens ++ [.ende]
  items := optionTextItems
  lexed := optionText_lexed
  parsed := by exact Gabbro.Grammatik.except_ok_get optionText_parsed
  prepared := (Profil.prepareItems {} optionTextItems).toOption.get optionText_prepared
  preparation := by exact Gabbro.Grammatik.except_ok_get optionText_prepared
  visibility := by cbv
  compileTime := by cbv

theorem optionText_metadata :
    Konst.checkSourceMetadata optionTextInput.original = .ok () := by cbv

theorem optionText_ordered :
    (Frontend.orderAliases optionTextInput.original).toOption.isSome = true := by cbv

theorem optionText_scopes :
    (Frontend.elaborateConstantScopes optionTextInput.original).toOption.isSome = true := by cbv

/-- Bind the complete alias/scope results before asking either final meaning checker. -/
def optionTextTail : SourceTail optionTextInput where
  metadata := optionText_metadata
  order := (Frontend.orderAliases optionTextInput.original).toOption.get optionText_ordered
  ordered := by exact Gabbro.Grammatik.except_ok_get optionText_ordered
  derived := (Frontend.elaborateConstantScopes optionTextInput.original).toOption.get optionText_scopes
  elaborated := by exact Gabbro.Grammatik.except_ok_get optionText_scopes
  aliases := by cbv
  constants := by cbv

/-- The exact parser output is extracted only after canonical success has been proved. -/
theorem noneText_parsed :
    (parseTopTief (noneTextScan.tokens ++ [.ende])).toOption.isSome = true := by cbv

def noneTextItems : List SItemTief :=
  (parseTopTief (noneTextScan.tokens ++ [.ende])).toOption.get noneText_parsed

theorem noneText_prepared :
    (Profil.prepareItems {} noneTextItems).toOption.isSome = true := by cbv

/-- Profile preparation, visibility, and the original call-hull guard remain actual checks. -/
def noneTextInput : SourceInput Gabbro.Stage0.Frontend.ConstValuesWitness.noneText where
  tokens := noneTextScan.tokens ++ [.ende]
  items := noneTextItems
  lexed := noneText_lexed
  parsed := by exact Gabbro.Grammatik.except_ok_get noneText_parsed
  prepared := (Profil.prepareItems {} noneTextItems).toOption.get noneText_prepared
  preparation := by exact Gabbro.Grammatik.except_ok_get noneText_prepared
  visibility := by cbv
  compileTime := by cbv

theorem noneText_metadata :
    Konst.checkSourceMetadata noneTextInput.original = .ok () := by cbv

theorem noneText_ordered :
    (Frontend.orderAliases noneTextInput.original).toOption.isSome = true := by cbv

theorem noneText_scopes :
    (Frontend.elaborateConstantScopes noneTextInput.original).toOption.isSome = true := by cbv

/-- Bind the complete alias/scope results before asking either final meaning checker. -/
def noneTextTail : SourceTail noneTextInput where
  metadata := noneText_metadata
  order := (Frontend.orderAliases noneTextInput.original).toOption.get noneText_ordered
  ordered := by exact Gabbro.Grammatik.except_ok_get noneText_ordered
  derived := (Frontend.elaborateConstantScopes noneTextInput.original).toOption.get noneText_scopes
  elaborated := by exact Gabbro.Grammatik.except_ok_get noneText_scopes
  aliases := by cbv
  constants := by cbv

end Gabbro.Stage0.Frontend.ConstPhases
