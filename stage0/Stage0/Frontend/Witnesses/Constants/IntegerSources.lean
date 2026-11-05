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
theorem increment_parsed :
    (parseTopTief (incrementScan.tokens ++ [.ende])).toOption.isSome = true := by cbv

def incrementItems : List SItemTief :=
  (parseTopTief (incrementScan.tokens ++ [.ende])).toOption.get increment_parsed

theorem increment_prepared :
    (Profil.prepareItems {} incrementItems).toOption.isSome = true := by cbv

/-- Profile preparation, visibility, and the original call-hull guard remain actual checks. -/
def incrementInput : SourceInput Gabbro.Stage0.Frontend.ConstWitness.text where
  tokens := incrementScan.tokens ++ [.ende]
  items := incrementItems
  lexed := increment_lexed
  parsed := by exact Gabbro.Grammatik.except_ok_get increment_parsed
  prepared := (Profil.prepareItems {} incrementItems).toOption.get increment_prepared
  preparation := by exact Gabbro.Grammatik.except_ok_get increment_prepared
  visibility := by cbv
  compileTime := by cbv

theorem increment_metadata :
    Konst.checkSourceMetadata incrementInput.original = .ok () := by cbv

theorem increment_ordered :
    (Frontend.orderAliases incrementInput.original).toOption.isSome = true := by cbv

theorem increment_scopes :
    (Frontend.elaborateConstantScopes incrementInput.original).toOption.isSome = true := by cbv

/-- Bind the complete alias/scope results before asking either final meaning checker. -/
def incrementTail : SourceTail incrementInput where
  metadata := increment_metadata
  order := (Frontend.orderAliases incrementInput.original).toOption.get increment_ordered
  ordered := by exact Gabbro.Grammatik.except_ok_get increment_ordered
  derived := (Frontend.elaborateConstantScopes incrementInput.original).toOption.get increment_scopes
  elaborated := by exact Gabbro.Grammatik.except_ok_get increment_scopes
  aliases := by cbv
  constants := by cbv

/-- The exact parser output is extracted only after canonical success has been proved. -/
theorem initializer_parsed :
    (parseTopTief (initializerScan.tokens ++ [.ende])).toOption.isSome = true := by cbv

def initializerItems : List SItemTief :=
  (parseTopTief (initializerScan.tokens ++ [.ende])).toOption.get initializer_parsed

theorem initializer_prepared :
    (Profil.prepareItems {} initializerItems).toOption.isSome = true := by cbv

/-- Profile preparation, visibility, and the original call-hull guard remain actual checks. -/
def initializerInput : SourceInput Gabbro.Stage0.Frontend.ConstWitness.initializerText where
  tokens := initializerScan.tokens ++ [.ende]
  items := initializerItems
  lexed := initializer_lexed
  parsed := by exact Gabbro.Grammatik.except_ok_get initializer_parsed
  prepared := (Profil.prepareItems {} initializerItems).toOption.get initializer_prepared
  preparation := by exact Gabbro.Grammatik.except_ok_get initializer_prepared
  visibility := by cbv
  compileTime := by cbv

theorem initializer_metadata :
    Konst.checkSourceMetadata initializerInput.original = .ok () := by cbv

theorem initializer_ordered :
    (Frontend.orderAliases initializerInput.original).toOption.isSome = true := by cbv

theorem initializer_scopes :
    (Frontend.elaborateConstantScopes initializerInput.original).toOption.isSome = true := by cbv

/-- Bind the complete alias/scope results before asking either final meaning checker. -/
def initializerTail : SourceTail initializerInput where
  metadata := initializer_metadata
  order := (Frontend.orderAliases initializerInput.original).toOption.get initializer_ordered
  ordered := by exact Gabbro.Grammatik.except_ok_get initializer_ordered
  derived := (Frontend.elaborateConstantScopes initializerInput.original).toOption.get initializer_scopes
  elaborated := by exact Gabbro.Grammatik.except_ok_get initializer_scopes
  aliases := by cbv
  constants := by cbv

end Gabbro.Stage0.Frontend.ConstPhases
