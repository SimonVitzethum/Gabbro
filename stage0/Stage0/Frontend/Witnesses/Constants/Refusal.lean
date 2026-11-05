module
public import Stage0.Frontend.Witnesses.Constants.Lexical
public import Stage0.Frontend.Witnesses.Constants.SourcePackets
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
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

-- This integer/Boolean fixture never uses the elaborator's float target.
attribute [local cbv_opaque] uFloatLimit Frontend.normalize

theorem blockText_parsed :
    (parseTopTief (blockTextScan.tokens ++ [.ende])).toOption.isSome = true := by cbv

def blockTextItems : List SItemTief :=
  (parseTopTief (blockTextScan.tokens ++ [.ende])).toOption.get blockText_parsed

/-- Bind the actual parser/profile constructors before either source guard is inspected. -/
def blockTextInput : SourceInput Gabbro.Stage0.Frontend.ConstValuesWitness.blockText := by
  refine {
    tokens := blockTextScan.tokens ++ [.ende]
    items := ?items
    lexed := blockText_lexed
    parsed := ?parsed
    prepared := ?prepared
    preparation := ?preparation
    visibility := ?visibility
    compileTime := ?compileTime }
  case parsed => cbv <;> exact Eq.refl _
  case preparation => cbv <;> exact Eq.refl _
  case visibility => cbv
  case compileTime => cbv

theorem blockText_prepared :
    (Profil.prepareItems {} blockTextItems).toOption.isSome = true := by
  obtain ⟨prepared, origin, _, _⟩ :=
    SourceInput.prepared_selected blockTextInput blockText_lexed
      (items := blockTextItems) (by exact Gabbro.Grammatik.except_ok_get blockText_parsed)
  rw [origin]
  rfl

/-- Classify the actual failed metadata phase, not a guessed diagnostic or source result. -/
theorem blockText_metadata_refused :
    ∃ error : String, Konst.checkSourceMetadata blockTextInput.original = .error error := by
  refine ⟨?error, ?equation⟩
  case equation => cbv <;> exact Eq.refl _

/-- The original unsupported const body fails the actual frontend, before any G compilation. -/
theorem blockText_refused :
    ∃ error : String, Frontend.source Gabbro.Stage0.Frontend.ConstValuesWitness.blockText = .error error := by
  obtain ⟨error, refused⟩ := blockText_metadata_refused
  exact ⟨error, source_metadata_refused blockTextInput error refused⟩

theorem blockText_compile_refused :
    (compile Gabbro.Stage0.Frontend.ConstValuesWitness.blockText).toOption.isSome = false := by
  obtain ⟨error, refused⟩ := blockText_refused
  simp only [compile, refused, bind, Except.bind, Except.toOption, Option.isSome]

end Gabbro.Stage0.Frontend.ConstPhases
