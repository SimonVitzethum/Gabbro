module
public import Stage0.Frontend.Witnesses.Constants.Lexical
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

@[expose] public section
namespace Gabbro.Stage0.Frontend.ConstPhases
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The original unsupported const body fails the actual frontend, before any G compilation. -/
theorem blockText_refused :
    ∃ error : String, Frontend.source Gabbro.Stage0.Frontend.ConstValuesWitness.blockText = .error error := by
  have parsed : (parseTopTief (blockTextScan.tokens ++ [.ende])).toOption.isSome = true := by cbv
  have parsedEq := Gabbro.Grammatik.except_ok_get (ε := String)
    (α := List SItemTief) (x := parseTopTief (blockTextScan.tokens ++ [.ende])) parsed
  refine ⟨?error, ?equation⟩
  case equation =>
    unfold Frontend.source
    split
    · rename_i error rejected
      cases rejected.symm.trans blockText_lexed
    · rename_i tokens selected
      have same : tokens = blockTextScan.tokens ++ [.ende] :=
        Except.ok.inj (selected.symm.trans blockText_lexed)
      subst tokens
      split
      · rename_i error rejected
        cases rejected.symm.trans parsedEq
      · rename_i items selected
        have same : items =
            (parseTopTief (blockTextScan.tokens ++ [.ende])).toOption.get parsed :=
          Except.ok.inj (selected.symm.trans parsedEq)
        subst items
        cbv <;> exact Eq.refl _

theorem blockText_compile_refused :
    (compile Gabbro.Stage0.Frontend.ConstValuesWitness.blockText).toOption.isSome = false := by
  obtain ⟨error, refused⟩ := blockText_refused
  simp only [compile, refused, bind, Except.bind, Except.toOption, Option.isSome]

end Gabbro.Stage0.Frontend.ConstPhases
