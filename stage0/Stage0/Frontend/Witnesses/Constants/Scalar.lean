module
public import Stage0.Frontend.Witnesses.Constants.Input
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
open Gabbro.Grammatik.Parser.Konst
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The whole typed call is constructed before its result or KExpr denotation is projected. -/
theorem increment_three :
    ∃ call : Scalar.CheckedCall ConstWitness.function [ConstWitness.function] [] [.lit 3],
      Scalar.checkCall ConstWitness.function [ConstWitness.function] [] [.lit 3] = .ok call ∧
      call.value = 4 := by
  refine ⟨?call, ?checked, ?value⟩
  case checked => cbv <;> exact Eq.refl _
  case value => rfl

theorem increment_five :
    ∃ call : Scalar.CheckedCall ConstWitness.function [ConstWitness.function] [] [.lit 5],
      Scalar.checkCall ConstWitness.function [ConstWitness.function] [] [.lit 5] = .ok call ∧
      call.value = 6 := by
  refine ⟨?call, ?checked, ?value⟩
  case checked => cbv <;> exact Eq.refl _
  case value => rfl

private theorem integer_projection {k : UKonstFn} {fns : List UKonstFn}
    {env : List (String × Int)} {sources : List SExpr}
    (answer : Except String (Scalar.CheckedCall k fns env sources)) :
    (do
      let replacement ← (do
        let checked ← answer
        pure (⟨literalVonInt checked.value, .integer checked⟩ : Replacement k fns env sources))
      pure replacement.syntax) = answer.map (fun checked => literalVonInt checked.value) := by
  cases answer <;> rfl

/-- Replay the ordinary substitution prefix against the already certified complete scalar answer. -/
theorem substitute_integer (fns : List UKonstFn) (name : String)
    (sources args : List SExpr) (k : UKonstFn) (lo hi : Int)
    (arguments : ersetzeSExprListIn [] fns sources = .ok args)
    (callee : fns.find? (fun fn => strEq fn.name name) = some k)
    (constants : k.constants = [])
    (closed : geschlossenSExprListB
      (args.map (Scalar.normalizeNames ([] : Scalar.Locals []) [])) = true)
    (integer : k.erg = .int lo hi) :
    ersetzeSExpr fns (.call name sources) =
      (Scalar.checkCall k fns [] args).map (fun checked => literalVonInt checked.value) := by
  rcases k with ⟨fnName, params, result, statement, signature, globals, schemas⟩
  dsimp only at constants integer
  cases constants
  cases integer
  simp only [ersetzeSExpr, ersetzeSExprIn, arguments, callee,
    List.filter_nil, closed, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp only [checkReplacement]
  exact integer_projection _

theorem increment_three_value :
    ersetzeSExpr [ConstWitness.function] (.call "increment" [.lit 3]) = .ok (.lit 4) := by
  obtain ⟨call, checked, value⟩ := increment_three
  rw [substitute_integer [ConstWitness.function] "increment" [.lit 3] [.lit 3]
    ConstWitness.function 0 11 (by cbv) (by cbv) rfl (by cbv) rfl, checked]
  simp only [Except.map, value]
  rfl

theorem increment_five_value :
    ersetzeSExpr [ConstWitness.function] (.call "increment" [.lit 5]) = .ok (.lit 6) := by
  obtain ⟨call, checked, value⟩ := increment_five
  rw [substitute_integer [ConstWitness.function] "increment" [.lit 5] [.lit 5]
    ConstWitness.function 0 11 (by cbv) (by cbv) rfl (by cbv) rfl, checked]
  simp only [Except.map, value]
  rfl

end Gabbro.Stage0.Frontend.ConstPhases
