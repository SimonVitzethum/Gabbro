module
public import Grammatik.Parser.Elab.Konst.Scopes.AliasOrder
public import Stage0.Frontend.Aliases
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
@[expose] public section


namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- A nondegenerate forward chain has a complete original-declaration permutation and no cycle. -/
theorem orderAliases_zeuge :
    let items := [SItemTief.typeT [] "Result" [] [] (some (.atom "Count")),
      .typeT [] "Count" [] [] (some (.atom "Byte")),
      .typeT [] "Byte" [] [] (some (.atom "u8"))]
    ∃ order : AliasOrder items, orderAliases items = .ok order ∧
      order.ordered.filterMap (fun | .typeT _ name _ _ _ => some name | _ => none) =
        ["Byte", "Count", "Result"] ∧ AliasAcyclic items := by
  dsimp only
  refine ⟨(orderAliases _).toOption.get (by decide +kernel), ?_, ?_, ?_⟩
  · exact Gabbro.Grammatik.except_ok_get _
  · decide +kernel
  · exact orderAliases_acyclic _ ((orderAliases _).toOption.get (by decide +kernel))

/-- Cycles are refused before even unused aliases can disappear from canonical collection. -/
theorem orderAliases_cycle_zeuge :
    orderAliases [SItemTief.typeT [] "A" [] [] (some (.atom "B")),
      .typeT [] "B" [] [] (some (.atom "A"))] =
      .error "compile-time alias dependency cycle at A" := by rfl

/-- The generic no-cycle theorem is inhabited by a nonempty, two-edge alias chain. -/
theorem AliasAcyclic.no_cycle_zeuge :
    ¬ Relation.TransGen (fun a b => (a, b) ∈ aliasEdges
      [SItemTief.typeT [] "A" [] [] (some (.atom "B")),
       .typeT [] "B" [] [] (some (.atom "u8"))]) "A" "A" :=
  (orderAliases_acyclic _ ((orderAliases _).toOption.get (by decide +kernel))).no_cycle "A"

end Gabbro.Stage0.Frontend
