/-
  Witness of the cost binding on a lowered unit (`uReset`: one function, a reset of a static array):
  a sufficient declared cost holds, a declared cost of zero does not, and the function is a member.
-/
module
public import Grammatik.Parser.Elab.Export.CostBinding
public import Grammatik.Parser.Elab.UebersetzeAllg3.Rest2
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

namespace Gabbro.Grammatik.Parser.CostBinding
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000 in
/-- **The check is not degenerate**: on the lowered `uReset` a declared cost of 100 holds for its
    function, a declared cost of 0 is refused, and a declaration naming no function of the unit is
    refused as well. -/
theorem holds_zeuge :
    ((lowerAllg uReset).toOption.map fun r =>
      (holds (Tafel.von _ [("leere", 100)]) uReset r.1 0,
       holds (Tafel.von _ [("leere", 0)]) uReset r.1 0,
       holds (Tafel.von _ [("fremd", 100)]) uReset r.1 0,
       (members (Tafel.von _ [("leere", 100)]) uReset).length)) = some (true, false, false, 1) := by
  decide +kernel

/-- **Constant cost expressions have their value**: a literal, a constant, a constant defined by an
    earlier one, a sum of products; a name that is no constant and a difference below zero have none. -/
theorem costValue_zeuge :
    let consts := constants [.constT "N" (.atom "u32") (.one (.lit 20)),
      .constT "M" (.atom "u32") (.one (.bin "*" (.variable "N") (.lit 2)))]
    (consts, costValue consts (.bin "+" (.variable "M") (.lit 4)), costValue consts (.variable "n"),
      costValue consts (.bin "-" (.lit 1) (.variable "N"))) =
      ([("N", 20), ("M", 40)], some 44, none, none) := by
  decide +kernel

end Gabbro.Grammatik.Parser.CostBinding
