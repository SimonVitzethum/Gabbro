module

public import Grammatik.Parser.SourceFolds.Hoist
import all Init.Data.Int.Repr
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
namespace Gabbro.Grammatik.Parser.SourceFolds

/-- A `let` binding a range fold hoists the loop before the binding. The
    accumulator uses the nested derivation, since the hoist carries no
    ascription; the ordinary elaborator checks the annotation afterwards. -/
theorem hoistAnw_let_zeuge :
    hoistAnw [] [("xs", .array (.atom "u8") (.lit 2))] none
      (.bind false "t" none
        (.ext .foldAdd ["i", "range"]
          [.lit 0, .lit 2, .tru, .index (.variable "xs") (.variable "i")])) =
    .ok (.block
      [.bind true "$rangeFold$acc$0" (some (.atom "u64")) (.lit 0),
       .each "i" none "elems" (.variable "xs") "unvisited" "" none
         (.block
           [.bind false "$rangeFold$value$0" none
              (.index (.variable "xs") (.variable "i")),
            .set (.variable "$rangeFold$acc$0") "+=" (.variable "$rangeFold$value$0")] none),
       .bind false "$rangeFold$result$0" none (.variable "$rangeFold$acc$0"),
       .bind false "t" none (.variable "$rangeFold$result$0")] none) := by with_unfolding_all rfl

end Gabbro.Grammatik.Parser.SourceFolds
