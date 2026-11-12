/-
  Witness of the hold-bound binding on a lowered unit with one lock and one section
  (`locks L { let x = n; k.v[i] = x; }`): a bound of 100 holds, a bound of 1 is refused, and a bound
  for a lock the unit does not have is refused.
-/
module
public import Grammatik.Parser.Elab.Export.HeldBinding
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

namespace Gabbro.Grammatik.Parser.HeldBinding
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- One table, one lock, one function whose body is one section of the lock. -/
def sectionUnit : UProg :=
  { tabs := [{ name := "T", count := 2, cols := [("v", 0, 4294967295)] }],
    locks := [{ name := "L", rank := 0, guard := ["T"] }],
    fns := [{ name := "w",
              params := [("k", .ptr (.table 0 (true, true))), ("i", .index 2), ("n", .int 0 255)],
              kinds := [.ptr (.table 0 (true, true)), .index 0, .int], res := none, held := [],
              puts := ["T"], gives := [],
              body := [.lockBeg "L", .bind "x" (some (0, 4294967295)) (.param "n"),
                .assign "k" "v" (.param "i") (.param "x"), .blkEnd],
              ret := .empty }],
    roots := [] }

set_option maxRecDepth 100000 in
/-- **The check is not degenerate.** -/
theorem holds_zeuge :
    ((lowerAllg sectionUnit).toOption.map fun r =>
      (holds (Tafel.von _ [("L", 100)]) (Tafel.von _ []) sectionUnit r.1 0,
       holds (Tafel.von _ [("L", 1)]) (Tafel.von _ []) sectionUnit r.1 0,
       holds (Tafel.von _ [("M", 100)]) (Tafel.von _ []) sectionUnit r.1 0)) =
      some (true, false, false) := by
  decide +kernel

end Gabbro.Grammatik.Parser.HeldBinding
