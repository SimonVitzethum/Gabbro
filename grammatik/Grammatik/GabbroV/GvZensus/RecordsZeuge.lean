module
public import Grammatik.GabbroV.GvZensus.Teil1
import Grammatik.Kern.Taktik.KernelRfl
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

namespace Gabbro.Grammatik.GabbroV.GvZensus
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

/-- A record declaration and a real slot field using it, as in the Stage-0 record probe. -/
def recordSlotItems : List SItemTief :=
  [.typeT [] "R" [] [] (some (.raw "{ v : u32 in 0 .. 9, }")),
   .tableT "T" none (some (.lit 4)) none none false
     [.tSlot [{ fname := "record", ftyp := .atom "R",
                pos := none, bezug := none, wo := none,
                reserviert := false, byOps := false }]]]

/-- The census retains a record-typed table instead of reporting an unknown tagged type. -/
theorem record_slot_census_zeuge : befundeElab recordSlotItems = [] := by kernel_rfl

end Gabbro.Grammatik.GabbroV.GvZensus
