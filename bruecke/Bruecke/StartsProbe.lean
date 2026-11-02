module
public import Bruecke.Quelle
public import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben2
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


/-! Wall 7 witness on the bridge side: an `entry` really becomes a declared start of `einheitAllg`
(the statement of `nutzer_aus_quelle` is then about a unit WITH a thread root, not about the empty
start list), and a unit without an entry keeps none. -/

namespace Gabbro.Bruecke

open Gabbro.Grammatik.Parser.UebersetzeProben2

theorem entry_ist_start :
    (uOf entry1_ok).map (fun u => (startsAllg u).length) = some 1 := by decide +kernel

theorem zwei_entries_zwei_starts :
    (uOf entry_two_ok).map (fun u => (startsAllg u).length) = some 2 := by decide +kernel

theorem ohne_entry_kein_start :
    (uOf locks1_ok).map (fun u => (startsAllg u).length) = some 0 := by decide +kernel

#print axioms entry_ist_start

end Gabbro.Bruecke
