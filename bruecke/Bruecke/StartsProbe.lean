import Bruecke.Quelle
import Grammatik.Parser.UebersetzeProben2

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
