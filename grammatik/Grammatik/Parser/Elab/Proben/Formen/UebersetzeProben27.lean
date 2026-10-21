/-
  File:      Grammatik/Parser/Elab/Proben/Formen/UebersetzeProben27.lean
  Subject:   Track P: the lock floor is DATA of the elaborated function (`UFn.boden`), filled after
             elaboration by `uMitBoden` with the rule `floorOf`, and read by the declaration (`mkSig`).
             A call bound by `let y = g(..) else (e) { .. }` is a call edge of the floor relation: before,
             it was not, and a lock held across a function that reaches a LOWER lock only through such a
             call was admitted.
-/
import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben27

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- The floors of the elaborated functions, in order (`none` for a source that does not elaborate). -/
def boeden (s : String) : Option (List (Option Int)) :=
  match lex s with
  | .error _ => none
  | .ok toks =>
    match parseTopTief toks with
    | .error _ => none
    | .ok items =>
      match elabU (pre108 items) with
      | .error _ => none
      | .ok u => some (u.fns.map (·.boden))

/-- `w` holds `L` (rank 0) across `h`, which reaches `M` (rank 1) only through `let .. else`: admitted. -/
def floor_else_ok : String :=
  "module m { reason R { A = 1 \"a\" exhaustive } lock L protects { } rank 0; lock M protects { } rank 1; impl fn g() -> u32 or R effects { locks M } { locks M { } return 1; } impl fn h() -> u32 { let y = g() else (e) { return 0; } return y; } impl fn w() effects { locks L } { locks L { let z = h(); } } }"
theorem floor_else_ok_stufe : stufe floor_else_ok = "OK" := by decide +kernel

/-- The floors as data: `g` and `h` take nothing below `M`, `w` takes `L`. -/
theorem floor_else_ok_boeden : boeden floor_else_ok = some [some 1, some 1, some 0] := by decide +kernel

/-- Planted defect: `w` holds `M` (rank 1) across `h`, which reaches `L` (rank 0) only through
    `let .. else`. Refused: the floor of `h` is 0. (Before the bound call counted, `h` had the floor 2 and
    the call was admitted.) -/
def floor_else_refused : String :=
  "module m { reason R { A = 1 \"a\" exhaustive } lock L protects { } rank 0; lock M protects { } rank 1; impl fn g() -> u32 or R effects { locks L } { locks L { } return 1; } impl fn h() -> u32 { let y = g() else (e) { return 0; } return y; } impl fn w() effects { locks M } { locks M { let z = h(); } } }"
theorem floor_else_refused_stufe :
    stufe floor_else_refused = "lower: call: a held lock does not rank below the callee's floor" := by
  decide +kernel

theorem floor_else_refused_boeden : boeden floor_else_refused = some [some 0, some 0, some 0] := by
  decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben27
