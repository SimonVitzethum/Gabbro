/-
  File:      Grammatik/Parser/Elab/UebersetzeProben17.lean
  Subject:   Track P: calls. `&T` as a pointer argument (`Expr.ptrOf`), an integer parameter as a table index
             (`Expr.widen` into `index`), the value of a call bound by `let y = f(..)` (`Block.bindCall`, in a
             nested block only: `Endblock` has no such former, recorded as a model gap) and the lock floors
             (`Signatur.boden`): a lock held across a call must rank below the callee's floor (`RufPasst.hx`).
-/
import Grammatik.Parser.Elab.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben17

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- `&T` passed for a `ptr<normal, rw> T` parameter. -/
def addr_ok : String :=
  "module m { table T count 2 { slot { v : u32 in 0 .. 9, } } impl fn wp(p : ptr<normal, rw> T, i : index into T) effects { writes p.slots } { p.slots[i].v = 1; } impl fn f() effects { writes T.slots } { wp(&T, 0); } }"
theorem addr_ok_stufe : stufe addr_ok = "OK" := by decide +kernel

/-- An integer parameter whose range lies inside the table indexes it. -/
def intindex_ok : String :=
  "module m { table T count 4 { slot { v : u32 in 0 .. 9, } } impl fn f(a : u32 in 0 .. 3) effects { writes T.slots } { T.slots[a].v = 1; } }"
theorem intindex_ok_stufe : stufe intindex_ok = "OK" := by decide +kernel

/-- ... and one whose range reaches beyond it does not. -/
def intindex_refused : String :=
  "module m { table T count 4 { slot { v : u32 in 0 .. 9, } } impl fn f(a : u32 in 0 .. 4) effects { writes T.slots } { T.slots[a].v = 1; } }"
theorem intindex_refused_stufe : stufe intindex_refused = "lower: index outside count" := by decide +kernel

/-- The value of a call, bound in a nested block. -/
def bindcall_ok : String :=
  "module m { impl fn h(a : u32 in 0 .. 9) -> u32 in 0 .. 9 { return a; } impl fn f(c : bool) -> u32 in 0 .. 9 { if c { let y = h(4); return y; } return 0; } }"
theorem bindcall_ok_stufe : stufe bindcall_ok = "OK" := by decide +kernel

/-- At the top level of a body the model has no former (`Endblock.bindCall`): recorded, not worked around. -/
def bindcall_top_refused : String :=
  "module m { impl fn h(a : u32 in 0 .. 9) -> u32 in 0 .. 9 { return a; } impl fn f() -> u32 in 0 .. 9 { let y = h(4); return y; } }"
theorem bindcall_top_refused_stufe : stufe bindcall_top_refused = "lower: lower: a value call at the top level of a body has no G form (Endblock lacks bindCall)" := by
  decide +kernel

/-- A callee whose result range does not fit the annotation. -/
def bindcall_range_refused : String :=
  "module m { impl fn h(a : u32 in 0 .. 9) -> u32 in 0 .. 9 { return a; } impl fn f(c : bool) -> u32 in 0 .. 9 { if c { let y : u32 in 0 .. 5 = h(4); return 1; } return 0; } }"
theorem bindcall_range_refused_stufe : stufe bindcall_range_refused = "elab: let: value outside the annotated range" := by
  decide +kernel

/-- A lock held across a call that takes a HIGHER lock: the floor of the callee is above it. -/
def floor_ok : String :=
  "module m { lock L protects { } rank 0; lock M protects { } rank 1; impl fn g() effects { locks M } { locks M { } } impl fn w() effects { locks L, locks M } { locks L { g(); } } }"
theorem floor_ok_stufe : stufe floor_ok = "OK" := by decide +kernel

/-- A lock held across a call that takes a LOWER lock: the callee's floor is below it. -/
def floor_refused : String :=
  "module m { lock L protects { } rank 0; lock M protects { } rank 1; impl fn g() effects { locks L } { locks L { } } impl fn w() effects { locks L, locks M } { locks M { g(); } } }"
theorem floor_refused_stufe : stufe floor_refused = "lower: call: a held lock does not rank below the callee's floor" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben17
