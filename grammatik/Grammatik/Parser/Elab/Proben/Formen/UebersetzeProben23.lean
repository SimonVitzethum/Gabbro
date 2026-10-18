/-
  File:      Grammatik/Parser/Elab/Proben/UebersetzeProben23.lean
  Subject:   Track P: `alloc` and `start`. `let i = alloc A (v) else { .. };` is the sugar `Block.arenaAlloc`
             (`ArenaZucker`: a `narrow` of the counter, the store, the bump), in a nested block only (`Endblock`
             lacks the former, recorded as a model gap); the rest reads `i` as an index into the arena.
             `start { f, g };` leaves no G term: its roots travel as `UProg.gestartet` (`Einheit.gestartet`),
             judged by the checker Bool as pool routines; a start under a held lock has no representation.
-/
import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben23

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- An allocation with its full-arena branch, and a read of the element. -/
def alloc_ok : String :=
  "module m { arena R capacity 2 .. 8 of u16; impl fn f(c : bool) -> u16 effects { reads R, writes R } { if c { let a = alloc R (1) else { return 100; }; return R[a]; } return 0; } }"
theorem alloc_ok_stufe : stufe alloc_ok = "OK" := by decide +kernel

/-- The branch is required. -/
def alloc_else_refused : String :=
  "module m { arena R capacity 2 .. 8 of u16; impl fn f(c : bool) effects { writes R } { if c { let a = alloc R (1); } } }"
theorem alloc_else_refused_stufe : stufe alloc_else_refused = "elab: alloc without else without G form" := by decide +kernel

/-- The write right on the arena. -/
def alloc_right_refused : String :=
  "module m { arena R capacity 2 .. 8 of u16; impl fn f(c : bool) { if c { let a = alloc R (1) else { return; }; } } }"
theorem alloc_right_refused_stufe : stufe alloc_right_refused = "lower: write without right" := by decide +kernel

/-- A start of two routines. -/
def start_ok : String :=
  "module m { impl fn w() { } impl fn z() { } impl fn f() { start { w, z }; } }"
theorem start_ok_stufe : stufe start_ok = "OK" := by decide +kernel

/-- A routine with parameters has no start-argument form. -/
def start_params_refused : String :=
  "module m { impl fn p(a : u32 in 0 .. 1) { } impl fn f() { start { p }; } }"
theorem start_params_refused_stufe : stufe start_params_refused = "elab: start names a function with parameters: no start-argument form: p" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben23
