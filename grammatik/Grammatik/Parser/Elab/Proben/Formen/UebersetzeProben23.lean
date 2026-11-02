/-
  File:      Grammatik/Parser/Elab/Proben/UebersetzeProben23.lean
  Subject:   Track P: `alloc` and `start`. `let i = alloc A (v) else { .. };` is the sugar `Block.arenaAlloc`
             (`ArenaZucker`: a `narrow` of the counter, the store, the bump), in a nested block only (`Endblock`
             lacks the former, recorded as a model gap); the rest reads `i` as an index into the arena.
             `start { f, g };` leaves no G term: its roots travel as `UProg.gestartet` (`Einheit.gestartet`),
             judged by the checker Bool as pool routines; a start under a held lock has no representation.
-/
module
public import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3
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


namespace Gabbro.Grammatik.Parser.UebersetzeProben23

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- An allocation with its full-arena branch, and a read of the element. -/
def alloc_ok : String :=
  "module m { arena R capacity 2 .. 8 of u16; impl fn f(c : bool) -> u16 effects { reads R, writes R } { if c { let a = alloc R (1) else { return 100; }; return R[a]; } return 0; } }"
theorem alloc_ok_stufe : stufe alloc_ok = "OK" := by decide +kernel

/-- No `else` needed: the required allocation runs the shared body, and a full
    arena is the caller's capacity duty (`Logik.kapazitaet`, excluded by
    `KoerperGutS/SA`). -/
def allocRequired_ok : String :=
  "module m { arena R capacity 2 .. 8 of u16; impl fn f(c : bool) -> u16 effects { reads R, writes R } { if c { let a = alloc R (1); return R[a]; } return 0; } }"
theorem allocRequired_ok_stufe : stufe allocRequired_ok = "OK" := by decide +kernel

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
