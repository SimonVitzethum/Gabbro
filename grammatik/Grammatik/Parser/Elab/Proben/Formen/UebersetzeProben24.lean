/-
  File:      Grammatik/Parser/Elab/Proben/UebersetzeProben24.lean
  Subject:   Track P: the failure channel. `reason R { C = 1 "text" exhaustive }` is `Ty.why n` (`n` the number of
             cases); a function `-> T or R` has `Signatur.gruende = n` and ends a failing path with `return R::C;`
             (`Stmt.retWhy`/`Endblock.retWhy`); a caller binds the value or handles the reason with
             `let y = f(..) else (e) { .. }` (`Block.bindCallElse`/`Endblock.bindCallElse`, including
             nested error continuations) and `match e { C => { .. } }` (`Stmt.onWhy`, one arm per case).
             A bare call of such a function has no form (`Stmt.call` needs `gruende = 0`).
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


namespace Gabbro.Grammatik.Parser.UebersetzeProben24

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- A function that fails with a named reason. -/
def fail_ok : String :=
  "module m { reason G { Weg = 1 \"weg\" exhaustive } impl fn hr(x : u32 in 0 .. 9) -> u32 in 0 .. 9 or G effects { pure } { if x == 0 { return G::Weg; } return x; } }"
theorem fail_ok_stufe : stufe fail_ok = "OK" := by decide +kernel

/-- A reason that is not a case of the channel. -/
def case_refused : String :=
  "module m { reason G { Weg = 1 \"weg\" exhaustive } impl fn hr(x : u32 in 0 .. 9) -> u32 in 0 .. 9 or G effects { pure } { if x == 0 { return G::Fort; } return x; } }"
theorem case_refused_stufe : stufe case_refused = "elab: reason case unknown: Fort" := by decide +kernel

/-- The caller handles the reason by a match, in a nested block. -/
def else_ok : String :=
  "module m { reason G { Weg = 1 \"weg\" exhaustive } impl fn hr(x : u32 in 0 .. 9) -> u32 in 0 .. 9 or G effects { pure } { if x == 0 { return G::Weg; } return x; } impl fn f(c : bool) -> u32 in 0 .. 9 { if c { let y = hr(4) else (e) { match e { Weg => { return 0; } } return 0; } return y; } return 0; } }"
theorem else_ok_stufe : stufe else_ok = "OK" := by decide +kernel

/-- A bare call of a function with a channel has no form. -/
def bare_refused : String :=
  "module m { reason G { Weg = 1 \"weg\" exhaustive } impl fn hr(x : u32 in 0 .. 9) -> u32 in 0 .. 9 or G effects { pure } { if x == 0 { return G::Weg; } return x; } impl fn f(c : bool) -> u32 in 0 .. 9 { if c { let y = hr(4); return y; } return 0; } }"
theorem bare_refused_stufe : stufe bare_refused = "elab: call of a function with a reason channel needs `let .. else`" := by decide +kernel

/-- At the top level of a body: `Endblock.bindCallElse` (Track P, 2026-10-18; was a model gap). -/
def else_top_ok : String :=
  "module m { reason G { Weg = 1 \"weg\" exhaustive } impl fn hr(x : u32 in 0 .. 9) -> u32 in 0 .. 9 or G effects { pure } { if x == 0 { return G::Weg; } return x; } impl fn f() -> u32 in 0 .. 9 { let y = hr(4) else (e) { match e { Weg => { return 0; } } return 0; } return y; } }"
theorem else_top_ok_stufe : stufe else_top_ok = "OK" := by decide +kernel

/-- Planted defect: the `else` branch falls off the end (it must not), so the unit is refused. -/
def else_top_refused : String :=
  "module m { reason G { Weg = 1 \"weg\" exhaustive } impl fn hr(x : u32 in 0 .. 9) -> u32 in 0 .. 9 or G effects { pure } { if x == 0 { return G::Weg; } return x; } impl fn f() -> u32 in 0 .. 9 { let y = hr(4) else (e) { } return y; } }"
theorem else_top_refused_stufe : (stufe else_top_refused != "OK") = true := by decide +kernel

/-- A reason that may be extended has no `Ty.why n`. -/
def open_refused : String :=
  "module m { reason G { Weg = 1 \"weg\" } impl fn f() { } }"
theorem open_refused_stufe : stufe open_refused = "elab: reason that is not exhaustive without G form" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben24
