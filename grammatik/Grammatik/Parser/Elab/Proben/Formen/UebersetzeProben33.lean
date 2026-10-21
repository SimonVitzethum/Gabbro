/-
  File:      Grammatik/Parser/Elab/Proben/Formen/UebersetzeProben33.lean
  Subject:   Track P: indirect calls in the numbering of `declOf` (one signature per function, `sig f = f`).
             `let p = &f;` binds `Expr.fnref f f rfl` at `Ty.fnptr f` (`&T` of a table stays the table pointer:
             the name decides); `p(..);` is `Stmt.callInd` and `let y = p(..);` is `Block.bindCallInd`, with the
             premises of a direct call of `f` decided as for a direct call. The bound form is a `Block` form only
             (`Endblock` has no `bindCallInd`). An indirect call is an edge of the floor relation.
-/
import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben33

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- A call through a pointer bound at the top level of a body. -/
def ind_ok : String :=
  "module m { impl fn g(a : u32 in 0 .. 9) { } impl fn f() { let p = &g; p(3); } }"
theorem ind_ok_stufe : stufe ind_ok = "OK" := by decide +kernel

/-- Planted defect: the argument lies outside the parameter range of the function pointed at. -/
def ind_arg_refused : String :=
  "module m { impl fn g(a : u32 in 0 .. 9) { } impl fn f() { let p = &g; p(30); } }"
theorem ind_arg_refused_stufe : stufe ind_arg_refused = "lower: value outside range" := by decide +kernel

/-- The value of an indirect call, bound in a nested block. -/
def bind_ok : String :=
  "module m { impl fn h(a : u32 in 0 .. 9) -> u32 in 0 .. 9 { return a; } impl fn f(c : bool) -> u32 in 0 .. 9 { if c { let p = &h; let y = p(4); return y; } return 0; } }"
theorem bind_ok_stufe : stufe bind_ok = "OK" := by decide +kernel

/-- ... and at the top level of a body it has no form. -/
def bind_top_refused : String :=
  "module m { impl fn h(a : u32 in 0 .. 9) -> u32 in 0 .. 9 { return a; } impl fn f() -> u32 in 0 .. 9 { let p = &h; let y = p(4); return y; } }"
theorem bind_top_refused_stufe : stufe bind_top_refused =
    "lower: lower: an indirect call bound at the top level of a body has no G form (Endblock lacks bindCallInd)" := by
  decide +kernel

/-- `w` holds `L` (rank 0) across `h`, which reaches `M` (rank 1) only through a pointer: admitted. -/
def floor_ind_ok : String :=
  "module m { lock L protects { } rank 0; lock M protects { } rank 1; impl fn g() effects { locks M } { locks M { } } impl fn h() { let p = &g; p(); } impl fn w() effects { locks L } { locks L { h(); } } }"
theorem floor_ind_ok_stufe : stufe floor_ind_ok = "OK" := by decide +kernel

/-- Planted defect: `w` holds `M` across `h`, which reaches `L` (rank 0) only through a pointer. Refused because
    the indirect call is an edge of the floor relation (without the edge `h` had the floor 2). -/
def floor_ind_refused : String :=
  "module m { lock L protects { } rank 0; lock M protects { } rank 1; impl fn g() effects { locks L } { locks L { } } impl fn h() { let p = &g; p(); } impl fn w() effects { locks M } { locks M { h(); } } }"
theorem floor_ind_refused_stufe :
    stufe floor_ind_refused = "lower: call: a held lock does not rank below the callee's floor" := by decide +kernel

/-- The function-pointer TYPE (`fn(..) .. effects { .. } costs <= n ops`) is read by the parser (up to the `ops`
    that ends its contract); its elaboration waits for the structural pointer types of the model. -/
def typ_refused : String :=
  "module m { impl fn g() { } impl fn f(p : fn() effects { } costs <= 1 ops) { } }"
theorem typ_refused_stufe : stufe typ_refused = "elab: type without G form" := by decide +kernel

/-- ... also in a list of parameters with a result, an `ensures` and a parameter behind it. -/
def typ2_refused : String :=
  "module m { impl fn f(p : fn(a : u32) -> bool ensures result effects { pure } costs <= 3 ops, q : u8) { } }"
theorem typ2_refused_stufe : stufe typ2_refused = "elab: type without G form" := by decide +kernel

/-- A pointer type without its contract does not parse (the contract is mandatory). -/
def typ_ohne_refused : String :=
  "module m { impl fn f(p : fn(), q : u8) { } }"
theorem typ_ohne_refused_stufe : stufe typ_ohne_refused = "parse: fn type without costs" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben33
