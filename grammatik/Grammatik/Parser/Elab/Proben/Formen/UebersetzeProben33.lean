/-
  File:      Grammatik/Parser/Elab/Proben/Formen/UebersetzeProben33.lean
  Subject:   Track P: indirect calls and function-pointer TYPES (structural since 2026-10-21). `let p = &f;`
             binds `Expr.fnref` at `Ty.fnptr f` (`f`'s own signature; `&T` of a table stays the table pointer: the
             name decides); a written type `fn(..) .. effects { .. } costs <= n ops` is a signature of the unit
             behind the functions' (`UProg.ptrs`), at a parameter and at `let p : fn(..) = &f;`, and `&f` may be
             passed for such a parameter -- where `f` CONFORMS (`Deklaration.passt`, decided by `passtAt`).
             `p(..);` is `Stmt.callInd`, `let y = p(..);` is `Block.bindCallInd`/`Endblock.bindCallInd`, with
             `RufPasst` against the pointer type decided (`rufPasstB`). A contract on a pointer type (a `requires`,
             `Held(..)` included, or an `ensures`) is refused (the model has none, TODO O43). An indirect call is an edge of the floor relation.
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

/-- ... and at the top level of a body (`Endblock.bindCallInd`). -/
def bind_top_ok : String :=
  "module m { impl fn h(a : u32 in 0 .. 9) -> u32 in 0 .. 9 { return a; } impl fn f() -> u32 in 0 .. 9 { let p = &h; let y = p(4); return y; } }"
theorem bind_top_ok_stufe : stufe bind_top_ok = "OK" := by decide +kernel

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

/-- The function-pointer TYPE (`fn(..) .. effects { .. } costs <= n ops`) at a parameter. -/
def typ_ok : String :=
  "module m { impl fn g() { } impl fn f(p : fn() effects { } costs <= 1 ops) { } }"
theorem typ_ok_stufe : stufe typ_ok = "OK" := by decide +kernel

/-- An `ensures` on a pointer type: refused by name (the model's signatures carry no contract, TODO O43). -/
def typ2_refused : String :=
  "module m { impl fn f(p : fn(a : u32) -> bool ensures result effects { } costs <= 3 ops, q : u8) { } }"
theorem typ2_refused_stufe : stufe typ2_refused = "elab: contract on a function-pointer type without G form" := by
  decide +kernel

/-- ... and a `requires`. -/
def typ3_refused : String :=
  "module m { impl fn f(p : fn(a : u32 in 0 .. 9) requires a > 0 effects { } costs <= 3 ops) { } }"
theorem typ3_refused_stufe : stufe typ3_refused = "elab: contract on a function-pointer type without G form" := by
  decide +kernel

/-- **A call through a parameter**, and `&g` passed for it: `g` conforms (same parameters, no writes). -/
def param_ok : String :=
  "module m { impl fn g(a : u32 in 0 .. 9) { } impl fn f(p : fn(b : u32 in 0 .. 9) effects { } costs <= 2 ops) { p(3); } impl fn h() { f(&g); } }"
theorem param_ok_stufe : stufe param_ok = "OK" := by decide +kernel

/-- The value of a call through a parameter, at the top level of a body. -/
def param_bind_ok : String :=
  "module m { impl fn g(a : u32 in 0 .. 9) -> u32 in 0 .. 9 { return a; } impl fn f(p : fn(u32 in 0 .. 9) -> u32 in 0 .. 9 effects { } costs <= 2 ops) -> u32 in 0 .. 9 { let y = p(3); return y; } impl fn h() -> u32 in 0 .. 9 { let z = f(&g); return z; } }"
theorem param_bind_ok_stufe : stufe param_bind_ok = "OK" := by decide +kernel

/-- **A typed pointer `let`**: `let p : fn(..) = &g;`, then a call through it. -/
def typlet_ok : String :=
  "module m { impl fn g(a : u32 in 0 .. 9) { } impl fn h() { let p : fn(u32 in 0 .. 9) effects { } costs <= 2 ops = &g; p(2); } }"
theorem typlet_ok_stufe : stufe typlet_ok = "OK" := by decide +kernel

/-- Planted defect: `g` writes `T`, the type writes nothing -- `g` does not conform (`SigPasst.schreibt`). -/
def passt_refused : String :=
  "module m { table T count 2 { slot { v : u32, } } impl fn g(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots } { k.slots[i].v = 1; } impl fn f(p : fn(k : ptr<normal, rw> T, i : index into T) effects { } costs <= 2 ops) { } impl fn h(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots } { f(&g); } }"
theorem passt_refused_stufe : stufe passt_refused = "lower: function does not conform to the pointer type" := by
  decide +kernel

/-- ... and the other way round: a function that writes LESS than the type conforms, but a caller through the
    pointer owes the type's writes (`RufPasst` against the type). -/
def rechte_refused : String :=
  "module m { table T count 2 { slot { v : u32, } } impl fn g(k : ptr<normal, rw> T, i : index into T) { } impl fn f(p : fn(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots } costs <= 2 ops, k : ptr<normal, rw> T, i : index into T) { p(k, i); } }"
theorem rechte_refused_stufe : stufe rechte_refused = "lower: call through a pointer against the rights of its type" := by
  decide +kernel

/-- ... admitted where the caller holds the type's writes, with `&g` (fewer writes) passed. -/
def rechte_ok : String :=
  "module m { table T count 2 { slot { v : u32, } } impl fn g(k : ptr<normal, rw> T, i : index into T) { } impl fn f(p : fn(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots } costs <= 2 ops, k : ptr<normal, rw> T, i : index into T) effects { writes k.slots } { p(k, i); } impl fn h(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots } { f(&g, k, i); } }"
theorem rechte_ok_stufe : stufe rechte_ok = "OK" := by decide +kernel

/-- A pointer type without its contract does not parse (the contract is mandatory). -/
def typ_ohne_refused : String :=
  "module m { impl fn f(p : fn(), q : u8) { } }"
theorem typ_ohne_refused_stufe : stufe typ_ohne_refused = "parse: fn type without costs" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben33
