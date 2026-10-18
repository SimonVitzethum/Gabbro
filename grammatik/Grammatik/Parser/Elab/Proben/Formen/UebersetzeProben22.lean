/-
  File:      Grammatik/Parser/Elab/Proben/UebersetzeProben22.lean
  Subject:   Track P: option values (`Ty.opt n`, `option index into T`) and `match` over them (`Stmt.onOption`).
             An option field keeps its place in the table's fields (`UTab.opts`), an option parameter or `let`
             is a variable of type `opt n`, `None`/`Some(i)` are `Expr.none`/`Expr.some`, and the arms of a
             `match` are blocks (`Some(k)` binds `k` as an index into the table, both arms must be given).
-/
import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben22

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- `beispiele/01`'s shape: read an option field, match on it. -/
def match_ok : String :=
  "module m { table N count 4 { slot { v : u32 in 0 .. 100, n : option index into N, } } impl fn f(i : index into N) -> u32 in 0 .. 100 effects { reads N.slots } { let o : option index into N = N.slots[i].n; match o { Some(k) => { return N.slots[k].v; } None => { return 0; } } return 0; } }"
theorem match_ok_stufe : stufe match_ok = "OK" := by decide +kernel

/-- The arms in the other order. -/
def match_order_ok : String :=
  "module m { table N count 4 { slot { v : u32 in 0 .. 100, n : option index into N, } } impl fn f(i : index into N) -> u32 in 0 .. 100 effects { reads N.slots } { let o : option index into N = N.slots[i].n; match o { None => { return 0; } Some(k) => { return N.slots[k].v; } } return 0; } }"
theorem match_order_ok_stufe : stufe match_order_ok = "OK" := by decide +kernel

/-- Both arms are required. -/
def match_arms_refused : String :=
  "module m { table N count 4 { slot { v : u32 in 0 .. 100, n : option index into N, } } impl fn f(i : index into N) -> u32 in 0 .. 100 effects { reads N.slots } { let o : option index into N = N.slots[i].n; match o { Some(k) => { return N.slots[k].v; } } return 0; } }"
theorem match_arms_refused_stufe : stufe match_arms_refused = "elab: match arms without G form" := by decide +kernel

/-- The option results. -/
def ret_some_ok : String :=
  "module m { table N count 4 { slot { v : u32 in 0 .. 100, n : option index into N, } } impl fn f(i : index into N) -> option index into N { return Some(i); } }"
theorem ret_some_ok_stufe : stufe ret_some_ok = "OK" := by decide +kernel

def ret_none_ok : String :=
  "module m { table N count 4 { slot { v : u32 in 0 .. 100, n : option index into N, } } impl fn f() -> option index into N { return None; } }"
theorem ret_none_ok_stufe : stufe ret_none_ok = "OK" := by decide +kernel

/-- `Some(i)` for an index outside the table. -/
def some_count_refused : String :=
  "module m { table N count 4 { slot { v : u32 in 0 .. 100, n : option index into N, } } impl fn f() -> option index into N { return Some(4); } }"
theorem some_count_refused_stufe : stufe some_count_refused = "elab: index outside count" := by decide +kernel

/-- An option store at a field. -/
def store_ok : String :=
  "module m { table N count 4 { slot { v : u32 in 0 .. 100, n : option index into N, } } impl fn f() effects { writes N.slots } { N.slots[1].n = Some(2); N.slots[2].n = None; } }"
theorem store_ok_stufe : stufe store_ok = "OK" := by decide +kernel

/-- An option field is no number. -/
def field_number_refused : String :=
  "module m { table N count 4 { slot { v : u32 in 0 .. 100, n : option index into N, } } impl fn f() -> u32 in 0 .. 100 effects { reads N.slots } { return N.slots[1].n; } }"
theorem field_number_refused_stufe : stufe field_number_refused = "elab: option field as a number" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben22
