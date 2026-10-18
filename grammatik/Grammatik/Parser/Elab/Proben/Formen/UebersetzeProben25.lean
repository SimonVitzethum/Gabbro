/-
  File:      Grammatik/Parser/Elab/Proben/UebersetzeProben25.lean
  Subject:   Track P: tagged types (`Ty.sum cs`). `tagged type M = { Leer, Kurz(u32 in 0 .. 100) };` has the
             specification `[none, some (0, 100)]`; a case is `Expr.case` (`Kurz(7)`, `Leer`), a parameter or
             `let` is a variable of type `sum cs`, a result may be a tagged value, and `match m { .. }` is
             `Stmt.onTag` with one arm per case in declaration order (the payload bound in the arm).
-/
import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben25

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- `match` over a tagged parameter. -/
def match_ok : String :=
  "module m { tagged type M = { Leer, Kurz(u32 in 0 .. 100) }; impl fn f(m : M) -> u32 in 0 .. 100 { match m { Leer => { return 0; } Kurz(k) => { return k; } } return 0; } }"
theorem match_ok_stufe : stufe match_ok = "OK" := by decide +kernel

/-- Arms in another order. -/
def match_order_ok : String :=
  "module m { tagged type M = { Leer, Kurz(u32 in 0 .. 100) }; impl fn f(m : M) -> u32 in 0 .. 100 { match m { Kurz(k) => { return k; } Leer => { return 0; } } return 0; } }"
theorem match_order_ok_stufe : stufe match_order_ok = "OK" := by decide +kernel

/-- Every case needs its arm. -/
def match_arms_refused : String :=
  "module m { tagged type M = { Leer, Kurz(u32 in 0 .. 100) }; impl fn f(m : M) -> u32 in 0 .. 100 { match m { Leer => { return 0; } } return 0; } }"
theorem match_arms_refused_stufe : stufe match_arms_refused = "elab: match arms without G form" := by decide +kernel

/-- The payload binder is bound by `Kurz(k)` only: `Leer(k)` has none. -/
def match_payload_refused : String :=
  "module m { tagged type M = { Leer, Kurz(u32 in 0 .. 100) }; impl fn f(m : M) -> u32 in 0 .. 100 { match m { Leer(k) => { return 0; } Kurz(k) => { return k; } } return 0; } }"
theorem match_payload_refused_stufe : stufe match_payload_refused = "elab: match arm payload without G form" := by decide +kernel

/-- A tagged result built from cases. -/
def make_ok : String :=
  "module m { tagged type M = { Leer, Kurz(u32 in 0 .. 100) }; impl fn f(k : bool) -> M { if k { return Kurz(7); } return Leer; } }"
theorem make_ok_stufe : stufe make_ok = "OK" := by decide +kernel

/-- The payload must fit its range. -/
def make_range_refused : String :=
  "module m { tagged type M = { Leer, Kurz(u32 in 0 .. 100) }; impl fn f(k : bool) -> M { if k { return Kurz(700); } return Leer; } }"
theorem make_range_refused_stufe : stufe make_range_refused = "lower: value outside range" := by decide +kernel

/-- A `let` of a case, matched at once. -/
def let_ok : String :=
  "module m { tagged type M = { Leer, Kurz(u32 in 0 .. 100) }; impl fn f() -> u32 in 0 .. 100 { let x = Kurz(3); match x { Leer => { return 0; } Kurz(k) => { return k; } } return 0; } }"
theorem let_ok_stufe : stufe let_ok = "OK" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben25
