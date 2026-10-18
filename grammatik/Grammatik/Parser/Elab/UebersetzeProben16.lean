/-
  File:      Grammatik/Parser/Elab/UebersetzeProben16.lean
  Subject:   Track P: truth values and mutable locals, from source text. A `bool` parameter and a `let` of a
             truth value (`Block.bind` at `Ty.bool`, `UParamArt.bool`), `let mut x : T = v;` (the binding carries
             the DECLARED range) with `x = w;` (`Stmt.assignVar`) and the compound forms `x &= w;` (sugar for
             `x = x & w;`), also at a static. A plain `let` is not assignable, and a `let mut` needs a type.
-/
import Grammatik.Parser.Elab.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben16

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- A `bool` parameter read in a condition. -/
def boolparam_ok : String :=
  "module m { impl fn f(q : bool) -> u32 in 0 .. 5 { if q { return 3; } return 4; } }"
theorem boolparam_ok_stufe : stufe boolparam_ok = "OK" := by decide +kernel

/-- A `let` of a truth value, used as a condition. -/
def boollet_ok : String :=
  "module m { impl fn f(a : u32 in 0 .. 100) -> u32 in 0 .. 5 { let r : bool = a < 50; if r { return 1; } return 2; } }"
theorem boollet_ok_stufe : stufe boollet_ok = "OK" := by decide +kernel

/-- A number used as a truth value is refused. -/
def numbool_refused : String :=
  "module m { impl fn f(a : u32 in 0 .. 100) -> u32 in 0 .. 5 { let r : bool = a; return 1; } }"
theorem numbool_refused_stufe : stufe numbool_refused = "elab: number as a truth value" := by
  decide +kernel

/-- `let mut` and an assignment in range. -/
def mut_ok : String :=
  "module m { impl fn f() -> u32 in 0 .. 100 { let mut x : u32 in 0 .. 100 = 3; x = 9; return x; } }"
theorem mut_ok_stufe : stufe mut_ok = "OK" := by decide +kernel

/-- An assignment outside the declared range: the model has no term. -/
def mut_range_refused : String :=
  "module m { impl fn f() -> u32 in 0 .. 100 { let mut x : u32 in 0 .. 10 = 3; x = 90; return x; } }"
theorem mut_range_refused_stufe : stufe mut_range_refused = "lower: value outside range" := by decide +kernel

/-- A `let` that is not `mut` is not assignable. -/
def immutable_refused : String :=
  "module m { impl fn f() -> u32 in 0 .. 100 { let x : u32 in 0 .. 100 = 3; x = 9; return x; } }"
theorem immutable_refused_stufe : stufe immutable_refused = "elab: place without G form" := by decide +kernel

/-- A `let mut` without a type has no range to carry. -/
def mut_untyped_refused : String :=
  "module m { impl fn f() -> u32 in 0 .. 100 { let mut x = 3; x = 9; return x; } }"
theorem mut_untyped_refused_stufe : stufe mut_untyped_refused = "elab: let mut without a type" := by
  decide +kernel

/-- A compound assignment at a local and at a static. -/
def compound_ok : String :=
  "module m { static mut S : u32 in 0 .. 100 = 1; impl fn f() -> u32 in 0 .. 100 effects { reads S, writes S } { let mut x : u32 in 0 .. 100 = 3; x &= 7; S &= 9; return x; } }"
theorem compound_ok_stufe : stufe compound_ok = "OK" := by decide +kernel

/-- The compound form carries the range check of the expanded one. -/
def compound_range_refused : String :=
  "module m { impl fn f() -> u32 in 0 .. 100 { let mut x : u32 in 0 .. 10 = 3; x += 9; return x; } }"
theorem compound_range_refused_stufe : stufe compound_range_refused = "lower: value outside range" := by
  decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben16
