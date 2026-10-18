/-
  File:      Grammatik/Parser/Elab/UebersetzeProben12.lean
  Subject:   Track P: statics (`UGlob`, `Expr.glob`, `Stmt.assignGlob`, `Declaration.Glob := Fin n`),
             from source text. Table-free sources (kernel memory). A static is ONE value, an integer
             range or `bool`; only a `mut` static is written, and only where the function declares
             `writes X`.
-/
import Grammatik.Parser.Elab.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben12

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- `beispiele/187`: a `bool` static, a writer and a reader. -/
def flag_ok : String :=
  "module m { static mut A : bool = false; impl fn h() effects { writes A } { A = true; } impl fn g() -> bool effects { reads A } { return A; } }"
theorem flag_ok_stufe : stufe flag_ok = "OK" := by decide +kernel

/-- A number static, read. -/
def num_ok : String :=
  "module m { static N : u32 = 5; impl fn f() -> u32 effects { reads N } { return N; } }"
theorem num_ok_stufe : stufe num_ok = "OK" := by decide +kernel

/-- Only a `mut` static is written. -/
def immutable_refused : String :=
  "module m { static A : bool = false; impl fn h() effects { writes A } { A = true; } }"
theorem immutable_refused_stufe : stufe immutable_refused = "elab: write to an immutable static" := by
  decide +kernel

/-- A write needs the declared effect: `Signatur.gschreibt` is the flag the body reads. -/
def undeclared_refused : String :=
  "module m { static mut A : bool = false; impl fn h() { A = true; } }"
theorem undeclared_refused_stufe : stufe undeclared_refused = "lower: write without right" := by
  decide +kernel

/-- A call writes no static its caller has no right to (`RufPasst.hg`). -/
def call_refused : String :=
  "module m { static mut A : bool = false; impl fn h() effects { writes A } { A = true; } impl fn k() { h(); } }"
theorem call_refused_stufe : stufe call_refused = "lower: call writes without right" := by decide +kernel

/-- An initialiser outside its range has no `sp0` value. -/
def range_refused : String :=
  "module m { static N : u8 = 300; impl fn f() -> u8 { return N; } }"
theorem range_refused_stufe : stufe range_refused = "elab: static initialiser outside its range" := by
  decide +kernel

/-- A `bool` static is no number. -/
def bool_number_refused : String :=
  "module m { static A : bool = false; impl fn f() -> u32 { return A; } }"
theorem bool_number_refused_stufe : stufe bool_number_refused = "elab: bool static as a number" := by
  decide +kernel

/-- A number static is no truth value. -/
def number_bool_refused : String :=
  "module m { static N : u32 = 1; impl fn f() -> bool { return N; } }"
theorem number_bool_refused_stufe : stufe number_bool_refused = "elab: number static as a truth value" := by
  decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben12
