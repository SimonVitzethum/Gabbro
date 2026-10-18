/-
  File:      Grammatik/Parser/Elab/Proben/UebersetzeProben20.lean
  Subject:   Track P: foreign bodies (`extern fn`, `D.Ax`). A call without an answer is `Stmt.axiomCall`; one with
             an answer (a number, a truth value, or `never`) is `Block.bindAxiom` / `Endblock.bindAxiom` (the
             end-block form exists, so a foreign call stands at the top of a body). An `extern fn` that
             writes, has a `requires`/`ensures` or an `or` channel has no form here.
-/
import Grammatik.Parser.Elab.Proben.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben20

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- A foreign call without an answer, at the top of a body. -/
def stmt_ok : String :=
  "module m { extern fn tick() effects { pure } costs <= 1 ops; impl fn f() effects { pure } { tick(); } }"
theorem stmt_ok_stufe : stufe stmt_ok = "OK" := by decide +kernel

/-- A foreign call with a number as the answer, bound at the top of a body. -/
def value_ok : String :=
  "module m { extern fn rd() -> u32 in 0 .. 9 effects { pure } costs <= 1 ops; impl fn f() -> u32 in 0 .. 9 { let x = rd(); return x; } }"
theorem value_ok_stufe : stufe value_ok = "OK" := by decide +kernel

/-- The answer's range is the bound variable's: returning it against a smaller range is refused. -/
def value_range_refused : String :=
  "module m { extern fn rd() -> u32 in 0 .. 9 effects { pure } costs <= 1 ops; impl fn f() -> u32 in 0 .. 5 { let x = rd(); return x; } }"
theorem value_range_refused_stufe : stufe value_range_refused = "lower: value outside range" := by decide +kernel

/-- A `-> never` handler called in a nested block. -/
def never_ok : String :=
  "module m { extern fn zeit() -> never effects { diverges } costs <= 1 ops; impl fn f(c : bool) { if c { zeit(); } } }"
theorem never_ok_stufe : stufe never_ok = "OK" := by decide +kernel

/-- Arguments are checked against the parameters of the foreign body. -/
def arg_ok : String :=
  "module m { extern fn out(v : u32 in 0 .. 9) effects { pure } costs <= 1 ops; impl fn f() effects { pure } { out(3); } }"
theorem arg_ok_stufe : stufe arg_ok = "OK" := by decide +kernel

def arg_range_refused : String :=
  "module m { extern fn out(v : u32 in 0 .. 9) effects { pure } costs <= 1 ops; impl fn f() effects { pure } { out(30); } }"
theorem arg_range_refused_stufe : stufe arg_range_refused = "lower: value outside range" := by decide +kernel

/-- A foreign body with a contract clause has no form. -/
def ensures_refused : String :=
  "module m { extern fn rd() -> u32 in 0 .. 9 ensures result < 5 effects { pure } costs <= 1 ops; impl fn f() { } }"
theorem ensures_refused_stufe : stufe ensures_refused = "elab: foreign fn clause without G form" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben20
