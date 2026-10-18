/-
  File:      Grammatik/Parser/Elab/UebersetzeProben8.lean
  Subject:   Track P: `if` and `return` inside blocks (`UStmt.wennAuf`/`sonst`/`zu`, `UStmt.ret`,
             `Stmt.ite`, `Stmt.ret`), from source text. Table-free sources (kernel memory).
-/
import Grammatik.Parser.Elab.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben8

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- An early return in the `then` part, the trailing return after it. -/
def early_ok : String :=
  "module m { impl fn f(a : u8) -> u8 { if a == 0 { return 1; } return 2; } }"
theorem early_ok_stufe : stufe early_ok = "OK" := by decide +kernel

/-- An `else if` chain with an `else`, each branch a value-preserving `let`. -/
def chain_ok : String :=
  "module m { impl fn f(a : u8) -> u8 { if a == 0 { return 1; } else if a == 1 { return 2; } else { return 3; } return 4; } }"
theorem chain_ok_stufe : stufe chain_ok = "OK" := by decide +kernel

/-- A return value outside the result range is refused by the lowering, in the branch as at the end. -/
def early_range : String :=
  "module m { impl fn f(a : u8) -> u8 { if a == 0 { return 300; } return 2; } }"
theorem early_range_stufe : stufe early_range = "lower: value outside range" := by decide +kernel

/-- A function with a result that ends in an `if` without a trailing return falls off: refused. -/
def falls_off : String :=
  "module m { impl fn f(a : u8) -> u8 { if a == 0 { return 1; } } }"
theorem falls_off_stufe : stufe falls_off = "elab: Funktion mit Ergebnis faellt durch" := by decide +kernel

/-- A `let` inside a branch is the branch's own. -/
def let_branch : String :=
  "module m { impl fn f(a : u8) -> u16 { if a == 0 { let x : u16 = a; return x; } return a; } }"
theorem let_branch_stufe : stufe let_branch = "OK" := by decide +kernel

def let_branch_scope : String :=
  "module m { impl fn f(a : u8) -> u16 { if a == 0 { let x : u16 = a; return x; } return x; } }"
theorem let_branch_scope_stufe : stufe let_branch_scope = "elab: Name unbekannt: x" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben8
