/-
  File:      Grammatik/Parser/Elab/UebersetzeProben7.lean
  Subject:   Track P: `let` inside and after a `locks` block, at the U level (no lexing: the kernel
             lexes a table source in 20 GB). The binding of a `locks` block is the block's own.
-/
import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben7

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000

/-- One table, one lock, one function `w(k, i, n)` with the given flat body. -/
def prog (body : List UStmt) : UProg :=
  { tabs := [{ name := "T", count := 2, cols := [("v", 0, 4294967295)] }],
    locks := [{ name := "L", rank := 0, guard := ["T"] }],
    fns := [{ name := "w",
              params := [("k", .ptr 0 true), ("i", .index 2), ("n", .int 0 255)],
              kinds := [.ptr 0 true, .index 0, .int], res := none, held := [],
              puts := ["T"], gives := [], body := body, ret := .empty }],
    roots := [] }

def ok? (u : UProg) : String :=
  match lowerAllg u with
  | .ok _ => "OK"
  | .error e => e

/-- A `let` inside `locks L { ... }` binds for the rest of that block and is written to a slot. -/
theorem locks_let_ok :
    ok? (prog [.lockBeg "L", .bind "x" (some (0, 4294967295)) (.param "n"),
      .assign "k" "v" (.param "i") (.param "x"), .blkEnd]) = "OK" := by
  decide +kernel

/-- ... and it does not outlive the block. -/
theorem locks_let_scope :
    ok? (prog [.lockBeg "L", .bind "x" none (.param "n"), .blkEnd,
      .assign "k" "v" (.param "i") (.param "x")]) = "name unknown: x" := by
  decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben7
