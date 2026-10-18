/-
  File:      Grammatik/Parser/Elab/UebersetzeProben9.lean
  Subject:   Track P: `traverse` with `leave`/`next` and a `return` under `locks`, at the U level (no
             lexing: the kernel lexes a table source in 20 GB). `Stmt.traverse` has a body with `l = true`,
             the binder is an index into the table, and `leave`/`next` exist only inside a loop.
-/
import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben9

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000

/-- One table with a `bool` field, one lock, one function `w(k)` with the given flat body. -/
def prog (body : List UStmt) (held : List String := ["L"]) : UProg :=
  { tabs := [{ name := "T", count := 2, cols := [("f", 0, 1)], bools := ["f"] }],
    locks := [{ name := "L", rank := 0, guard := ["T"] }],
    fns := [{ name := "w", params := [("k", .ptr 0 true)], kinds := [.ptr 0 true], res := none,
              held := held, puts := ["T"], gives := [], body := body, ret := .empty }],
    roots := [] }

def ok? (u : UProg) : String :=
  match lowerAllg u with
  | .ok _ => "OK"
  | .error e => e

/-- Claim the first free slot: `traverse i … { if k.slots[i].f { k.slots[i].f = false; leave i; } }`. -/
def claim : List UStmt :=
  [.loopBeg "i" "T" .tru,
    .ifBeg (.slotB "k" "f" (.param "i")),
    .assignB "k" "f" (.param "i") .fls, .leave "i",
    .ifElse, .blkEnd, .blkEnd]

theorem claim_ok : ok? (prog claim) = "OK" := by decide +kernel

/-- `leave` outside a loop has no G form (`Stmt.leave` needs `l = true`). -/
theorem leave_outside : ok? (prog [.leave "i"]) = "lower: leave outside a traverse" := by decide +kernel

/-- `next` too. -/
theorem next_outside : ok? (prog [.next "i"]) = "lower: next outside a traverse" := by decide +kernel

/-- The binder is an index into the table, and only inside the loop. -/
theorem binder_scope :
    ok? (prog [.loopBeg "i" "T" .tru, .blkEnd, .assignB "k" "f" (.param "i") .fls])
      = "name unknown: i" := by decide +kernel

/-- A `return` under `locks` has no G form: `Stmt.ret` needs the held list to be the contract end. -/
theorem ret_under_locks :
    ok? (prog [.lockBeg "L", .ret .empty, .blkEnd] []) = "lower: return under locks has no G form" := by
  decide +kernel

/-- A traverse over an unknown table is refused by name. -/
theorem traverse_unknown :
    ok? (prog [.loopBeg "i" "Nix" .tru, .blkEnd]) = "table unknown: Nix" := by decide +kernel

/-- An unclosed traverse is refused. -/
theorem traverse_unclosed :
    ok? (prog [.loopBeg "i" "T" .tru]) = "lower: a traverse is not closed" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben9
