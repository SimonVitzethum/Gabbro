/-
  File:      Grammatik/Parser/Elab/UebersetzeProben9.lean
  Subject:   Track P: `traverse` with `leave`/`next` and a `return` under `locks`, at the U level (no
             lexing: the kernel lexes a table source in 20 GB). `Stmt.traverse` has a body with `l = true`,
             the binder is an index into the table, and `leave`/`next` exist only inside a loop.
-/
import Grammatik.Parser.Elab.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben9

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000

/-- One table with a `bool` field, one lock, one function `w(k)` with the given flat body. -/
def prog (body : List UStmt) (held : List String := ["L"]) : UProg :=
  { tabellen := [{ name := "T", count := 2, felder := [("f", 0, 1)], bools := ["f"] }],
    sperren := [{ name := "L", rank := 0, schutz := ["T"] }],
    fns := [{ name := "w", params := [("k", .ptr 0 true)], parten := [.ptr 0 true], res := none,
              held := held, schreibt := ["T"], gives := [], saetze := body, rueck := .empty }],
    wurzeln := [] }

def ok? (u : UProg) : String :=
  match lowerAllg u with
  | .ok _ => "OK"
  | .error e => e

/-- Claim the first free slot: `traverse i … { if k.slots[i].f { k.slots[i].f = false; leave i; } }`. -/
def claim : List UStmt :=
  [.schleifeAuf "i" "T" .tru,
    .wennAuf (.slotB "k" "f" (.param "i")),
    .assignB "k" "f" (.param "i") .fls, .leave "i",
    .sonst, .zu, .zu]

theorem claim_ok : ok? (prog claim) = "OK" := by decide +kernel

/-- `leave` outside a loop has no G form (`Stmt.leave` needs `l = true`). -/
theorem leave_outside : ok? (prog [.leave "i"]) = "lower: leave outside a traverse" := by decide +kernel

/-- `next` too. -/
theorem next_outside : ok? (prog [.next "i"]) = "lower: next outside a traverse" := by decide +kernel

/-- The binder is an index into the table, and only inside the loop. -/
theorem binder_scope :
    ok? (prog [.schleifeAuf "i" "T" .tru, .zu, .assignB "k" "f" (.param "i") .fls])
      = "name unknown: i" := by decide +kernel

/-- A `return` under `locks` has no G form: `Stmt.ret` needs the held list to be the contract end. -/
theorem ret_under_locks :
    ok? (prog [.sperrtAuf "L", .ret .empty, .zu] []) = "lower: return under locks has no G form" := by
  decide +kernel

/-- A traverse over an unknown table is refused by name. -/
theorem traverse_unknown :
    ok? (prog [.schleifeAuf "i" "Nix" .tru, .zu]) = "table unknown: Nix" := by decide +kernel

/-- An unclosed traverse is refused. -/
theorem traverse_unclosed :
    ok? (prog [.schleifeAuf "i" "T" .tru]) = "lower: a traverse is not closed" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben9
