/-
  File:      Grammatik/Parser/Elab/UebersetzeProben7.lean
  Subject:   Track P: `let` inside and after a `locks` block, at the U level (no lexing: the kernel
             lexes a table source in 20 GB). The binding of a `locks` block is the block's own.
-/
module
public import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section


namespace Gabbro.Grammatik.Parser.UebersetzeProben7

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000

/-- One table, one lock, one function `w(k, i, n)` with the given flat body. -/
def prog (body : List UStmt) : UProg :=
  { tabs := [{ name := "T", count := 2, cols := [("v", 0, 4294967295)] }],
    locks := [{ name := "L", rank := 0, guard := ["T"] }],
    fns := [{ name := "w",
              params := [("k", .ptr (.table 0 (true, true))), ("i", .index 2), ("n", .int 0 255)],
              kinds := [.ptr (.table 0 (true, true)), .index 0, .int], res := none, held := [],
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
