/-
  P22 probe, LESESTELLE gap #20 `bitpos` (G-LAYOUT).
  Rule: a layout position is erased. `@[hi:lo]`, `offset_into`, and `@bitpos`
  become `Expr.bitfeld`: the positions arrive as computed `Nat` arguments
  (offset and width), never as syntax. A plain `int` position is the
  emitter's alone; nothing of it reaches the tree.
  Witness: `Expr.bitfeld` takes `(lo' breite : Nat)`; the `#check` output
  below is the evidence (no position syntax in the signature).
  Check with: LEAN_PATH=grammatik/.lake/build/lib/lean lean <this file>.
-/
import Grammatik.Zucker

open Gabbro.Grammatik

#check @Expr.bitfeld
#check @Expr.leseBytes
