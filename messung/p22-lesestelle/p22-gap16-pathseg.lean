/-
  P22 probe, LESESTELLE gap #16 `pathseg` (G-NAME).
  Rule: a path segment (word or generated operation name) resolves before
  the tree: to a declared Fn, Tab, or generated op. The tree carries the
  resolved entity, never the segment strings.
  Witness: `Expr.fnref` and `Stmt.call` take `D.Fn`, not strings; the
  `#check` output below is the evidence (no `String` argument).
  Check with: LEAN_PATH=grammatik/.lake/build/lib/lean lean <this file>.
-/
import Grammatik.Syntax

open Gabbro.Grammatik

#check @Expr.fnref
#check @Stmt.call
