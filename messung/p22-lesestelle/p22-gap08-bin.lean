/-
  P22 probe, LESESTELLE gap #08 `bin` (G-LEX).
  Rule: a `bin` token is the binary spelling of an integer literal (`0b`
  prefix, one spelling). Like every integer spelling it feeds its VALUE to
  `Expr.lit`, where it becomes both bounds n..n; the prefix and the base
  never reach the tree.
  Witness: the tree node for the token `0b101` (value 5).
  Check with: LEAN_PATH=grammatik/.lake/build/lib/lean lean <this file>.
-/
import Grammatik.Syntax

open Gabbro.Grammatik

variable (D : Deklaration)

/-- Gap #08: token `0b101` (bin spelling) is `Expr.lit` with bounds 5..5. -/
example : Expr D [] [] (.int 5 5) := .lit 5
