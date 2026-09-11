/-
  P22 probe, LESESTELLE gap #06 `dec` (G-LEX).
  Rule: a `dec` token is the decimal spelling of an integer literal, exactly
  one spelling. The parser feeds its VALUE to `Expr.lit`, where it becomes
  both bounds n..n; the spelling itself never reaches the tree.
  Witness: the tree node for the token `42`.
  Check with: LEAN_PATH=grammatik/.lake/build/lib/lean lean <this file>.
-/
import Grammatik.Syntax

open Gabbro.Grammatik

variable (D : Deklaration)

/-- Gap #06: token `42` (dec spelling) is `Expr.lit` with bounds 42..42. -/
example : Expr D [] [] (.int 42 42) := .lit 42
