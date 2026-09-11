/-
  GAP-05 `int` (G-LEX) -- LESESTELLE probe, p21 (odd).
  Registry: messung/SYNTAX-PARSER-ENTWURF.md, fifth LESESTELLE row.
  EBNF (dokumente/SYNTAX.md, Lexis): int = dec | hex | bin.

  MAPPING RULE (tree vs token). `int` has no constructor as a term: the
  literal VALUE feeds `Expr.lit` bounds, and the value becomes BOTH bounds
  `n..n`. The spelling arm (decimal, hex, binary) is discharged by the lexer;
  only the value crosses into the tree. So surface `42`, `0x2A` and `0b101010`
  are three spellings of one tree: `Expr.lit 42 : Expr Γ Λ (.int 42 42)`.

  MINIMAL PARSE WITNESS. Surface `42` (decimal arm) evaluates to 42, hence
  the tree `Expr.lit 42` with bounds 42..42. The model below is the
  digit-sequence valuation; the hex and binary arms are GAP-07 and p22's
  even gap respectively and agree on the value by the same rule.
-/
import Grammatik.Syntax

namespace P21.Gap05Int

/-- Value of a decimal digit sequence, head = most significant. -/
def digitsVal : List Nat → Nat
  | [] => 0
  | d :: ds => d * 10 ^ ds.length + digitsVal ds

-- Surface `42`: the value is 42, so both bounds of the `Expr.lit` tree are 42.
example : digitsVal [4, 2] = 42 := rfl
-- Surface `0`: the empty bound, still both bounds equal.
example : digitsVal [0] = 0 := rfl

-- Carrier link: the value becomes both bounds n..n at `Expr.lit`.
open Gabbro.Grammatik in
#check @Expr.lit

end P21.Gap05Int
