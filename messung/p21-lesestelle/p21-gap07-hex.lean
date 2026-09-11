/-
  GAP-07 `hex` (G-LEX) -- LESESTELLE probe, p21 (odd).
  Registry: messung/SYNTAX-PARSER-ENTWURF.md, seventh LESESTELLE row.
  EBNF (dokumente/SYNTAX.md, Lexis): hex = "0x" hexdigit { hexdigit | "_" }.

  MAPPING RULE (tree vs token). `hex` has no constructor: it is one spelling
  arm of `int` (GAP-05). The lexer consumes the `0x` prefix and the `_`
  separators, values the hexdigit sequence, and hands the VALUE to the `int`
  rule -- same tree as the decimal spelling (`Expr.lit n` with bounds n..n).
  One spelling only: `0X` is refused (L004), so the prefix test is exact.

  MINIMAL PARSE WITNESS. Surface `0x2A` values to 42 -- the same tree as
  surface `42`. The model below is the hexdigit-sequence valuation over
  digit VALUES (the `hexdigit` class itself is p22's even gap).
-/
import Grammatik.Syntax

namespace P21.Gap07Hex

/-- Value of a hexdigit-value sequence, head = most significant. -/
def hexVal : List Nat → Nat
  | [] => 0
  | d :: ds => d * 16 ^ ds.length + hexVal ds

-- Surface `0x2A`: 0x2 * 16 + 0xA = 42, same tree as decimal `42`.
example : hexVal [2, 10] = 42 := rfl
-- Surface `0xff`: the full byte.
example : hexVal [15, 15] = 255 := rfl

-- Carrier link: shared with `int` -- the value lands at `Expr.lit`.
open Gabbro.Grammatik in
#check @Expr.lit

end P21.Gap07Hex
