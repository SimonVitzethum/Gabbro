/-
  GAP-03 `digit` (G-LEX) -- LESESTELLE probe, p21 (odd).
  Registry: messung/SYNTAX-PARSER-ENTWURF.md, third LESESTELLE row.
  EBNF (dokumente/SYNTAX.md, Lexis): digit = "0" … "9".

  MAPPING RULE (tree vs token). `digit` is a lexer character class with no
  constructor. It never reaches the tree itself; it feeds `dec` (and through
  it `int`), where the digit SEQUENCE becomes a value. The parser keeps the
  class membership test at the lexer and passes only values upward.

  MINIMAL PARSE WITNESS. Surface `7` is a digit; surface `a` is not --
  `a` starts an `ident` instead. The model below is the class test;
  the value it guards feeds `Expr.lit` through GAP-05 (`int`).
-/
import Grammatik.Syntax

namespace P21.Gap03Digit

/-- The lexer class: exactly "0" through "9". -/
def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

-- Surface `7`: a digit.
example : isDigit '7' = true := rfl
-- Surface `a`: not a digit (an `ident` start).
example : isDigit 'a' = false := rfl
-- Surface `_`: not a digit either (an `ident` start or separator).
example : isDigit '_' = false := rfl

-- Carrier link: digit sequences become values at `int`, whose tree is `Expr.lit`.
open Gabbro.Grammatik in
#check @Expr.lit

end P21.Gap03Digit
