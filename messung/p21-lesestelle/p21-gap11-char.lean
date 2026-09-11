/-
  GAP-11 `char` (G-LEX) -- LESESTELLE probe, p21 (odd).
  Registry: messung/SYNTAX-PARSER-ENTWURF.md, eleventh LESESTELLE row.
  EBNF (dokumente/SYNTAX.md, Lexis): char = ? any character except quote and newline ?.

  MAPPING RULE (tree vs token). `char` is a lexer character class with no
  constructor. It never reaches the tree; it is the CONTENT class inside
  `string`, and strings are the content of `claim`, `reason`, `assume`,
  `section` and `asm` strings only (SYNTAX.md, Lexis). The parser keeps the
  exclusion test (not quote, not newline) at the lexer and passes the string
  content upward as data attached to those five declaration forms.

  MINIMAL PARSE WITNESS. Surface `a` is string content; surface `"` ends the
  string instead (p22's even gap `quote`); a line break ends the line instead
  (GAP-13 `newline`). The model below is the content-class test.
-/

namespace P21.Gap11Char

/-- The content class: any character except quote and newline. -/
def isStringChar (c : Char) : Bool := c != '"' && c != '\n'

-- Surface `a` inside a string: content.
example : isStringChar 'a' = true := rfl
-- Surface `"`: not content -- it is the delimiter (even gap `quote`).
example : isStringChar '"' = false := rfl
-- A line break: not content -- it is `newline` (GAP-13).
example : isStringChar '\n' = false := rfl

-- No carrier link by design: `char` feeds `string` content, and strings attach
-- as data to claim/reason/assume/section/asm forms, never as a term.

end P21.Gap11Char
