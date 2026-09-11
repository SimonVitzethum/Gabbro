/-
  P22 probe, LESESTELLE gap #02 `letter` (G-LEX).
  Rule: a letter is a lexer character class (SYNTAX.md lexis: a-z, A-Z,
  German letters). Letters build identifiers; no constructor takes a letter.
  Witness: the class as a Boolean predicate, with checked examples.
  Check with: LEAN_PATH=grammatik/.lake/build/lib/lean lean <this file>.
-/

/-- Gap #02: the `letter` class. -/
def p22Letter (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') ||
  c == 'ä' || c == 'ö' || c == 'ü' || c == 'Ä' || c == 'Ö' || c == 'Ü' || c == 'ß'

example : p22Letter 'a' = true := rfl
example : p22Letter 'Z' = true := rfl
example : p22Letter 'ß' = true := rfl
example : p22Letter 'Ä' = true := rfl
example : p22Letter '0' = false := rfl
example : p22Letter '_' = false := rfl
