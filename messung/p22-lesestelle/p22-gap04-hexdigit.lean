/-
  P22 probe, LESESTELLE gap #04 `hexdigit` (G-LEX).
  Rule: a hex digit is a digit or a-f or A-F (SYNTAX.md lexis). It feeds the
  `hex` spelling only; no constructor takes a hex digit.
  Witness: the class as a Boolean predicate, with checked examples.
  Check with: LEAN_PATH=grammatik/.lake/build/lib/lean lean <this file>.
-/

/-- Gap #04: the `hexdigit` class over the `digit` class. -/
def p22Digit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

def p22Hexdigit (c : Char) : Bool :=
  p22Digit c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

example : p22Hexdigit '9' = true := rfl
example : p22Hexdigit 'a' = true := rfl
example : p22Hexdigit 'F' = true := rfl
example : p22Hexdigit 'g' = false := rfl
example : p22Hexdigit 'x' = false := rfl
