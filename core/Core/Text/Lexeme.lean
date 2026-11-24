module

public import Core.Text.Token
public import Init.Data.Int.Basic

@[expose] public section

namespace Gabbro.Core.Text

def isLetter (c : Char) : Prop :=
  ('a' ≤ c ∧ c ≤ 'z') ∨ ('A' ≤ c ∧ c ≤ 'Z') ∨ c ∈ ['ä', 'ö', 'ü', 'Ä', 'Ö', 'Ü', 'ß']

def isNameStart (c : Char) : Prop := isLetter c ∨ c = '_'

def isNamePart (c : Char) : Prop := isNameStart c ∨ ('0' ≤ c ∧ c ≤ '9')

def digitValue (c : Char) (n : Nat) : Prop :=
  ('0' ≤ c ∧ c ≤ '9' ∧ n = c.toNat - '0'.toNat) ∨
  ('a' ≤ c ∧ c ≤ 'f' ∧ n = 10 + (c.toNat - 'a'.toNat)) ∨
  ('A' ≤ c ∧ c ≤ 'F' ∧ n = 10 + (c.toNat - 'A'.toNat))

/-- Positional value and digit count, ignoring separators. -/
inductive Digits (base : Nat) : List Char → Nat → Nat → Prop where
  | nil : Digits base [] 0 0
  | digit : digitValue c d → d < base → Digits base rest value places →
      Digits base (c :: rest) (d * base ^ places + value) (places + 1)
  | separator : Digits base rest value places → Digits base ('_' :: rest) value places

/-- A numeral starts with a digit. -/
def Numeral (base : Nat) (spelling : List Char) (value places : Nat) : Prop :=
  ∃ c rest d, spelling = c :: rest ∧ digitValue c d ∧ d < base ∧ Digits base spelling value places

/-- Exponents use a nonempty sequence of decimal digits without separators. -/
def ExponentDigits (spelling : List Char) (value places : Nat) : Prop :=
  Numeral 10 spelling value places ∧ '_' ∉ spelling

inductive Exponent : List Char → Int → Prop where
  | absent : Exponent [] 0
  | unsigned : ExponentDigits text n places → Exponent ('e' :: text) (Int.ofNat n)
  | positive : ExponentDigits text n places → Exponent ('e' :: '+' :: text) (Int.ofNat n)
  | negative : ExponentDigits text n places → Exponent ('e' :: '-' :: text) (-Int.ofNat n)

/-- The common escape alphabet, plus the delimiter for the current literal. -/
inductive Escape (delimiter : Char) : Char → Char → Prop where
  | newline : Escape delimiter 'n' '\n'
  | tab : Escape delimiter 't' '\t'
  | carriageReturn : Escape delimiter 'r' '\r'
  | zero : Escape delimiter '0' (Char.ofNat 0)
  | backslash : Escape delimiter '\\' '\\'
  | quote : Escape delimiter delimiter delimiter

inductive StringContent : List Char → List Char → Prop where
  | nil : StringContent [] []
  | plain : c ≠ '"' → c ≠ '\\' → c ≠ '\n' →
      StringContent raw decoded → StringContent (c :: raw) (c :: decoded)
  | escaped : Escape '"' code c → StringContent raw decoded →
      StringContent ('\\' :: code :: raw) (c :: decoded)

inductive CharacterContent : List Char → Char → Prop where
  | plain : 32 ≤ c.toNat → c.toNat ≤ 126 → c ≠ '\'' → c ≠ '\\' → CharacterContent [c] c
  | escaped : Escape '\'' code c → CharacterContent ['\\', code] c

/-- A comment body includes its closing delimiter. This makes a marker
    spanning the last body character and the closer visible to the rule. -/
inductive BlockBody : List Char → Prop where
  | close : BlockBody ['*', '/']
  | plain : (∀ tail, c :: rest ≠ '/' :: '*' :: tail) →
      (∀ tail, c :: rest ≠ '*' :: '/' :: tail) →
      BlockBody rest → BlockBody (c :: rest)
  | nested : BlockBody child → BlockBody rest →
      BlockBody (['/', '*'] ++ child ++ rest)

def isSpace (c : Char) : Prop := c ∈ [' ', '\t', '\r', '\n']

/-- All punctuation is specified independently of dispatch order. -/
def punctuation : List String :=
  ["<<%", "..<", "::", "..", "->", "=>", "==", "!=", "<=", ">=", "<<", ">>",
    "+=", "+%", "+|", "-=", "-%", "*%", "&&", "&=", "||", "|=", ":", ";", ",",
    ".", "(", ")", "{", "}", "[", "]", "<", ">", "=", "+", "-", "*", "/", "%",
    "!", "&", "|", "^", "~", "?", "@", "#"]

/-- A single exact spelling with its semantic value or trivia class. -/
inductive Lexeme : List Char → PieceKind → Prop where
  | word : isNameStart c → (∀ a ∈ rest, isNamePart a) →
      Lexeme (c :: rest) (.semantic (.word (c :: rest)))
  | punctuation : word ∈ punctuation →
      Lexeme word.toList (.semantic (.punctuation word.toList))
  | decimalInteger : Numeral 10 raw value places → Lexeme raw (.semantic (.natural value))
  | hexInteger : Numeral 16 raw value places →
      Lexeme ('0' :: 'x' :: raw) (.semantic (.natural value))
  | binaryInteger : Numeral 2 raw value places →
      Lexeme ('0' :: 'b' :: raw) (.semantic (.natural value))
  | decimal : Numeral 10 left whole leftPlaces → Numeral 10 right fraction places →
      Exponent exp exponent →
      Lexeme (left ++ ['.'] ++ right ++ exp) (.semantic (.decimal ⟨whole, fraction, places, exponent⟩))
  | character : CharacterContent raw c →
      Lexeme (['\''] ++ raw ++ ['\'']) (.semantic (.natural c.toNat))
  | string : StringContent raw decoded → Lexeme (['"'] ++ raw ++ ['"']) (.semantic (.string decoded))
  | whitespace : isSpace c → (∀ a ∈ rest, isSpace a) → Lexeme (c :: rest) (.trivia .whitespace)
  | line : '\n' ∉ raw → raw.head? ≠ some '/' →
      Lexeme ('/' :: '/' :: raw) (.trivia .lineComment)
  | doc : '\n' ∉ raw → raw.head? ≠ some '/' →
      Lexeme ('/' :: '/' :: '/' :: raw) (.trivia .docComment)
  | extendedLine : '\n' ∉ raw → Lexeme ('/' :: '/' :: '/' :: '/' :: raw) (.trivia .lineComment)
  | block : BlockBody raw → Lexeme (['/', '*'] ++ raw) (.trivia .blockComment)

end Gabbro.Core.Text
