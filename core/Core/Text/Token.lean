module

public import Init.Data.Char.Basic
public import Init.Data.List.Basic

@[expose] public section

namespace Gabbro.Core.Text

/-- Raw source in Unicode scalar order. Source offsets count scalars. -/
abbrev RawText := List Char

/-- A half-open source interval. The lexical judgment establishes its bounds. -/
structure Span where
  start : Nat
  stop : Nat
  deriving DecidableEq

/-- A decimal literal retains its written scale and its signed exponent. -/
structure Decimal where
  whole : Nat
  fraction : Nat
  places : Nat
  exponent : Int
  deriving DecidableEq

/-- Words are contextual. A grammar rule distinguishes keywords from names. -/
inductive Token where
  | word (spelling : List Char)
  | punctuation (spelling : List Char)
  | natural (value : Nat)
  | decimal (value : Decimal)
  | string (decoded : List Char)
  deriving DecidableEq

inductive Trivia where
  | whitespace
  | lineComment
  | docComment
  | blockComment
  deriving DecidableEq

inductive PieceKind where
  | semantic (token : Token)
  | trivia (kind : Trivia)
  deriving DecidableEq

/-- The spelling is kept verbatim, including trivia and literal escapes. -/
structure Piece where
  start : Nat
  spelling : List Char
  kind : PieceKind
  deriving DecidableEq

def Piece.span (piece : Piece) : Span :=
  ⟨piece.start, piece.start + piece.spelling.length⟩

structure LocatedToken where
  span : Span
  value : Token
  deriving DecidableEq

def semanticTokens : List Piece → List LocatedToken
  | [] => []
  | piece :: rest =>
    match piece.kind with
    | .semantic token => ⟨piece.span, token⟩ :: semanticTokens rest
    | .trivia _ => semanticTokens rest

def spellings : List Piece → RawText
  | [] => []
  | piece :: rest => piece.spelling ++ spellings rest

end Gabbro.Core.Text
