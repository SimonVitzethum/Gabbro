module

public import Grammatik.Parser.Lex.Lexer.Teil1
import Init.Data.String.Lemmas.Intercalate
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section

namespace Gabbro.Grammatik.Uebersetzung.LibraryFixtureScanning

open Gabbro.Grammatik.Parser

/-- A bounded equation of the canonical scanner, retaining its arbitrary suffix
    and exact remaining fuel. This carries evidence, not another scanner. -/
structure Chunk where
  characters : List Char
  tokens : List Token
  steps : Nat
  scanned : ∀ (rest : List Char) (remaining : Nat),
    scan false (characters ++ rest) (remaining + steps) =
      tokens.foldr (fun token answer => Except.map (token :: ·) answer)
        (scan false rest remaining)

private theorem token_maps (tokens : List Token) (answer : Except LexFehler (List Token)) :
    tokens.foldr (fun token result => Except.map (token :: ·) result) answer =
      Except.map (tokens ++ ·) answer := by
  induction tokens with
  | nil => cases answer <;> rfl
  | cons token tokens ih =>
    simp only [List.foldr, ih]
    cases answer <;> rfl

def characters (chunks : List Chunk) : List Char := chunks.flatMap Chunk.characters

def tokens (chunks : List Chunk) : List Token := chunks.flatMap Chunk.tokens ++ [.ende]

def steps : List Chunk → Nat
  | [] => 0
  | chunk :: rest => chunk.steps + steps rest

/-- Compose fragment spellings while their scanner data remains abstract. -/
theorem characters_join (chunks : List Chunk) :
    String.ofList (characters chunks) =
      String.join (chunks.map (fun chunk => String.ofList chunk.characters)) := by
  induction chunks with
  | nil => rfl
  | cons chunk chunks ih =>
    change String.ofList (chunk.characters ++ characters chunks) =
      String.join (String.ofList chunk.characters ::
        chunks.map (fun entry => String.ofList entry.characters))
    rw [String.ofList_append, String.join_cons, ih]

/-- Local checked scanner costs compose at the original character-count fuel. -/
theorem steps_le_length (chunks : List Chunk) :
    chunks.all (fun chunk => decide (chunk.steps ≤ chunk.characters.length)) = true →
      steps chunks ≤ (characters chunks).length := by
  induction chunks with
  | nil => intro _; exact Nat.le_refl _
  | cons chunk chunks ih =>
    intro bounded
    simp only [List.all_cons, Bool.and_eq_true] at bounded
    change chunk.steps + steps chunks ≤ (chunk.characters ++ characters chunks).length
    rw [List.length_append]
    exact Nat.add_le_add (of_decide_eq_true bounded.1) (ih bounded.2)

private theorem scan_chunks (chunks : List Chunk) (remaining : Nat) :
    scan false (characters chunks) (steps chunks + remaining) = .ok (tokens chunks) := by
  induction chunks with
  | nil => cbv
  | cons chunk rest ih =>
    change scan false (chunk.characters ++ characters rest)
      ((chunk.steps + steps rest) + remaining) =
        .ok ((chunk.tokens ++ rest.flatMap Chunk.tokens) ++ [.ende])
    rw [Nat.add_assoc, Nat.add_comm chunk.steps, chunk.scanned, ih, token_maps]
    change (Except.ok (chunk.tokens ++ (rest.flatMap Chunk.tokens ++ [.ende])) :
      Except LexFehler (List Token)) = _
    rw [List.append_assoc]

/-- Compose short checked cuts at the original character-count fuel. -/
theorem lex_chunks (chunks : List Chunk)
    (room : steps chunks ≤ (characters chunks).length + 1) :
    lexL (characters chunks) = .ok (tokens chunks) := by
  have complete := scan_chunks chunks ((characters chunks).length + 1 - steps chunks)
  have fuel : steps chunks + ((characters chunks).length + 1 - steps chunks) =
      (characters chunks).length + 1 := Nat.add_sub_of_le room
  rw [fuel] at complete
  exact complete

-- Each proof reduces only this short fragment with a symbolic suffix and fuel.
-- Token spellings and fuel costs are checked against the actual scanner here.

def Chunk.moduleSample : Chunk where
  characters := ['m', 'o', 'd', 'u', 'l', 'e', ' ', 's', 'a', 'm', 'p', 'l', 'e', ' ', '{', ' ']
  tokens := [.wort "module", .ident "sample", .zeichen "{"]
  steps := 6
  scanned := by intro rest remaining; cbv

def Chunk.moduleA : Chunk where
  characters := ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'a', ' ', '{', ' ']
  tokens := [.wort "module", .ident "a", .zeichen "{"]
  steps := 6
  scanned := by intro rest remaining; cbv

def Chunk.moduleB : Chunk where
  characters := ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'b', ' ', '{', ' ']
  tokens := [.wort "module", .ident "b", .zeichen "{"]
  steps := 6
  scanned := by intro rest remaining; cbv

def Chunk.tableTwo : Chunk where
  characters := ['t', 'a', 'b', 'l', 'e', ' ', 'R', 'o', 'w', 's', ' ', 'c', 'o', 'u', 'n', 't', ' ', '2', ' ', '{', ' ']
  tokens := [.wort "table", .ident "Rows", .wort "count", .num 2, .zeichen "{"]
  steps := 10
  scanned := by intro rest remaining; cbv

def Chunk.tableOne : Chunk where
  characters := ['t', 'a', 'b', 'l', 'e', ' ', 'R', 'o', 'w', 's', ' ', 'c', 'o', 'u', 'n', 't', ' ', '1', ' ', '{', ' ']
  tokens := [.wort "table", .ident "Rows", .wort "count", .num 1, .zeichen "{"]
  steps := 10
  scanned := by intro rest remaining; cbv

def Chunk.slot : Chunk where
  characters := ['s', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1',
    '0', ',', ' ', '}', ' ', '}', ' ']
  tokens := [.wort "slot", .zeichen "{", .ident "v", .zeichen ":", .wort "u8", .wort "in", .num 0, .zeichen "..", .num 10, .zeichen ",", .zeichen "}", .zeichen "}"]
  steps := 23
  scanned := by intro rest remaining; cbv

def Chunk.libraryHead : Chunk where
  characters := ['l', 'i', 'b', 'r', 'a', 'r', 'y', ' ', 'f', 'n', ' ', 'c', 'o', 'n', 's', 'u', 'm', 'e', '(', 'p', ' ', ':', ' ']
  tokens := [.wort "library", .wort "fn", .ident "consume", .zeichen "(", .ident "p", .zeichen ":"]
  steps := 10
  scanned := by intro rest remaining; cbv

def Chunk.libraryTail : Chunk where
  characters := ['p', 't', 'r', '<', 'n', 'o', 'r', 'm', 'a', 'l', ',', ' ', 'r', '>', ' ', 'R', 'o', 'w', 's', ')', ' ', 'p', 'a',
    'y', 'l', 'o', 'a', 'd', ' ', 'R', 'o', 'w', 's', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ';', ' ', '}', ' ']
  tokens := [.wort "ptr", .zeichen "<", .wort "normal", .zeichen ",", .wort "r", .zeichen ">", .ident "Rows", .zeichen ")", .wort "payload", .ident "Rows", .zeichen "{", .wort "return", .zeichen ";", .zeichen "}"]
  steps := 22
  scanned := by intro rest remaining; cbv

def Chunk.translatorHead : Chunk where
  characters := ['t', 'r', 'a', 'n', 's', 'l', 'a', 't', 'o', 'r', ' ', 'b', 'u', 'i', 'l', 'd', ' ', 'f', 'o', 'r', ' ', 'c', 'o',
    'n', 's', 'u', 'm', 'e', '(', 'r', 'e', 'g', 'i', 'o', 'n', ' ', ':', ' ']
  tokens := [.wort "translator", .ident "build", .wort "for", .ident "consume", .zeichen "(", .ident "region", .zeichen ":"]
  steps := 12
  scanned := by intro rest remaining; cbv

def Chunk.inputTwo : Chunk where
  characters := ['[', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', ';', ' ', '2', ']', ')', ' ', '-', '>', ' ']
  tokens := [.zeichen "[", .wort "u8", .wort "in", .num 0, .zeichen "..", .num 10, .zeichen ";", .num 2, .zeichen "]", .zeichen ")", .zeichen "->"]
  steps := 18
  scanned := by intro rest remaining; cbv

def Chunk.outputTwo : Chunk where
  characters := ['[', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', ';', ' ', '2', ']', ' ']
  tokens := [.zeichen "[", .wort "u8", .wort "in", .num 0, .zeichen "..", .num 10, .zeichen ";", .num 2, .zeichen "]"]
  steps := 15
  scanned := by intro rest remaining; cbv

def Chunk.inputOne : Chunk where
  characters := ['[', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', ';', ' ', '1', ']', ')', ' ', '-', '>', ' ']
  tokens := [.zeichen "[", .wort "u8", .wort "in", .num 0, .zeichen "..", .num 10, .zeichen ";", .num 1, .zeichen "]", .zeichen ")", .zeichen "->"]
  steps := 18
  scanned := by intro rest remaining; cbv

def Chunk.outputOne : Chunk where
  characters := ['[', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', ';', ' ', '1', ']', ' ']
  tokens := [.zeichen "[", .wort "u8", .wort "in", .num 0, .zeichen "..", .num 10, .zeichen ";", .num 1, .zeichen "]"]
  steps := 15
  scanned := by intro rest remaining; cbv

def Chunk.effects : Chunk where
  characters := ['e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'p', 'u', 'r', 'e', ' ', '}', ' ', '{', ' ', 'r', 'e', 't', 'u',
    'r', 'n', ' ']
  tokens := [.wort "effects", .zeichen "{", .wort "pure", .zeichen "}", .zeichen "{", .wort "return"]
  steps := 12
  scanned := by intro rest remaining; cbv

def Chunk.plainResult : Chunk where
  characters := ['r', 'e', 'g', 'i', 'o', 'n', ';', ' ', '}', ' ']
  tokens := [.ident "region", .zeichen ";", .zeichen "}"]
  steps := 5
  scanned := by intro rest remaining; cbv

def Chunk.reverseResult : Chunk where
  characters := ['[', 'r', 'e', 'g', 'i', 'o', 'n', '[', '1', ']', ',', ' ', 'r', 'e', 'g', 'i', 'o', 'n', '[', '0', ']', ']', ';',
    ' ', '}', ' ']
  tokens := [.zeichen "[", .ident "region", .zeichen "[", .num 1, .zeichen "]", .zeichen ",", .ident "region", .zeichen "[", .num 0, .zeichen "]", .zeichen "]", .zeichen ";", .zeichen "}"]
  steps := 16
  scanned := by intro rest remaining; cbv

def Chunk.recursiveResult : Chunk where
  characters := ['b', 'u', 'i', 'l', 'd', '(', 'r', 'e', 'g', 'i', 'o', 'n', ')', ';', ' ', '}', ' ']
  tokens := [.ident "build", .zeichen "(", .ident "region", .zeichen ")", .zeichen ";", .zeichen "}"]
  steps := 8
  scanned := by intro rest remaining; cbv

def Chunk.closeSpace : Chunk where
  characters := ['}', ' ']
  tokens := [.zeichen "}"]
  steps := 2
  scanned := by intro rest remaining; cbv

def Chunk.close : Chunk where
  characters := ['}']
  tokens := [.zeichen "}"]
  steps := 1
  scanned := by intro rest remaining; cbv

def Chunk.callerHead : Chunk where
  characters := ['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'c', 'a', 'l', 'l', 'e', 'r', '(', ')', ' ', '{', ' ']
  tokens := [.wort "impl", .wort "fn", .ident "caller", .zeichen "(", .zeichen ")", .zeichen "{"]
  steps := 10
  scanned := by intro rest remaining; cbv

def Chunk.callSample : Chunk where
  characters := ['@', 's', 'a', 'm', 'p', 'l', 'e', '#', 'c', 'o', 'n', 's', 'u', 'm', 'e', '(', ')', ' ', '{', ' ']
  tokens := [.zeichen "@", .ident "sample", .zeichen "#", .ident "consume", .zeichen "(", .zeichen ")", .zeichen "{"]
  steps := 9
  scanned := by intro rest remaining; cbv

def Chunk.callA : Chunk where
  characters := ['@', 'a', '#', 'c', 'o', 'n', 's', 'u', 'm', 'e', '(', ')', ' ', '{', ' ']
  tokens := [.zeichen "@", .ident "a", .zeichen "#", .ident "consume", .zeichen "(", .zeichen ")", .zeichen "{"]
  steps := 9
  scanned := by intro rest remaining; cbv

def Chunk.valuesTwo : Chunk where
  characters := ['3', ' ', '5', ' ', '}', ';', ' ', 'r', 'e', 't', 'u', 'r', 'n', ';', ' ', '}', ' ']
  tokens := [.num 3, .num 5, .zeichen "}", .zeichen ";", .wort "return", .zeichen ";", .zeichen "}"]
  steps := 12
  scanned := by intro rest remaining; cbv

def Chunk.valuesTwoFinal : Chunk where
  characters := ['3', ' ', '5', ' ', '}', ';', ' ', 'r', 'e', 't', 'u', 'r', 'n', ';', ' ', '}']
  tokens := [.num 3, .num 5, .zeichen "}", .zeichen ";", .wort "return", .zeichen ";", .zeichen "}"]
  steps := 11
  scanned := by intro rest remaining; cbv

def Chunk.valuesOne : Chunk where
  characters := ['3', ' ', '}', ';', ' ', 'r', 'e', 't', 'u', 'r', 'n', ';', ' ', '}', ' ']
  tokens := [.num 3, .zeichen "}", .zeichen ";", .wort "return", .zeichen ";", .zeichen "}"]
  steps := 10
  scanned := by intro rest remaining; cbv

end Gabbro.Grammatik.Uebersetzung.LibraryFixtureScanning
