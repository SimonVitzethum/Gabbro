module

public import Grammatik.Parser.Stmt.LibraryFixtureScanning
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

namespace Gabbro.Grammatik.Parser.InvariantText
open Gabbro.Grammatik.Uebersetzung.LibraryFixtureScanning

-- Each equation checks only a short cut of the unchanged invariant sources.
-- Its suffix and remaining fuel stay symbolic; the general lexer law composes it.

def moduleM : Chunk where
  characters :=
    ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ']
  tokens :=
    [.wort "module", .ident "m", .zeichen "{"]
  steps := 6
  scanned := by intro rest remaining; cbv

def tableT : Chunk where
  characters :=
    ['t', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u', 'n', 't', ' ', '2', ' ', '{', ' ']
  tokens :=
    [.wort "table", .ident "T", .wort "count", .num 2, .zeichen "{"]
  steps := 10
  scanned := by intro rest remaining; cbv

def sharedTableT : Chunk where
  characters :=
    ['t', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u', 'n', 't', ' ', '2', ' ', 's', 'h', 'a', 'r', 'e',
     'd', ' ', '{', ' ']
  tokens :=
    [.wort "table", .ident "T", .wort "count", .num 2, .wort "shared", .zeichen "{"]
  steps := 12
  scanned := by intro rest remaining; cbv

def tableU : Chunk where
  characters :=
    ['t', 'a', 'b', 'l', 'e', ' ', 'U', ' ', 'c', 'o', 'u', 'n', 't', ' ', '2', ' ', '{', ' ']
  tokens :=
    [.wort "table", .ident "U", .wort "count", .num 2, .zeichen "{"]
  steps := 10
  scanned := by intro rest remaining; cbv

def slotV : Chunk where
  characters :=
    ['s', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '3', '2', ',', ' ', '}', ' ']
  tokens :=
    [.wort "slot", .zeichen "{", .ident "v", .zeichen ":", .wort "u32", .zeichen ",", .zeichen "}"]
  steps := 13
  scanned := by intro rest remaining; cbv

def slotW : Chunk where
  characters :=
    ['s', 'l', 'o', 't', ' ', '{', ' ', 'w', ' ', ':', ' ', 'u', '3', '2', ',', ' ', '}', ' ']
  tokens :=
    [.wort "slot", .zeichen "{", .wort "w", .zeichen ":", .wort "u32", .zeichen ",", .zeichen "}"]
  steps := 13
  scanned := by intro rest remaining; cbv

def invariantI : Chunk where
  characters :=
    ['i', 'n', 'v', 'a', 'r', 'i', 'a', 'n', 't', ' ', 'I', ' ', ':', ' ']
  tokens :=
    [.wort "invariant", .ident "I", .zeichen ":"]
  steps := 6
  scanned := by intro rest remaining; cbv

def forallT : Chunk where
  characters :=
    ['f', 'o', 'r', 'a', 'l', 'l', ' ', 'k', ' ', 'i', 'n', ' ', 's', 'l', 'o', 't', 's', ' ', 'o', 'f', ' ',
     'T', ' ', ':', ' ']
  tokens :=
    [.wort "forall", .ident "k", .wort "in", .wort "slots", .wort "of", .ident "T", .zeichen ":"]
  steps := 14
  scanned := by intro rest remaining; cbv

def indexedLess : Chunk where
  characters :=
    ['T', '.', 's', 'l', 'o', 't', 's', '[', 'k', ']', '.', 'v', ' ', '<', ' ', '9', ';', ' ']
  tokens :=
    [.ident "T", .zeichen ".", .wort "slots", .zeichen "[", .ident "k", .zeichen "]", .zeichen ".",
     .ident "v", .zeichen "<", .num 9, .zeichen ";"]
  steps := 14
  scanned := by intro rest remaining; cbv

def firstLess : Chunk where
  characters :=
    ['T', '.', 's', 'l', 'o', 't', 's', '[', '0', ']', '.', 'v', ' ', '<', ' ', '9', ';', ' ']
  tokens :=
    [.ident "T", .zeichen ".", .wort "slots", .zeichen "[", .num 0, .zeichen "]", .zeichen ".", .ident "v",
     .zeichen "<", .num 9, .zeichen ";"]
  steps := 14
  scanned := by intro rest remaining; cbv

def truePredicate : Chunk where
  characters :=
    ['t', 'r', 'u', 'e', ';', ' ']
  tokens :=
    [.wort "true", .zeichen ";"]
  steps := 3
  scanned := by intro rest remaining; cbv

def lockT : Chunk where
  characters :=
    ['l', 'o', 'c', 'k', ' ', 'L', ' ', 'p', 'r', 'o', 't', 'e', 'c', 't', 's', ' ', '{', ' ', 'T', ' ', '}',
     ' ', 'r', 'a', 'n', 'k', ' ', '0', ';', ' ']
  tokens :=
    [.wort "lock", .ident "L", .wort "protects", .zeichen "{", .ident "T", .zeichen "}", .wort "rank",
     .num 0, .zeichen ";"]
  steps := 17
  scanned := by intro rest remaining; cbv

def indexFunction : Chunk where
  characters :=
    ['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'f', '(', 'i', ' ', ':', ' ', 'i', 'n', 'd', 'e', 'x', ' ', 'i',
     'n', 't', 'o', ' ', 'T', ')', ' ']
  tokens :=
    [.wort "impl", .wort "fn", .ident "f", .zeichen "(", .ident "i", .zeichen ":", .wort "index",
     .wort "into", .ident "T", .zeichen ")"]
  steps := 17
  scanned := by intro rest remaining; cbv

def heldL : Chunk where
  characters :=
    ['r', 'e', 'q', 'u', 'i', 'r', 'e', 's', ' ', 'H', 'e', 'l', 'd', '(', 'L', ')', ' ']
  tokens :=
    [.wort "requires", .ident "Held", .zeichen "(", .ident "L", .zeichen ")"]
  steps := 7
  scanned := by intro rest remaining; cbv

def writesT : Chunk where
  characters :=
    ['e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'w', 'r', 'i', 't', 'e', 's', ' ', 'T', '.', 's', 'l',
     'o', 't', 's', ' ', '}', ' ']
  tokens :=
    [.wort "effects", .zeichen "{", .wort "writes", .ident "T", .zeichen ".", .wort "slots", .zeichen "}"]
  steps := 12
  scanned := by intro rest remaining; cbv

def writeT : Chunk where
  characters :=
    ['{', ' ', 'T', '.', 's', 'l', 'o', 't', 's', '[', 'i', ']', '.', 'v', ' ', '=', ' ', '1', ';', ' ', '}',
     ' ']
  tokens :=
    [.zeichen "{", .ident "T", .zeichen ".", .wort "slots", .zeichen "[", .ident "i", .zeichen "]",
     .zeichen ".", .ident "v", .zeichen "=", .num 1, .zeichen ";", .zeichen "}"]
  steps := 18
  scanned := by intro rest remaining; cbv

def locksT : Chunk where
  characters :=
    ['e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'w', 'r', 'i', 't', 'e', 's', ' ', 'T', '.', 's', 'l',
     'o', 't', 's', ',', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '}', ' ']
  tokens :=
    [.wort "effects", .zeichen "{", .wort "writes", .ident "T", .zeichen ".", .wort "slots", .zeichen ",",
     .wort "locks", .ident "L", .zeichen "}"]
  steps := 17
  scanned := by intro rest remaining; cbv

def lockedWriteT : Chunk where
  characters :=
    ['{', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '{', ' ', 'T', '.', 's', 'l', 'o', 't', 's', '[', 'i',
     ']', '.', 'v', ' ', '=', ' ', '1', ';', ' ', '}', ' ', '}', ' ']
  tokens :=
    [.zeichen "{", .wort "locks", .ident "L", .zeichen "{", .ident "T", .zeichen ".", .wort "slots",
     .zeichen "[", .ident "i", .zeichen "]", .zeichen ".", .ident "v", .zeichen "=", .num 1, .zeichen ";",
     .zeichen "}", .zeichen "}"]
  steps := 26
  scanned := by intro rest remaining; cbv

def groupTU : Chunk where
  characters :=
    ['g', 'r', 'o', 'u', 'p', ' ', 'G', ' ', 'o', 'v', 'e', 'r', ' ', '{', ' ', 'T', ',', ' ', 'U', ' ', '}',
     ' ', '{', ' ']
  tokens :=
    [.wort "group", .ident "G", .wort "over", .zeichen "{", .ident "T", .zeichen ",", .ident "U",
     .zeichen "}", .zeichen "{"]
  steps := 17
  scanned := by intro rest remaining; cbv

def compareT : Chunk where
  characters :=
    ['i', 'n', 'v', 'a', 'r', 'i', 'a', 'n', 't', ' ', 'J', ' ', ':', ' ', 'T', '.', 's', 'l', 'o', 't', 's',
     '[', '0', ']', '.', 'v', ' ', '<', '=', ' ']
  tokens :=
    [.wort "invariant", .ident "J", .zeichen ":", .ident "T", .zeichen ".", .wort "slots", .zeichen "[",
     .num 0, .zeichen "]", .zeichen ".", .ident "v", .zeichen "<="]
  steps := 17
  scanned := by intro rest remaining; cbv

def firstU : Chunk where
  characters :=
    ['U', '.', 's', 'l', 'o', 't', 's', '[', '0', ']', '.', 'w', ';', ' ']
  tokens :=
    [.ident "U", .zeichen ".", .wort "slots", .zeichen "[", .num 0, .zeichen "]", .zeichen ".", .wort "w",
     .zeichen ";"]
  steps := 10
  scanned := by intro rest remaining; cbv

def emptyFunction : Chunk where
  characters :=
    ['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'f', '(', ')', ' ', '{', ' ', '}', ' ']
  tokens :=
    [.wort "impl", .wort "fn", .ident "f", .zeichen "(", .zeichen ")", .zeichen "{", .zeichen "}"]
  steps := 12
  scanned := by intro rest remaining; cbv

def breakingFunction : Chunk where
  characters :=
    ['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'f', '(', ')', ' ', '{', ' ', 'b', 'r', 'e', 'a', 'k', 'i', 'n',
     'g', ' ', 'I', ' ', '{', ' ', '}', ' ', '}', ' ']
  tokens :=
    [.wort "impl", .wort "fn", .ident "f", .zeichen "(", .zeichen ")", .zeichen "{", .wort "breaking",
     .ident "I", .zeichen "{", .zeichen "}", .zeichen "}"]
  steps := 20
  scanned := by intro rest remaining; cbv

def staticA : Chunk where
  characters :=
    ['s', 't', 'a', 't', 'i', 'c', ' ', 'm', 'u', 't', ' ', 'A', ' ', ':', ' ', 'u', '3', '2', ' ', '=', ' ',
     '0', ' ', 's', 'h', 'a', 'r', 'e', 'd', ';', ' ']
  tokens :=
    [.wort "static", .wort "mut", .ident "A", .zeichen ":", .wort "u32", .zeichen "=", .num 0,
     .wort "shared", .zeichen ";"]
  steps := 17
  scanned := by intro rest remaining; cbv

def staticB : Chunk where
  characters :=
    ['s', 't', 'a', 't', 'i', 'c', ' ', 'm', 'u', 't', ' ', 'B', ' ', ':', ' ', 'u', '3', '2', ' ', '=', ' ',
     '0', ' ', 's', 'h', 'a', 'r', 'e', 'd', ';', ' ']
  tokens :=
    [.wort "static", .wort "mut", .ident "B", .zeichen ":", .wort "u32", .zeichen "=", .num 0,
     .wort "shared", .zeichen ";"]
  steps := 17
  scanned := by intro rest remaining; cbv

def staticN : Chunk where
  characters :=
    ['s', 't', 'a', 't', 'i', 'c', ' ', 'm', 'u', 't', ' ', 'N', ' ', ':', ' ', 'u', '3', '2', ' ', '=', ' ',
     '0', ' ', 's', 'h', 'a', 'r', 'e', 'd', ';', ' ']
  tokens :=
    [.wort "static", .wort "mut", .ident "N", .zeichen ":", .wort "u32", .zeichen "=", .num 0,
     .wort "shared", .zeichen ";"]
  steps := 17
  scanned := by intro rest remaining; cbv

def lockAB : Chunk where
  characters :=
    ['l', 'o', 'c', 'k', ' ', 'L', ' ', 'p', 'r', 'o', 't', 'e', 'c', 't', 's', ' ', '{', ' ', 'A', ',', ' ',
     'B', ' ', '}', ' ', 'r', 'a', 'n', 'k', ' ', '0', ';', ' ']
  tokens :=
    [.wort "lock", .ident "L", .wort "protects", .zeichen "{", .ident "A", .zeichen ",", .ident "B",
     .zeichen "}", .wort "rank", .num 0, .zeichen ";"]
  steps := 20
  scanned := by intro rest remaining; cbv

def groupAB : Chunk where
  characters :=
    ['g', 'r', 'o', 'u', 'p', ' ', 'G', ' ', 'o', 'v', 'e', 'r', ' ', '{', ' ', 'A', ',', ' ', 'B', ' ', '}',
     ' ', '{', ' ']
  tokens :=
    [.wort "group", .ident "G", .wort "over", .zeichen "{", .ident "A", .zeichen ",", .ident "B",
     .zeichen "}", .zeichen "{"]
  steps := 17
  scanned := by intro rest remaining; cbv

def compareAB : Chunk where
  characters :=
    ['i', 'n', 'v', 'a', 'r', 'i', 'a', 'n', 't', ' ', 'J', ' ', ':', ' ', 'A', ' ', '<', '=', ' ', 'B', ';',
     ' ']
  tokens :=
    [.wort "invariant", .ident "J", .zeichen ":", .ident "A", .zeichen "<=", .ident "B", .zeichen ";"]
  steps := 13
  scanned := by intro rest remaining; cbv

def plainFunction : Chunk where
  characters :=
    ['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'f', '(', ')', ' ']
  tokens :=
    [.wort "impl", .wort "fn", .ident "f", .zeichen "(", .zeichen ")"]
  steps := 8
  scanned := by intro rest remaining; cbv

def writesA : Chunk where
  characters :=
    ['e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'w', 'r', 'i', 't', 'e', 's', ' ', 'A', ' ', '}', ' ']
  tokens :=
    [.wort "effects", .zeichen "{", .wort "writes", .ident "A", .zeichen "}"]
  steps := 10
  scanned := by intro rest remaining; cbv

def writeA : Chunk where
  characters :=
    ['{', ' ', 'A', ' ', '=', ' ', '1', ';', ' ', '}', ' ']
  tokens :=
    [.zeichen "{", .ident "A", .zeichen "=", .num 1, .zeichen ";", .zeichen "}"]
  steps := 11
  scanned := by intro rest remaining; cbv

def lockTN : Chunk where
  characters :=
    ['l', 'o', 'c', 'k', ' ', 'L', ' ', 'p', 'r', 'o', 't', 'e', 'c', 't', 's', ' ', '{', ' ', 'T', ',', ' ',
     'N', ' ', '}', ' ', 'r', 'a', 'n', 'k', ' ', '0', ';', ' ']
  tokens :=
    [.wort "lock", .ident "L", .wort "protects", .zeichen "{", .ident "T", .zeichen ",", .ident "N",
     .zeichen "}", .wort "rank", .num 0, .zeichen ";"]
  steps := 20
  scanned := by intro rest remaining; cbv

def groupTN : Chunk where
  characters :=
    ['g', 'r', 'o', 'u', 'p', ' ', 'G', ' ', 'o', 'v', 'e', 'r', ' ', '{', ' ', 'T', ',', ' ', 'N', ' ', '}',
     ' ', '{', ' ']
  tokens :=
    [.wort "group", .ident "G", .wort "over", .zeichen "{", .ident "T", .zeichen ",", .ident "N",
     .zeichen "}", .zeichen "{"]
  steps := 17
  scanned := by intro rest remaining; cbv

def readN : Chunk where
  characters :=
    ['N', ';', ' ']
  tokens :=
    [.ident "N", .zeichen ";"]
  steps := 3
  scanned := by intro rest remaining; cbv

def writesN : Chunk where
  characters :=
    ['e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'w', 'r', 'i', 't', 'e', 's', ' ', 'N', ' ', '}', ' ']
  tokens :=
    [.wort "effects", .zeichen "{", .wort "writes", .ident "N", .zeichen "}"]
  steps := 10
  scanned := by intro rest remaining; cbv

def writeN : Chunk where
  characters :=
    ['{', ' ', 'N', ' ', '=', ' ', '1', ';', ' ', '}', ' ']
  tokens :=
    [.zeichen "{", .ident "N", .zeichen "=", .num 1, .zeichen ";", .zeichen "}"]
  steps := 11
  scanned := by intro rest remaining; cbv

def locksA : Chunk where
  characters :=
    ['e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'w', 'r', 'i', 't', 'e', 's', ' ', 'A', ',', ' ', 'l',
     'o', 'c', 'k', 's', ' ', 'L', ' ', '}', ' ']
  tokens :=
    [.wort "effects", .zeichen "{", .wort "writes", .ident "A", .zeichen ",", .wort "locks", .ident "L",
     .zeichen "}"]
  steps := 15
  scanned := by intro rest remaining; cbv

def lockedWriteA : Chunk where
  characters :=
    ['{', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '{', ' ', 'A', ' ', '=', ' ', '1', ';', ' ', '}', ' ',
     '}', ' ']
  tokens :=
    [.zeichen "{", .wort "locks", .ident "L", .zeichen "{", .ident "A", .zeichen "=", .num 1, .zeichen ";",
     .zeichen "}", .zeichen "}"]
  steps := 19
  scanned := by intro rest remaining; cbv

def groupT : Chunk where
  characters :=
    ['g', 'r', 'o', 'u', 'p', ' ', 'G', ' ', 'o', 'v', 'e', 'r', ' ', '{', ' ', 'T', ' ', '}', ' ', '{', ' ']
  tokens :=
    [.wort "group", .ident "G", .wort "over", .zeichen "{", .ident "T", .zeichen "}", .zeichen "{"]
  steps := 14
  scanned := by intro rest remaining; cbv

def lockA : Chunk where
  characters :=
    ['l', 'o', 'c', 'k', ' ', 'L', ' ', 'p', 'r', 'o', 't', 'e', 'c', 't', 's', ' ', '{', ' ', 'A', ' ', '}',
     ' ', 'r', 'a', 'n', 'k', ' ', '0', ';', ' ']
  tokens :=
    [.wort "lock", .ident "L", .wort "protects", .zeichen "{", .ident "A", .zeichen "}", .wort "rank",
     .num 0, .zeichen ";"]
  steps := 17
  scanned := by intro rest remaining; cbv

def groupAZ : Chunk where
  characters :=
    ['g', 'r', 'o', 'u', 'p', ' ', 'G', ' ', 'o', 'v', 'e', 'r', ' ', '{', ' ', 'A', ',', ' ', 'Z', ' ', '}',
     ' ', '{', ' ']
  tokens :=
    [.wort "group", .ident "G", .wort "over", .zeichen "{", .ident "A", .zeichen ",", .ident "Z",
     .zeichen "}", .zeichen "{"]
  steps := 17
  scanned := by intro rest remaining; cbv

def compareA : Chunk where
  characters :=
    ['i', 'n', 'v', 'a', 'r', 'i', 'a', 'n', 't', ' ', 'J', ' ', ':', ' ', 'A', ' ', '<', '=', ' ', '9', ';',
     ' ']
  tokens :=
    [.wort "invariant", .ident "J", .zeichen ":", .ident "A", .zeichen "<=", .num 9, .zeichen ";"]
  steps := 13
  scanned := by intro rest remaining; cbv

/-- The standard character-count fuel covers every certified cut. -/
theorem lexed (chunks : List Chunk)
    (room : chunks.all (fun chunk => decide (chunk.steps ≤ chunk.characters.length)) = true) :
    lexL (characters chunks) = .ok (tokens chunks) :=
  lex_chunks chunks (Nat.le_trans (steps_le_length chunks room) (Nat.le_succ _))

end Gabbro.Grammatik.Parser.InvariantText
