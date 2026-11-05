module
public import Stage0.Frontend.Witnesses.Constants.Basis
import all Grammatik.Parser.Lex.Lexer.Teil1
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
namespace Gabbro.Stage0.Frontend.ConstPhases
open Gabbro.Grammatik.Parser
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment30 : ScanPiece ['c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 's', 'e', 'l', 'e', 'c', 't', 'e', 'd', '(', ')', ' ', '-', '>', ' ', 's', 't', 'r', 'i', 'n', 'g', ' ', 'm', 'a', 'x', ' '] := by
  let tokens := ((lexL ['c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 's', 'e', 'l', 'e', 'c', 't', 'e', 'd', '(', ')', ' ', '-', '>', ' ', 's', 't', 'r', 'i', 'n', 'g', ' ', 'm', 'a', 'x', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 6, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment31 : ScanPiece ['1', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', '"', 'A', '"', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' '] := by
  let tokens := ((lexL ['1', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', '"', 'A', '"', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 8, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment32 : ScanPiece ['-', '>', ' ', 's', 't', 'r', 'i', 'n', 'g', ' ', 'm', 'a', 'x', ' ', '1', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' '] := by
  let tokens := ((lexL ['-', '>', ' ', 's', 't', 'r', 'i', 'n', 'g', ' ', 'm', 'a', 'x', ' ', '1', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 6, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment33 : ScanPiece ['c', 'o', 'n', 's', 't', ' ', 'K', ' ', ':', ' ', 'u', '8', ' ', '=', ' ', '5', ';', ' ', 'c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 'a', 'd', 'd', 'K', '(', 'x', ' '] := by
  let tokens := ((lexL ['c', 'o', 'n', 's', 't', ' ', 'K', ' ', ':', ' ', 'u', '8', ' ', '=', ' ', '5', ';', ' ', 'c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 'a', 'd', 'd', 'K', '(', 'x', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 9, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment34 : ScanPiece [':', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', ')', ' ', '-', '>', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '2', '0', ' '] := by
  let tokens := ((lexL [':', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', ')', ' ', '-', '>', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '2', '0', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 12, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment35 : ScanPiece ['{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'x', ' ', '+', ' ', 'K', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' '] := by
  let tokens := ((lexL ['{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'x', ' ', '+', ' ', 'K', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 9, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment36 : ScanPiece ['-', '>', ' ', 'u', '8', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'a', 'd', 'd', 'K', '(', 'K', ' ', '+', ' ', '1', ')', ';', ' ', '}'] := by
  let tokens := ((lexL ['-', '>', ' ', 'u', '8', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'a', 'd', 'd', 'K', '(', 'K', ' ', '+', ' ', '1', ')', ';', ' ', '}']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 7, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment37 : ScanPiece ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'C', 'o', 'n', 's', 't', 'a', 'n', 't', 's', ' ', '{', ' ', 'p', 'u', 'b', ' ', 'c', 'o', 'n', 's', 't', ' ', 'K', ' ', ':', ' '] := by
  let tokens := ((lexL ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'C', 'o', 'n', 's', 't', 'a', 'n', 't', 's', ' ', '{', ' ', 'p', 'u', 'b', ' ', 'c', 'o', 'n', 's', 't', ' ', 'K', ' ', ':', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 7, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment38 : ScanPiece ['u', '8', ' ', '=', ' ', '5', ';', ' ', '}', ' ', 'c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 'a', 'd', 'd', 'K', '(', 'x', ' ', ':', ' ', 'u', '8', ' ', 'i', 'n', ' '] := by
  let tokens := ((lexL ['u', '8', ' ', '=', ' ', '5', ';', ' ', '}', ' ', 'c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 'a', 'd', 'd', 'K', '(', 'x', ' ', ':', ' ', 'u', '8', ' ', 'i', 'n', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 10, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment39 : ScanPiece ['0', ' ', '.', '.', ' ', '1', '0', ')', ' ', '-', '>', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '2', '0', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' '] := by
  let tokens := ((lexL ['0', ' ', '.', '.', ' ', '1', '0', ')', ' ', '-', '>', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '2', '0', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 11, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment40 : ScanPiece ['x', ' ', '+', ' ', 'C', 'o', 'n', 's', 't', 'a', 'n', 't', 's', ':', ':', 'K', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' '] := by
  let tokens := ((lexL ['x', ' ', '+', ' ', 'C', 'o', 'n', 's', 't', 'a', 'n', 't', 's', ':', ':', 'K', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 7, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment41 : ScanPiece ['-', '>', ' ', 'u', '8', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'a', 'd', 'd', 'K', '(', 'C', 'o', 'n', 's', 't', 'a', 'n', 't', 's', ':', ':', 'K', ' ', '+', ' '] := by
  let tokens := ((lexL ['-', '>', ' ', 'u', '8', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'a', 'd', 'd', 'K', '(', 'C', 'o', 'n', 's', 't', 'a', 'n', 't', 's', ':', ':', 'K', ' ', '+', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 6, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment42 : ScanPiece ['1', ')', ';', ' ', '}'] := by
  let tokens := ((lexL ['1', ')', ';', ' ', '}']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 1, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment43 : ScanPiece ['c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 's', 'e', 'l', 'e', 'c', 't', 'e', 'd', '(', ')', ' ', '-', '>', ' ', 'b', 'o', 'o', 'l', ' ', '{', ' ', 'l', 'e', 't', ' '] := by
  let tokens := ((lexL ['c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 's', 'e', 'l', 'e', 'c', 't', 'e', 'd', '(', ')', ' ', '-', '>', ' ', 'b', 'o', 'o', 'l', ' ', '{', ' ', 'l', 'e', 't', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 7, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment44 : ScanPiece ['x', ' ', '=', ' ', 't', 'r', 'u', 'e', ';', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'x', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' '] := by
  let tokens := ((lexL ['x', ' ', '=', ' ', 't', 'r', 'u', 'e', ';', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'x', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 8, equation := ?_ }
  intro rest fuel
  cbv

end Gabbro.Stage0.Frontend.ConstPhases
