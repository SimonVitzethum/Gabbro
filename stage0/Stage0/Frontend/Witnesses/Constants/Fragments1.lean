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
def fragment0 : ScanPiece ['c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 'i', 'n', 'c', 'r', 'e', 'm', 'e', 'n', 't', '(', 'x', ' ', ':', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' '] := by
  let tokens := ((lexL ['c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 'i', 'n', 'c', 'r', 'e', 'm', 'e', 'n', 't', '(', 'x', ' ', ':', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 8, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment1 : ScanPiece ['1', '0', ')', ' ', '-', '>', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '1', ' ', 'r', 'e', 'q', 'u', 'i', 'r', 'e', 's', ' ', 'x', ' ', '>', ' '] := by
  let tokens := ((lexL ['1', '0', ')', ' ', '-', '>', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '1', ' ', 'r', 'e', 'q', 'u', 'i', 'r', 'e', 's', ' ', 'x', ' ', '>', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 10, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment2 : ScanPiece ['0', ' ', 'e', 'n', 's', 'u', 'r', 'e', 's', ' ', 'r', 'e', 's', 'u', 'l', 't', ' ', '=', '=', ' ', 'x', ' ', '+', ' ', '1', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' '] := by
  let tokens := ((lexL ['0', ' ', 'e', 'n', 's', 'u', 'r', 'e', 's', ' ', 'r', 'e', 's', 'u', 'l', 't', ' ', '=', '=', ' ', 'x', ' ', '+', ' ', '1', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 9, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment3 : ScanPiece ['x', ' ', '+', ' ', '1', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '6', '4', ' ', '{', ' '] := by
  let tokens := ((lexL ['x', ' ', '+', ' ', '1', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '6', '4', ' ', '{', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 10, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment4 : ScanPiece ['r', 'e', 't', 'u', 'r', 'n', ' ', 'i', 'n', 'c', 'r', 'e', 'm', 'e', 'n', 't', '(', '3', ')', ' ', '+', ' '] := by
  let tokens := ((lexL ['r', 'e', 't', 'u', 'r', 'n', ' ', 'i', 'n', 'c', 'r', 'e', 'm', 'e', 'n', 't', '(', '3', ')', ' ', '+', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 3, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment5 : ScanPiece ['i', 'n', 'c', 'r', 'e', 'm', 'e', 'n', 't', '(', '5', ')', ';', ' ', '}'] := by
  let tokens := ((lexL ['i', 'n', 'c', 'r', 'e', 'm', 'e', 'n', 't', '(', '5', ')', ';', ' ', '}']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 1, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment6 : ScanPiece ['x', ' ', '+', ' ', '1', ';', ' ', '}', ' ', 'c', 'o', 'n', 's', 't', ' ', 'A', 'N', 'S', 'W', 'E', 'R', ' ', ':', ' ', 'u', '8', ' ', '=', ' '] := by
  let tokens := ((lexL ['x', ' ', '+', ' ', '1', ';', ' ', '}', ' ', 'c', 'o', 'n', 's', 't', ' ', 'A', 'N', 'S', 'W', 'E', 'R', ' ', ':', ' ', 'u', '8', ' ', '=', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 9, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment7 : ScanPiece ['i', 'n', 'c', 'r', 'e', 'm', 'e', 'n', 't', '(', '3', ')', ';', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '8', ' '] := by
  let tokens := ((lexL ['i', 'n', 'c', 'r', 'e', 'm', 'e', 'n', 't', '(', '3', ')', ';', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '8', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 6, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment8 : ScanPiece ['{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'A', 'N', 'S', 'W', 'E', 'R', ';', ' ', '}'] := by
  let tokens := ((lexL ['{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'A', 'N', 'S', 'W', 'E', 'R', ';', ' ', '}']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 3, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment9 : ScanPiece ['c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 'p', 'o', 's', 'i', 't', 'i', 'v', 'e', '(', 'x', ' ', ':', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' '] := by
  let tokens := ((lexL ['c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 'p', 'o', 's', 'i', 't', 'i', 'v', 'e', '(', 'x', ' ', ':', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 8, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment10 : ScanPiece ['1', '0', ')', ' ', '-', '>', ' ', 'b', 'o', 'o', 'l', ' ', 'e', 'n', 's', 'u', 'r', 'e', 's', ' ', 'r', 'e', 's', 'u', 'l', 't', ' ', '=', '=', ' ', '(', 'x', ' ', '>', ' '] := by
  let tokens := ((lexL ['1', '0', ')', ' ', '-', '>', ' ', 'b', 'o', 'o', 'l', ' ', 'e', 'n', 's', 'u', 'r', 'e', 's', ' ', 'r', 'e', 's', 'u', 'l', 't', ' ', '=', '=', ' ', '(', 'x', ' ', '>', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 8, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment11 : ScanPiece ['0', ')', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'x', ' ', '>', ' ', '0', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' '] := by
  let tokens := ((lexL ['0', ')', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'x', ' ', '>', ' ', '0', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 9, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment12 : ScanPiece ['m', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'b', 'o', 'o', 'l', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' '] := by
  let tokens := ((lexL ['m', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'b', 'o', 'o', 'l', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 5, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment13 : ScanPiece ['p', 'o', 's', 'i', 't', 'i', 'v', 'e', '(', '3', ')', ' ', '&', '&', ' ', '!', 'p', 'o', 's', 'i', 't', 'i', 'v', 'e', '(', '0', ')', ';', ' ', '}'] := by
  let tokens := ((lexL ['p', 'o', 's', 'i', 't', 'i', 'v', 'e', '(', '3', ')', ' ', '&', '&', ' ', '!', 'p', 'o', 's', 'i', 't', 'i', 'v', 'e', '(', '0', ')', ';', ' ', '}']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 3, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment14 : ScanPiece ['t', 'a', 'b', 'l', 'e', ' ', 'S', 'l', 'o', 't', 's', ' ', 'c', 'o', 'u', 'n', 't', ' ', '4', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', 'a', 'l', 'u', 'e', ' '] := by
  let tokens := ((lexL ['t', 'a', 'b', 'l', 'e', ' ', 'S', 'l', 'o', 't', 's', ' ', 'c', 'o', 'u', 'n', 't', ' ', '4', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', 'a', 'l', 'u', 'e', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 8, equation := ?_ }
  intro rest fuel
  cbv

end Gabbro.Stage0.Frontend.ConstPhases
