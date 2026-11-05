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
def fragment15 : ScanPiece [':', ' ', 'u', '8', ',', ' ', '}', ' ', '}', ' ', 'c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 's', 'e', 'l', 'e', 'c', 't', 'e', 'd', '(', 'x', ' ', ':', ' ', 'u', '8', ' '] := by
  let tokens := ((lexL [':', ' ', 'u', '8', ',', ' ', '}', ' ', '}', ' ', 'c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 's', 'e', 'l', 'e', 'c', 't', 'e', 'd', '(', 'x', ' ', ':', ' ', 'u', '8', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 9, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment16 : ScanPiece ['i', 'n', ' ', '0', ' ', '.', '.', ' ', '3', ')', ' ', '-', '>', ' ', 'o', 'p', 't', 'i', 'o', 'n', ' ', 'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' '] := by
  let tokens := ((lexL ['i', 'n', ' ', '0', ' ', '.', '.', ' ', '3', ')', ' ', '-', '>', ' ', 'o', 'p', 't', 'i', 'o', 'n', ' ', 'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 8, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment17 : ScanPiece ['S', 'l', 'o', 't', 's', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'S', 'o', 'm', 'e', '(', 'x', ')', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' '] := by
  let tokens := ((lexL ['S', 'l', 'o', 't', 's', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'S', 'o', 'm', 'e', '(', 'x', ')', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 7, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment18 : ScanPiece ['m', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'o', 'p', 't', 'i', 'o', 'n', ' ', 'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'S', 'l', 'o', 't', 's', ' '] := by
  let tokens := ((lexL ['m', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'o', 'p', 't', 'i', 'o', 'n', ' ', 'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'S', 'l', 'o', 't', 's', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 6, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment19 : ScanPiece ['{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 's', 'e', 'l', 'e', 'c', 't', 'e', 'd', '(', '2', ')', ';', ' ', '}'] := by
  let tokens := ((lexL ['{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 's', 'e', 'l', 'e', 'c', 't', 'e', 'd', '(', '2', ')', ';', ' ', '}']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 3, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment20 : ScanPiece [':', ' ', 'u', '8', ',', ' ', '}', ' ', '}', ' ', 'c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 's', 'e', 'l', 'e', 'c', 't', 'e', 'd', '(', ')', ' ', '-', '>', ' '] := by
  let tokens := ((lexL [':', ' ', 'u', '8', ',', ' ', '}', ' ', '}', ' ', 'c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 's', 'e', 'l', 'e', 'c', 't', 'e', 'd', '(', ')', ' ', '-', '>', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 8, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment21 : ScanPiece ['o', 'p', 't', 'i', 'o', 'n', ' ', 'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'S', 'l', 'o', 't', 's', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' '] := by
  let tokens := ((lexL ['o', 'p', 't', 'i', 'o', 'n', ' ', 'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'S', 'l', 'o', 't', 's', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 6, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment22 : ScanPiece ['N', 'o', 'n', 'e', '(', ')', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'o', 'p', 't', 'i', 'o', 'n', ' '] := by
  let tokens := ((lexL ['N', 'o', 'n', 'e', '(', ')', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'o', 'p', 't', 'i', 'o', 'n', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 7, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment23 : ScanPiece ['i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'S', 'l', 'o', 't', 's', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' '] := by
  let tokens := ((lexL ['i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'S', 'l', 'o', 't', 's', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 5, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment24 : ScanPiece ['s', 'e', 'l', 'e', 'c', 't', 'e', 'd', '(', ')', ';', ' ', '}'] := by
  let tokens := ((lexL ['s', 'e', 'l', 'e', 'c', 't', 'e', 'd', '(', ')', ';', ' ', '}']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 1, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment25 : ScanPiece ['t', 'a', 'g', 'g', 'e', 'd', ' ', 't', 'y', 'p', 'e', ' ', 'C', 'h', 'o', 'i', 'c', 'e', ' ', '=', ' ', '{', ' ', 'E', 'm', 'p', 't', 'y', ',', ' '] := by
  let tokens := ((lexL ['t', 'a', 'g', 'g', 'e', 'd', ' ', 't', 'y', 'p', 'e', ' ', 'C', 'h', 'o', 'i', 'c', 'e', ' ', '=', ' ', '{', ' ', 'E', 'm', 'p', 't', 'y', ',', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 6, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment26 : ScanPiece ['D', 'a', 't', 'a', '(', 'u', '8', ')', ' ', '}', ';', ' ', 'c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 's', 'e', 'l', 'e', 'c', 't', 'e', 'd', '(', 'x', ' ', ':', ' '] := by
  let tokens := ((lexL ['D', 'a', 't', 'a', '(', 'u', '8', ')', ' ', '}', ';', ' ', 'c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 's', 'e', 'l', 'e', 'c', 't', 'e', 'd', '(', 'x', ' ', ':', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 6, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment27 : ScanPiece ['u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', ')', ' ', '-', '>', ' ', 'C', 'h', 'o', 'i', 'c', 'e', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' '] := by
  let tokens := ((lexL ['u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', ')', ' ', '-', '>', ' ', 'C', 'h', 'o', 'i', 'c', 'e', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 9, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment28 : ScanPiece ['D', 'a', 't', 'a', '(', 'x', ' ', '+', ' ', '1', ')', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' '] := by
  let tokens := ((lexL ['D', 'a', 't', 'a', '(', 'x', ' ', '+', ' ', '1', ')', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 8, equation := ?_ }
  intro rest fuel
  cbv

/-- A short equation of the canonical scanner, including its exact fuel consumption. -/
def fragment29 : ScanPiece ['C', 'h', 'o', 'i', 'c', 'e', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 's', 'e', 'l', 'e', 'c', 't', 'e', 'd', '(', '4', ')', ';', ' ', '}'] := by
  let tokens := ((lexL ['C', 'h', 'o', 'i', 'c', 'e', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 's', 'e', 'l', 'e', 'c', 't', 'e', 'd', '(', '4', ')', ';', ' ', '}']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 4, equation := ?_ }
  intro rest fuel
  cbv

end Gabbro.Stage0.Frontend.ConstPhases
