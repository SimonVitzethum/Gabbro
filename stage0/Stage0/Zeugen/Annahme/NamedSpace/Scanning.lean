module
public import Stage0.SourceWitness.Owners
import all Stage0.SourceWitness.Owners
import all Grammatik.Parser.Lex.Lexer.Teil1
import Init.Data.String.Lemmas.Intercalate

@[expose] public section
namespace Gabbro.Stage0.NamedSpaceWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Frontend.ConstPhases
set_option maxRecDepth 2000
set_option maxHeartbeats 400000

-- Space binding is nominal; neither source manufactures an owner mark.
def text : String :=
  "module named_space_probe { table T count 2 space sharedData { slot { v : u32 in 0 .. 100, } } impl fn main() -> u32 in 0 .. 100 effects { reads T.slots } { return T.slots[0].v; } }"

def pointerText : String :=
  "module named_space_pointer_probe { table T count 2 space sharedData { slot { v : u32 in 0 .. 100, } } impl fn main(p : ptr<sharedData, r> T) -> u32 in 0 .. 100 effects { reads p.slots } { return p.slots[0].v; } }"

namespace Phases

def sourceText : Bool → String | false => text | true => pointerText

-- The token data is inferred from this exact scanner success, before any
-- suffix theorem or ScanPiece constructor is introduced.
def plainHeadOutput : { actual : List Token // lexL ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'n', 'a', 'm', 'e', 'd', '_', 's', 'p', 'a', 'c', 'e', '_', 'p', 'r', 'o', 'b', 'e', ' ', '{', ' '] = .ok actual } := by
  refine ⟨?actual, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

def plainHeadTokens : List Token := plainHeadOutput.val.dropLast

private theorem plainHeadEquation (rest : List Char) (fuel : Nat) :
    scan false (['m', 'o', 'd', 'u', 'l', 'e', ' ', 'n', 'a', 'm', 'e', 'd', '_', 's', 'p', 'a', 'c', 'e', '_', 'p', 'r', 'o', 'b', 'e', ' ', '{', ' '] ++ rest) (fuel + (plainHeadTokens.length + 3)) =
      plainHeadTokens.foldr (fun token answer => Except.map (token :: ·) answer)
        (scan false rest fuel) := by cbv

def plainHead : ScanPiece ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'n', 'a', 'm', 'e', 'd', '_', 's', 'p', 'a', 'c', 'e', '_', 'p', 'r', 'o', 'b', 'e', ' ', '{', ' '] where
  tokens := plainHeadTokens
  steps := plainHeadTokens.length + 3
  equation := by exact plainHeadEquation

-- The token data is inferred from this exact scanner success, before any
-- suffix theorem or ScanPiece constructor is introduced.
def pointerHeadOutput : { actual : List Token // lexL ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'n', 'a', 'm', 'e', 'd', '_', 's', 'p', 'a', 'c', 'e', '_', 'p', 'o', 'i', 'n', 't', 'e', 'r', '_', 'p', 'r', 'o', 'b', 'e', ' ', '{', ' '] = .ok actual } := by
  refine ⟨?actual, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

def pointerHeadTokens : List Token := pointerHeadOutput.val.dropLast

private theorem pointerHeadEquation (rest : List Char) (fuel : Nat) :
    scan false (['m', 'o', 'd', 'u', 'l', 'e', ' ', 'n', 'a', 'm', 'e', 'd', '_', 's', 'p', 'a', 'c', 'e', '_', 'p', 'o', 'i', 'n', 't', 'e', 'r', '_', 'p', 'r', 'o', 'b', 'e', ' ', '{', ' '] ++ rest) (fuel + (pointerHeadTokens.length + 3)) =
      pointerHeadTokens.foldr (fun token answer => Except.map (token :: ·) answer)
        (scan false rest fuel) := by cbv

def pointerHead : ScanPiece ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'n', 'a', 'm', 'e', 'd', '_', 's', 'p', 'a', 'c', 'e', '_', 'p', 'o', 'i', 'n', 't', 'e', 'r', '_', 'p', 'r', 'o', 'b', 'e', ' ', '{', ' '] where
  tokens := pointerHeadTokens
  steps := pointerHeadTokens.length + 3
  equation := by exact pointerHeadEquation

-- The token data is inferred from this exact scanner success, before any
-- suffix theorem or ScanPiece constructor is introduced.
def tableOutput : { actual : List Token // lexL ['t', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u', 'n', 't', ' ', '2', ' ', 's', 'p', 'a', 'c', 'e', ' ', 's', 'h', 'a', 'r', 'e', 'd', 'D', 'a', 't', 'a', ' ', '{', ' '] = .ok actual } := by
  refine ⟨?actual, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

def tableTokens : List Token := tableOutput.val.dropLast

private theorem tableEquation (rest : List Char) (fuel : Nat) :
    scan false (['t', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u', 'n', 't', ' ', '2', ' ', 's', 'p', 'a', 'c', 'e', ' ', 's', 'h', 'a', 'r', 'e', 'd', 'D', 'a', 't', 'a', ' ', '{', ' '] ++ rest) (fuel + (tableTokens.length + 7)) =
      tableTokens.foldr (fun token answer => Except.map (token :: ·) answer)
        (scan false rest fuel) := by cbv

def table : ScanPiece ['t', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u', 'n', 't', ' ', '2', ' ', 's', 'p', 'a', 'c', 'e', ' ', 's', 'h', 'a', 'r', 'e', 'd', 'D', 'a', 't', 'a', ' ', '{', ' '] where
  tokens := tableTokens
  steps := tableTokens.length + 7
  equation := by exact tableEquation

-- The token data is inferred from this exact scanner success, before any
-- suffix theorem or ScanPiece constructor is introduced.
def fieldOutput : { actual : List Token // lexL ['s', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', '0', ',', ' ', '}', ' ', '}', ' '] = .ok actual } := by
  refine ⟨?actual, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

def fieldTokens : List Token := fieldOutput.val.dropLast

private theorem fieldEquation (rest : List Char) (fuel : Nat) :
    scan false (['s', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', '0', ',', ' ', '}', ' ', '}', ' '] ++ rest) (fuel + (fieldTokens.length + 11)) =
      fieldTokens.foldr (fun token answer => Except.map (token :: ·) answer)
        (scan false rest fuel) := by cbv

def field : ScanPiece ['s', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', '0', ',', ' ', '}', ' ', '}', ' '] where
  tokens := fieldTokens
  steps := fieldTokens.length + 11
  equation := by exact fieldEquation

-- The token data is inferred from this exact scanner success, before any
-- suffix theorem or ScanPiece constructor is introduced.
def plainMainOutput : { actual : List Token // lexL ['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', '0', ' '] = .ok actual } := by
  refine ⟨?actual, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

def plainMainTokens : List Token := plainMainOutput.val.dropLast

private theorem plainMainEquation (rest : List Char) (fuel : Nat) :
    scan false (['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', '0', ' '] ++ rest) (fuel + (plainMainTokens.length + 9)) =
      plainMainTokens.foldr (fun token answer => Except.map (token :: ·) answer)
        (scan false rest fuel) := by cbv

def plainMain : ScanPiece ['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', '0', ' '] where
  tokens := plainMainTokens
  steps := plainMainTokens.length + 9
  equation := by exact plainMainEquation

-- The token data is inferred from this exact scanner success, before any
-- suffix theorem or ScanPiece constructor is introduced.
def plainReadOutput : { actual : List Token // lexL ['e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'r', 'e', 'a', 'd', 's', ' ', 'T', '.', 's', 'l', 'o', 't', 's', ' ', '}', ' '] = .ok actual } := by
  refine ⟨?actual, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

def plainReadTokens : List Token := plainReadOutput.val.dropLast

private theorem plainReadEquation (rest : List Char) (fuel : Nat) :
    scan false (['e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'r', 'e', 'a', 'd', 's', ' ', 'T', '.', 's', 'l', 'o', 't', 's', ' ', '}', ' '] ++ rest) (fuel + (plainReadTokens.length + 5)) =
      plainReadTokens.foldr (fun token answer => Except.map (token :: ·) answer)
        (scan false rest fuel) := by cbv

def plainRead : ScanPiece ['e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'r', 'e', 'a', 'd', 's', ' ', 'T', '.', 's', 'l', 'o', 't', 's', ' ', '}', ' '] where
  tokens := plainReadTokens
  steps := plainReadTokens.length + 5
  equation := by exact plainReadEquation

-- The token data is inferred from this exact scanner success, before any
-- suffix theorem or ScanPiece constructor is introduced.
def pointerReadOutput : { actual : List Token // lexL ['e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'r', 'e', 'a', 'd', 's', ' ', 'p', '.', 's', 'l', 'o', 't', 's', ' ', '}', ' '] = .ok actual } := by
  refine ⟨?actual, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

def pointerReadTokens : List Token := pointerReadOutput.val.dropLast

private theorem pointerReadEquation (rest : List Char) (fuel : Nat) :
    scan false (['e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'r', 'e', 'a', 'd', 's', ' ', 'p', '.', 's', 'l', 'o', 't', 's', ' ', '}', ' '] ++ rest) (fuel + (pointerReadTokens.length + 5)) =
      pointerReadTokens.foldr (fun token answer => Except.map (token :: ·) answer)
        (scan false rest fuel) := by cbv

def pointerRead : ScanPiece ['e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'r', 'e', 'a', 'd', 's', ' ', 'p', '.', 's', 'l', 'o', 't', 's', ' ', '}', ' '] where
  tokens := pointerReadTokens
  steps := pointerReadTokens.length + 5
  equation := by exact pointerReadEquation

-- The token data is inferred from this exact scanner success, before any
-- suffix theorem or ScanPiece constructor is introduced.
def plainReturnOutput : { actual : List Token // lexL ['{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'T', '.', 's', 'l', 'o', 't', 's', '[', '0', ']', '.', 'v', ';', ' ', '}', ' ', '}'] = .ok actual } := by
  refine ⟨?actual, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

def plainReturnTokens : List Token := plainReturnOutput.val.dropLast

private theorem plainReturnEquation (rest : List Char) (fuel : Nat) :
    scan false (['{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'T', '.', 's', 'l', 'o', 't', 's', '[', '0', ']', '.', 'v', ';', ' ', '}', ' ', '}'] ++ rest) (fuel + (plainReturnTokens.length + 4)) =
      plainReturnTokens.foldr (fun token answer => Except.map (token :: ·) answer)
        (scan false rest fuel) := by cbv

def plainReturn : ScanPiece ['{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'T', '.', 's', 'l', 'o', 't', 's', '[', '0', ']', '.', 'v', ';', ' ', '}', ' ', '}'] where
  tokens := plainReturnTokens
  steps := plainReturnTokens.length + 4
  equation := by exact plainReturnEquation

-- The token data is inferred from this exact scanner success, before any
-- suffix theorem or ScanPiece constructor is introduced.
def pointerReturnOutput : { actual : List Token // lexL ['{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'p', '.', 's', 'l', 'o', 't', 's', '[', '0', ']', '.', 'v', ';', ' ', '}', ' ', '}'] = .ok actual } := by
  refine ⟨?actual, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

def pointerReturnTokens : List Token := pointerReturnOutput.val.dropLast

private theorem pointerReturnEquation (rest : List Char) (fuel : Nat) :
    scan false (['{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'p', '.', 's', 'l', 'o', 't', 's', '[', '0', ']', '.', 'v', ';', ' ', '}', ' ', '}'] ++ rest) (fuel + (pointerReturnTokens.length + 4)) =
      pointerReturnTokens.foldr (fun token answer => Except.map (token :: ·) answer)
        (scan false rest fuel) := by cbv

def pointerReturn : ScanPiece ['{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'p', '.', 's', 'l', 'o', 't', 's', '[', '0', ']', '.', 'v', ';', ' ', '}', ' ', '}'] where
  tokens := pointerReturnTokens
  steps := pointerReturnTokens.length + 4
  equation := by exact pointerReturnEquation

-- The token data is inferred from this exact scanner success, before any
-- suffix theorem or ScanPiece constructor is introduced.
def pointerParamsOutput : { actual : List Token // lexL ['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', 'p', ' ', ':', ' ', 'p', 't', 'r', '<', 's', 'h', 'a', 'r', 'e', 'd', 'D', 'a', 't', 'a', ',', ' ', 'r', '>', ' ', 'T', ')', ' '] = .ok actual } := by
  refine ⟨?actual, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

def pointerParamsTokens : List Token := pointerParamsOutput.val.dropLast

private theorem pointerParamsEquation (rest : List Char) (fuel : Nat) :
    scan false (['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', 'p', ' ', ':', ' ', 'p', 't', 'r', '<', 's', 'h', 'a', 'r', 'e', 'd', 'D', 'a', 't', 'a', ',', ' ', 'r', '>', ' ', 'T', ')', ' '] ++ rest) (fuel + (pointerParamsTokens.length + 7)) =
      pointerParamsTokens.foldr (fun token answer => Except.map (token :: ·) answer)
        (scan false rest fuel) := by cbv

def pointerParams : ScanPiece ['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', 'p', ' ', ':', ' ', 'p', 't', 'r', '<', 's', 'h', 'a', 'r', 'e', 'd', 'D', 'a', 't', 'a', ',', ' ', 'r', '>', ' ', 'T', ')', ' '] where
  tokens := pointerParamsTokens
  steps := pointerParamsTokens.length + 7
  equation := by exact pointerParamsEquation

-- The token data is inferred from this exact scanner success, before any
-- suffix theorem or ScanPiece constructor is introduced.
def pointerResultOutput : { actual : List Token // lexL ['-', '>', ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', '0', ' '] = .ok actual } := by
  refine ⟨?actual, ?produced⟩
  case produced => cbv <;> exact Eq.refl _

def pointerResultTokens : List Token := pointerResultOutput.val.dropLast

private theorem pointerResultEquation (rest : List Char) (fuel : Nat) :
    scan false (['-', '>', ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', '0', ' '] ++ rest) (fuel + (pointerResultTokens.length + 6)) =
      pointerResultTokens.foldr (fun token answer => Except.map (token :: ·) answer)
        (scan false rest fuel) := by cbv

def pointerResult : ScanPiece ['-', '>', ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', '0', ' '] where
  tokens := pointerResultTokens
  steps := pointerResultTokens.length + 6
  equation := by exact pointerResultEquation

-- Every token comes from a short real scanner application, with a symbolic
-- suffix and fuel. Only composition is used for the original complete text.
def sourceChunks : Bool → Σ characters : List Char, ScanPiece characters
  | false => ⟨_, ((plainHead.append table).append field).append
      ((plainMain.append plainRead).append plainReturn)⟩
  | true => ⟨_, ((pointerHead.append table).append field).append
      (((pointerParams.append pointerResult).append pointerRead).append pointerReturn)⟩

def characters (pointer : Bool) : List Char := (sourceChunks pointer).1

def scanned (pointer : Bool) : ScanPiece (characters pointer) := (sourceChunks pointer).2

private theorem source_spelling (pointer : Bool) :
    sourceText pointer = String.ofList (characters pointer) := by
  cases pointer <;> decide +kernel

-- Normalize the composed token list once, before a parser or SourceInput can
-- project it. This data equality composes the existing cuts, not another lexer.
def wholeTokens : (pointer : Bool) →
    { actual : List Token // (scanned pointer).tokens ++ [.ende] = actual }
  | false => by
    refine ⟨?plainResult, ?plainResultEq⟩
    case plainResultEq => cbv <;> exact Eq.refl _
  | true => by
    refine ⟨?pointerResult, ?pointerResultEq⟩
    case pointerResultEq => cbv <;> exact Eq.refl _

private theorem lexed (pointer : Bool) :
    lex (sourceText pointer) = .ok (wholeTokens pointer).val := by
  rw [source_spelling, lex_ofList]
  have actual := (scanned pointer).lexed (by cases pointer <;> cbv)
  rw [(wholeTokens pointer).property] at actual
  exact actual

end Phases
end Gabbro.Stage0.NamedSpaceWitness
