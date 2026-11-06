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

def plainHead : ScanPiece ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'n', 'a', 'm', 'e', 'd', '_', 's', 'p', 'a', 'c', 'e', '_', 'p', 'r', 'o', 'b', 'e', ' ', '{', ' '] := by
  let tokens := ((lexL ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'n', 'a', 'm', 'e', 'd', '_', 's', 'p', 'a', 'c', 'e', '_', 'p', 'r', 'o', 'b', 'e', ' ', '{', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 3, equation := ?_ }
  intro rest fuel
  cbv

def pointerHead : ScanPiece ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'n', 'a', 'm', 'e', 'd', '_', 's', 'p', 'a', 'c', 'e', '_', 'p', 'o', 'i', 'n', 't', 'e', 'r', '_', 'p', 'r', 'o', 'b', 'e', ' ', '{', ' '] := by
  let tokens := ((lexL ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'n', 'a', 'm', 'e', 'd', '_', 's', 'p', 'a', 'c', 'e', '_', 'p', 'o', 'i', 'n', 't', 'e', 'r', '_', 'p', 'r', 'o', 'b', 'e', ' ', '{', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 3, equation := ?_ }
  intro rest fuel
  cbv

def table : ScanPiece ['t', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u', 'n', 't', ' ', '2', ' ', 's', 'p', 'a', 'c', 'e', ' ', 's', 'h', 'a', 'r', 'e', 'd', 'D', 'a', 't', 'a', ' ', '{', ' '] := by
  let tokens := ((lexL ['t', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u', 'n', 't', ' ', '2', ' ', 's', 'p', 'a', 'c', 'e', ' ', 's', 'h', 'a', 'r', 'e', 'd', 'D', 'a', 't', 'a', ' ', '{', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 7, equation := ?_ }
  intro rest fuel
  cbv

def field : ScanPiece ['s', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', '0', ',', ' ', '}', ' ', '}', ' '] := by
  let tokens := ((lexL ['s', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', '0', ',', ' ', '}', ' ', '}', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 11, equation := ?_ }
  intro rest fuel
  cbv

def plainMain : ScanPiece ['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', '0', ' '] := by
  let tokens := ((lexL ['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', '0', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 9, equation := ?_ }
  intro rest fuel
  cbv

def plainRead : ScanPiece ['e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'r', 'e', 'a', 'd', 's', ' ', 'T', '.', 's', 'l', 'o', 't', 's', ' ', '}', ' '] := by
  let tokens := ((lexL ['e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'r', 'e', 'a', 'd', 's', ' ', 'T', '.', 's', 'l', 'o', 't', 's', ' ', '}', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 5, equation := ?_ }
  intro rest fuel
  cbv

def pointerRead : ScanPiece ['e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'r', 'e', 'a', 'd', 's', ' ', 'p', '.', 's', 'l', 'o', 't', 's', ' ', '}', ' '] := by
  let tokens := ((lexL ['e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'r', 'e', 'a', 'd', 's', ' ', 'p', '.', 's', 'l', 'o', 't', 's', ' ', '}', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 5, equation := ?_ }
  intro rest fuel
  cbv

def plainReturn : ScanPiece ['{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'T', '.', 's', 'l', 'o', 't', 's', '[', '0', ']', '.', 'v', ';', ' ', '}', ' ', '}'] := by
  let tokens := ((lexL ['{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'T', '.', 's', 'l', 'o', 't', 's', '[', '0', ']', '.', 'v', ';', ' ', '}', ' ', '}']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 4, equation := ?_ }
  intro rest fuel
  cbv

def pointerReturn : ScanPiece ['{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'p', '.', 's', 'l', 'o', 't', 's', '[', '0', ']', '.', 'v', ';', ' ', '}', ' ', '}'] := by
  let tokens := ((lexL ['{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'p', '.', 's', 'l', 'o', 't', 's', '[', '0', ']', '.', 'v', ';', ' ', '}', ' ', '}']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 4, equation := ?_ }
  intro rest fuel
  cbv

def pointerParams : ScanPiece ['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', 'p', ' ', ':', ' ', 'p', 't', 'r', '<', 's', 'h', 'a', 'r', 'e', 'd', 'D', 'a', 't', 'a', ',', ' ', 'r', '>', ' ', 'T', ')', ' '] := by
  let tokens := ((lexL ['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', 'p', ' ', ':', ' ', 'p', 't', 'r', '<', 's', 'h', 'a', 'r', 'e', 'd', 'D', 'a', 't', 'a', ',', ' ', 'r', '>', ' ', 'T', ')', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 7, equation := ?_ }
  intro rest fuel
  cbv

def pointerResult : ScanPiece ['-', '>', ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', '0', ' '] := by
  let tokens := ((lexL ['-', '>', ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', '0', ' ']).toOption.get (by cbv)).dropLast
  refine { tokens := tokens, steps := tokens.length + 6, equation := ?_ }
  intro rest fuel
  cbv

-- Every token comes from a short real scanner application, with a symbolic
-- suffix and fuel. Only composition is used for the original complete text.
def scanned : (pointer : Bool) → ScanPiece (sourceText pointer).toList
  | false => ((plainHead.append table).append field).append
      ((plainMain.append plainRead).append plainReturn)
  | true => ((pointerHead.append table).append field).append
      (((pointerParams.append pointerResult).append pointerRead).append pointerReturn)

private theorem lexed (pointer : Bool) :
    lex (sourceText pointer) = .ok ((scanned pointer).tokens ++ [.ende]) := by
  cases pointer with
  | false =>
    change lex (String.ofList ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'n', 'a', 'm', 'e', 'd', '_', 's', 'p', 'a', 'c', 'e', '_', 'p', 'r', 'o', 'b', 'e', ' ', '{', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u', 'n', 't', ' ', '2', ' ', 's', 'p', 'a', 'c', 'e', ' ', 's', 'h', 'a', 'r', 'e', 'd', 'D', 'a', 't', 'a', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', '0', ',', ' ', '}', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', '0', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'r', 'e', 'a', 'd', 's', ' ', 'T', '.', 's', 'l', 'o', 't', 's', ' ', '}', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'T', '.', 's', 'l', 'o', 't', 's', '[', '0', ']', '.', 'v', ';', ' ', '}', ' ', '}']) = _
    rw [lex_ofList]
    exact (scanned false).lexed (by cbv)
  | true =>
    change lex (String.ofList ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'n', 'a', 'm', 'e', 'd', '_', 's', 'p', 'a', 'c', 'e', '_', 'p', 'o', 'i', 'n', 't', 'e', 'r', '_', 'p', 'r', 'o', 'b', 'e', ' ', '{', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u', 'n', 't', ' ', '2', ' ', 's', 'p', 'a', 'c', 'e', ' ', 's', 'h', 'a', 'r', 'e', 'd', 'D', 'a', 't', 'a', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', '0', ',', ' ', '}', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', 'p', ' ', ':', ' ', 'p', 't', 'r', '<', 's', 'h', 'a', 'r', 'e', 'd', 'D', 'a', 't', 'a', ',', ' ', 'r', '>', ' ', 'T', ')', ' ', '-', '>', ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', '0', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'r', 'e', 'a', 'd', 's', ' ', 'p', '.', 's', 'l', 'o', 't', 's', ' ', '}', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'p', '.', 's', 'l', 'o', 't', 's', '[', '0', ']', '.', 'v', ';', ' ', '}', ' ', '}']) = _
    rw [lex_ofList]
    exact (scanned true).lexed (by cbv)

attribute [local cbv_opaque] Frontend.normalize uFloatLimit
attribute [local cbv_eval] String.intercalate_singleton

-- Fix the complete parser and profile results before introducing dependent
-- AliasOrder/DerivedScopes types. No AST or scope snapshot is provided.
def parsed : (pointer : Bool) →
    { items : List SItemTief // parseTopTief ((scanned pointer).tokens ++ [.ende]) = .ok items }
  | false => by
    refine ⟨?items, ?made⟩
    case made => cbv <;> exact Eq.refl _
  | true => by
    refine ⟨?items, ?made⟩
    case made => cbv <;> exact Eq.refl _

def prepared : (pointer : Bool) →
    { value : Profil.Prepared {} (parsed pointer).val //
      Profil.prepareItems {} (parsed pointer).val = .ok value }
  | false => by
    refine ⟨?value, ?made⟩
    case made => cbv <;> exact Eq.refl _
  | true => by
    refine ⟨?value, ?made⟩
    case made => cbv <;> exact Eq.refl _

private theorem visibility (pointer : Bool) :
    Oeffentlich.huelleZu (prepared pointer).val.elaborierbar = true := by cases pointer <;> cbv
private theorem compileTime (pointer : Bool) :
    Frontend.compileTimeSafe (uMembers (pre108 (prepared pointer).val.elaborierbar)) = true := by
  cases pointer <;> cbv

def input (pointer : Bool) : SourceInput (sourceText pointer) where
  tokens := (scanned pointer).tokens ++ [.ende]
  items := (parsed pointer).val
  lexed := by exact lexed pointer
  parsed := by exact (parsed pointer).property
  prepared := (prepared pointer).val
  preparation := by exact (prepared pointer).property
  visibility := by exact visibility pointer
  compileTime := by exact compileTime pointer

def original : (pointer : Bool) →
    { items : List SItemTief // (input pointer).original = items }
  | false => by
    refine ⟨?items, ?same⟩
    case same => cbv <;> exact Eq.refl _
  | true => by
    refine ⟨?items, ?same⟩
    case same => cbv <;> exact Eq.refl _

private theorem metadata (pointer : Bool) :
    Konst.checkSourceMetadata (original pointer).val = .ok () := by cases pointer <;> cbv

def ordered : (pointer : Bool) →
    { order : Frontend.AliasOrder (original pointer).val //
      Frontend.orderAliases (original pointer).val = .ok order }
  | false => by
    refine ⟨?value, ?made⟩
    case made => cbv <;> exact Eq.refl _
  | true => by
    refine ⟨?value, ?made⟩
    case made => cbv <;> exact Eq.refl _

def scopes : (pointer : Bool) →
    { derived : Frontend.DerivedScopes (original pointer).val //
      Frontend.elaborateConstantScopes (original pointer).val = .ok derived }
  | false => by
    refine ⟨?value, ?made⟩
    case made => cbv <;> exact Eq.refl _
  | true => by
    refine ⟨?value, ?made⟩
    case made => cbv <;> exact Eq.refl _

private theorem aliases (pointer : Bool) :
    (original pointer).val.all (Frontend.checkAliasMeaning (scopes pointer).val.scope.types) = true := by
  cases pointer <;> cbv
private theorem constants (pointer : Bool) :
    (original pointer).val.all (Frontend.checkConstantMeaning (scopes pointer).val.scope.types
      (scopes pointer).val.scope.functions (scopes pointer).val.scope.values) = true := by
  cases pointer <;> cbv

def tail (pointer : Bool) : SourceTail (input pointer) :=
  SourceTail.ofOriginal (input pointer) (original pointer).val (original pointer).property
    (by exact metadata pointer) (ordered pointer).val (ordered pointer).property
    (scopes pointer).val (scopes pointer).property
    (by exact aliases pointer) (by exact constants pointer)

def source (pointer : Bool) : Frontend.Source (sourceText pointer) :=
  sourceFrom (input pointer) (tail pointer)

-- Opaque whole-field equations transport the same source packet without
-- repeatedly reopening the normalizer or the indexed SourceTail constructor.
theorem source_original (pointer : Bool) :
    uMembers (pre108 (source pointer).prepared.elaborierbar) = (original pointer).val :=
  (original pointer).property

theorem source_metadata (pointer : Bool) :
    Konst.checkSourceMetadata (uMembers (pre108 (source pointer).prepared.elaborierbar)) = .ok () := by
  rw [source_original]
  exact metadata pointer

end Phases
end Gabbro.Stage0.NamedSpaceWitness
