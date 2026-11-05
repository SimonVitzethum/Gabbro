module

public import Grammatik.Logik.Vertraege.Uebersetzung
import Grammatik.Parser.Stmt.LibraryFixtureProofs
import Grammatik.Parser.Stmt.LibraryFixtureScanning
public import Grammatik.Parser.Stmt.LibraryTranslationFixtures
-- Concrete phase certificates need the bodies of the canonical export gates.
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Grammatik.Parser.Elab.UebersetzeAllg3.Stufe
import all Grammatik.Parser.Elab.UebersetzeAllg3.Seq
import all Grammatik.Parser.Elab.UebersetzeAllg3.Struct
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

namespace Gabbro.Grammatik.Uebersetzung

open Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
open LibraryFixtureProofs

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

attribute [local cbv_opaque] elabFn lowStufe lowSeqL lowStructL lowEndL
attribute [local cbv_eval] empty_function seq_succ lowStructL_succ lowEndL_succ
  lowStufe_seq lowStufe_struct lowStufe_ende

/-- Two library functions under one key refuse as ambiguous, never by first match. -/
def doppeltMembers : List SItemTief :=
  [.fnT { art := "library", name := "consume", params := [], res := none, fehler := none, klauseln := [] } (.block [] none),
   .fnT { art := "library", name := "consume", params := [], res := none, fehler := none, klauseln := [] } (.block [] none)]

/-- A library function without a translator refuses: selection stays unique and total. -/
def ohneTranslatorMembers : List SItemTief :=
  [.fnT { art := "library", name := "solo", params := [], res := none, fehler := none, klauseln := [.load ["Rows"]] } (.block [] none)]

/-- A recursive translator: its body calls itself, so no certificate path exists (C17). -/
def translationRekText : String :=
  "module sample { table Rows count 1 { slot { v : u8 in 0 .. 10, } } " ++
  "library fn consume(p : ptr<normal, r> Rows) payload Rows { return; } " ++
  "translator build for consume(region : [u8 in 0 .. 10; 1]) -> [u8 in 0 .. 10; 1] " ++
  "effects { pure } { return build(region); } impl fn caller() { @sample#consume() { 3 }; return; } }"

private def translationRekCharacters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 's', 'a', 'm', 'p', 'l', 'e', ' ', '{', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'R',
   'o', 'w', 's', ' ', 'c', 'o', 'u', 'n', 't', ' ', '1', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ',
   ':', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', ',', ' ', '}', ' ', '}', ' ', 'l', 'i',
   'b', 'r', 'a', 'r', 'y', ' ', 'f', 'n', ' ', 'c', 'o', 'n', 's', 'u', 'm', 'e', '(', 'p', ' ', ':', ' ', 'p', 't',
   'r', '<', 'n', 'o', 'r', 'm', 'a', 'l', ',', ' ', 'r', '>', ' ', 'R', 'o', 'w', 's', ')', ' ', 'p', 'a', 'y', 'l',
   'o', 'a', 'd', ' ', 'R', 'o', 'w', 's', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ';', ' ', '}', ' ', 't', 'r',
   'a', 'n', 's', 'l', 'a', 't', 'o', 'r', ' ', 'b', 'u', 'i', 'l', 'd', ' ', 'f', 'o', 'r', ' ', 'c', 'o', 'n', 's',
   'u', 'm', 'e', '(', 'r', 'e', 'g', 'i', 'o', 'n', ' ', ':', ' ', '[', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.',
   '.', ' ', '1', '0', ';', ' ', '1', ']', ')', ' ', '-', '>', ' ', '[', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.',
   '.', ' ', '1', '0', ';', ' ', '1', ']', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'p', 'u', 'r', 'e',
   ' ', '}', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'b', 'u', 'i', 'l', 'd', '(', 'r', 'e', 'g', 'i', 'o',
   'n', ')', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'c', 'a', 'l', 'l', 'e', 'r', '(', ')', ' ',
   '{', ' ', '@', 's', 'a', 'm', 'p', 'l', 'e', '#', 'c', 'o', 'n', 's', 'u', 'm', 'e', '(', ')', ' ', '{', ' ', '3',
   ' ', '}', ';', ' ', 'r', 'e', 't', 'u', 'r', 'n', ';', ' ', '}', ' ', '}']

private theorem translation_rek_text :
    translationRekText = String.ofList translationRekCharacters := by cbv

def translationRekTokens : List Token := (lexL translationRekText.toList).toOption.getD []

def translationRekItems : List SItemTief := (parseTopTief translationRekTokens).toOption.getD []

def translationRekMembers : List SItemTief :=
  Aufloesung.loeseL (Aufloesung.quelle translationRekItems) [] translationRekItems

private def rekChunks : List LibraryFixtureScanning.Chunk :=
  [LibraryFixtureScanning.Chunk.moduleSample, .tableOne, .slot, .libraryHead, .libraryTail,
    .translatorHead, .inputOne, .outputOne, .effects, .recursiveResult, .callerHead,
    .callSample, .valuesOne, .close]

private def rekPhaseTokens : List Token := LibraryFixtureScanning.tokens rekChunks

private theorem rek_lexed : lexL translationRekCharacters = .ok rekPhaseTokens := by
  have source : translationRekCharacters = LibraryFixtureScanning.characters rekChunks := rfl
  rw [source]
  exact LibraryFixtureScanning.lex_chunks rekChunks (by decide +kernel)

private theorem rek_parsed : parseTopTief rekPhaseTokens =
    .ok (parsedFixture 1 (.call "build" [.variable "region"]) [.num 3]) := by cbv

private theorem rek_parse_success :
    (parseTopTief rekPhaseTokens).toOption.isSome = true := by
  rw [rek_parsed]
  rfl

private def rekPhaseItems : List SItemTief :=
  (parseTopTief rekPhaseTokens).toOption.get rek_parse_success

private theorem rek_items : rekPhaseItems =
    parsedFixture 1 (.call "build" [.variable "region"]) [.num 3] := by
  simp only [rekPhaseItems, rek_parsed]
  rfl

attribute [local cbv_opaque] rekPhaseItems
attribute [local cbv_eval] rek_items

private def rekPhaseMembers : List SItemTief :=
  Aufloesung.loeseL (Aufloesung.quelle rekPhaseItems) [] rekPhaseItems

private theorem rek_library_success :
    (libraryDecl rekPhaseMembers ⟨["sample"], ["consume"], [], [.num 3]⟩).toOption.isSome = true := by cbv

private def rekPhaseLibrary : ULibrary :=
  (libraryDecl rekPhaseMembers ⟨["sample"], ["consume"], [], [.num 3]⟩).toOption.get rek_library_success

-- The ordinary-call binder's unused float target keeps its endpoints symbolic.
attribute [local cbv_opaque] uFloatLimit
private theorem rek_elab_success :
    (elabU (pre108 (translatorItems rekPhaseMembers rekPhaseLibrary))).toOption.isSome = true := by cbv

private def rekPhaseUnit : UProg :=
  (elabU (pre108 (translatorItems rekPhaseMembers rekPhaseLibrary))).toOption.get rek_elab_success

private theorem rek_lower_success : (lowerAllg rekPhaseUnit).toOption.isSome = true := by
  apply lowering_from_elaboration
    (source := elabU (pre108 (translatorItems rekPhaseMembers rekPhaseLibrary)))
    (success := rek_elab_success)
  refine ⟨?unit, ?elaborated, ?invariants, ?contracts, ?functions⟩
  case elaborated => cbv <;> exact Eq.refl _
  case invariants => cbv
  case contracts => cbv
  case functions =>
    rintro ⟨index, bound⟩
    have small : index < 1 := bound
    have zero : index = 0 := by omega
    subst index
    constructor <;> cbv

private theorem translation_rek_phases :
    lexL translationRekText.toList = .ok translationRekTokens ∧
    parseTopTief translationRekTokens = .ok translationRekItems ∧ True ∧
    ∃ library unit,
      libraryDecl translationRekMembers ⟨["sample"], ["consume"], [], [.num 3]⟩ = .ok library ∧
      elabU (pre108 (translatorItems translationRekMembers library)) = .ok unit ∧
      (lowerAllg unit).toOption.isSome = true := by
  unfold translationRekMembers translationRekItems translationRekTokens
  simp only [translation_rek_text, String.toList_ofList]
  refine certifyPhases translationRekCharacters ⟨["sample"], ["consume"], [], [.num 3]⟩
    (fun (_ : List SItemTief) => True) ?_
  exact ⟨rekPhaseTokens, rekPhaseItems, rekPhaseMembers, rekPhaseLibrary, rekPhaseUnit,
    rek_lexed, except_ok_get rek_parse_success, rfl, True.intro,
    except_ok_get rek_library_success, except_ok_get rek_elab_success, rek_lower_success⟩

theorem translation_rek_library_zeuge :
    (libraryDecl translationRekMembers ⟨["sample"], ["consume"], [], [.num 3]⟩).toOption.isSome = true := by
  obtain ⟨library, unit, found, _, _⟩ := translation_rek_phases.2.2.2
  rw [found]
  rfl

def translationRekLibrary : ULibrary :=
  (libraryDecl translationRekMembers ⟨["sample"], ["consume"], [], [.num 3]⟩).toOption.get
    translation_rek_library_zeuge

def translationRekUnit : UProg :=
  (elabU (pre108 (translatorItems translationRekMembers translationRekLibrary))).toOption.getD
    { tabs := [], locks := [], fns := [] }

theorem translation_rek_lower_zeuge : (lowerAllg translationRekUnit).toOption.isSome = true := by
  exact lowerFromPhases translationRekMembers ⟨["sample"], ["consume"], [], [.num 3]⟩
    translation_rek_library_zeuge translation_rek_phases.2.2.2

def translationRekLowered :
    Programm (declOf translationRekUnit) × List (declOf translationRekUnit).Fn :=
  (lowerAllg translationRekUnit).toOption.get translation_rek_lower_zeuge

end Gabbro.Grammatik.Uebersetzung
