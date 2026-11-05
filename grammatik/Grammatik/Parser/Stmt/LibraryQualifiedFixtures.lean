module

public import Grammatik.Logik.Vertraege.Uebersetzung
public import Grammatik.Parser.Stmt.LibraryFixtureProofs
import Grammatik.Parser.Stmt.LibraryFixtureScanning
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

-- Reduce only the selected operation of the canonical fuel record. Evaluating
-- its unused fields eagerly would construct all 100000 recursive levels.
private theorem seq_succ (u : UProg) (caller : Fin u.fns.length) (n : Nat)
    {l : Bool} (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (pe : AtTop u caller Λ) (ss : List UStmt) :
    lowSeqL (l := l) u caller Γ fn (n + 1) Λ pe ss =
      lowSeqStep u caller (lowStufe u caller n) Γ fn Λ pe ss := rfl

attribute [local cbv_opaque] lowStufe lowSeqL lowStructL lowEndL
attribute [local cbv_eval] seq_succ lowStructL_succ lowEndL_succ
  lowStufe_seq lowStufe_struct lowStufe_ende


/-- A qualified translator target parses to its joined path. -/
def ttQual : List Token :=
  [.wort "translator", .ident "build", .wort "for", .ident "a", .zeichen "::", .ident "sum",
   .zeichen "(", .ident "region", .zeichen ":", .ident "SumTab",
   .zeichen ")", .zeichen "->", .ident "SumTab", .wort "effects",
   .zeichen "{", .wort "pure", .zeichen "}", .wort "costs",
   .zeichen "<=", .num 8, .wort "ops", .wort "decreases",
   .ident "region", .zeichen ".", .ident "v", .zeichen "{",
   .wort "return", .ident "region", .zeichen ";", .zeichen "}",
   .ende]

/-- Two modules with same-named libraries; the top-level caller qualifies module `a`. -/
def translationQualText : String :=
  "module a { table Rows count 2 { slot { v : u8 in 0 .. 10, } } " ++
  "library fn consume(p : ptr<normal, r> Rows) payload Rows { return; } " ++
  "translator build for consume(region : [u8 in 0 .. 10; 2]) -> [u8 in 0 .. 10; 2] " ++
  "effects { pure } { return region; } } " ++
  "module b { table Rows count 2 { slot { v : u8 in 0 .. 10, } } " ++
  "library fn consume(p : ptr<normal, r> Rows) payload Rows { return; } " ++
  "translator build for consume(region : [u8 in 0 .. 10; 2]) -> [u8 in 0 .. 10; 2] " ++
  "effects { pure } { return region; } } " ++
  "impl fn caller() { @a#consume() { 3 5 }; return; }"

private def translationQualCharacters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'a', ' ', '{', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'R', 'o', 'w', 's', ' ', 'c',
   'o', 'u', 'n', 't', ' ', '2', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '8', ' ',
   'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', ',', ' ', '}', ' ', '}', ' ', 'l', 'i', 'b', 'r', 'a', 'r', 'y',
   ' ', 'f', 'n', ' ', 'c', 'o', 'n', 's', 'u', 'm', 'e', '(', 'p', ' ', ':', ' ', 'p', 't', 'r', '<', 'n', 'o', 'r',
   'm', 'a', 'l', ',', ' ', 'r', '>', ' ', 'R', 'o', 'w', 's', ')', ' ', 'p', 'a', 'y', 'l', 'o', 'a', 'd', ' ', 'R',
   'o', 'w', 's', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ';', ' ', '}', ' ', 't', 'r', 'a', 'n', 's', 'l', 'a',
   't', 'o', 'r', ' ', 'b', 'u', 'i', 'l', 'd', ' ', 'f', 'o', 'r', ' ', 'c', 'o', 'n', 's', 'u', 'm', 'e', '(', 'r',
   'e', 'g', 'i', 'o', 'n', ' ', ':', ' ', '[', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', ';',
   ' ', '2', ']', ')', ' ', '-', '>', ' ', '[', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', ';',
   ' ', '2', ']', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'p', 'u', 'r', 'e', ' ', '}', ' ', '{', ' ',
   'r', 'e', 't', 'u', 'r', 'n', ' ', 'r', 'e', 'g', 'i', 'o', 'n', ';', ' ', '}', ' ', '}', ' ', 'm', 'o', 'd', 'u',
   'l', 'e', ' ', 'b', ' ', '{', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'R', 'o', 'w', 's', ' ', 'c', 'o', 'u', 'n', 't',
   ' ', '2', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0',
   ' ', '.', '.', ' ', '1', '0', ',', ' ', '}', ' ', '}', ' ', 'l', 'i', 'b', 'r', 'a', 'r', 'y', ' ', 'f', 'n', ' ',
   'c', 'o', 'n', 's', 'u', 'm', 'e', '(', 'p', ' ', ':', ' ', 'p', 't', 'r', '<', 'n', 'o', 'r', 'm', 'a', 'l', ',',
   ' ', 'r', '>', ' ', 'R', 'o', 'w', 's', ')', ' ', 'p', 'a', 'y', 'l', 'o', 'a', 'd', ' ', 'R', 'o', 'w', 's', ' ',
   '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ';', ' ', '}', ' ', 't', 'r', 'a', 'n', 's', 'l', 'a', 't', 'o', 'r', ' ',
   'b', 'u', 'i', 'l', 'd', ' ', 'f', 'o', 'r', ' ', 'c', 'o', 'n', 's', 'u', 'm', 'e', '(', 'r', 'e', 'g', 'i', 'o',
   'n', ' ', ':', ' ', '[', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', ';', ' ', '2', ']', ')',
   ' ', '-', '>', ' ', '[', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', ';', ' ', '2', ']', ' ',
   'e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'p', 'u', 'r', 'e', ' ', '}', ' ', '{', ' ', 'r', 'e', 't', 'u',
   'r', 'n', ' ', 'r', 'e', 'g', 'i', 'o', 'n', ';', ' ', '}', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ',
   'c', 'a', 'l', 'l', 'e', 'r', '(', ')', ' ', '{', ' ', '@', 'a', '#', 'c', 'o', 'n', 's', 'u', 'm', 'e', '(', ')',
   ' ', '{', ' ', '3', ' ', '5', ' ', '}', ';', ' ', 'r', 'e', 't', 'u', 'r', 'n', ';', ' ', '}']

private theorem translation_qual_text :
    translationQualText = String.ofList translationQualCharacters := by cbv

def translationQualTokens : List Token := (lexL translationQualText.toList).toOption.getD []

def translationQualItems : List SItemTief := (parseTopTief translationQualTokens).toOption.getD []

def translationQualMembers : List SItemTief :=
  Aufloesung.loeseL (Aufloesung.quelle translationQualItems) [] translationQualItems

/-- The resolved call: the qualifier joins the function path into the unique item key. -/
def translationQualCall : SLibraryCall := ⟨["a"], ["a::consume"], [], [.num 3, .num 5]⟩

def translationQualCaller : FnSig :=
  { art := "impl", name := "caller", params := [], res := none, fehler := none, klauseln := [] }

def translationQualCallerBody : SAnw := .block [.lcall translationQualCall] (some (.ret none))

private def qualChunks : List LibraryFixtureScanning.Chunk :=
  let moduleA := [LibraryFixtureScanning.Chunk.moduleA, .tableTwo, .slot, .libraryHead,
    .libraryTail, .translatorHead, .inputTwo, .outputTwo, .effects, .plainResult, .closeSpace]
  let moduleB := [LibraryFixtureScanning.Chunk.moduleB, .tableTwo, .slot, .libraryHead,
    .libraryTail, .translatorHead, .inputTwo, .outputTwo, .effects, .plainResult, .closeSpace]
  moduleA ++ moduleB ++ [LibraryFixtureScanning.Chunk.callerHead, .callA, .valuesTwoFinal]

private def qualPhaseTokens : List Token := LibraryFixtureScanning.tokens qualChunks

private theorem qual_lexed : lexL translationQualCharacters = .ok qualPhaseTokens := by
  have source : translationQualCharacters = LibraryFixtureScanning.characters qualChunks := rfl
  rw [source]
  exact LibraryFixtureScanning.lex_chunks qualChunks (by decide +kernel)

private theorem qual_parse_success :
    (parseTopTief qualPhaseTokens).toOption.isSome = true := by cbv

private def qualPhaseItems : List SItemTief :=
  (parseTopTief qualPhaseTokens).toOption.get qual_parse_success

private def qualPhaseMembers : List SItemTief :=
  Aufloesung.loeseL (Aufloesung.quelle qualPhaseItems) [] qualPhaseItems

private theorem qual_retained :
    qualPhaseMembers[6]? = some (.fnT translationQualCaller translationQualCallerBody) := by cbv

private theorem qual_library_success :
    (libraryDecl qualPhaseMembers translationQualCall).toOption.isSome = true := by cbv

private def qualPhaseLibrary : ULibrary :=
  (libraryDecl qualPhaseMembers translationQualCall).toOption.get qual_library_success

private theorem qual_elab_success :
    (elabU (pre108 (translatorItems qualPhaseMembers qualPhaseLibrary))).toOption.isSome = true := by cbv

private def qualPhaseUnit : UProg :=
  (elabU (pre108 (translatorItems qualPhaseMembers qualPhaseLibrary))).toOption.get qual_elab_success

private theorem qual_lower_success : (lowerAllg qualPhaseUnit).toOption.isSome = true := by
  apply lowering_from_elaboration
    (source := elabU (pre108 (translatorItems qualPhaseMembers qualPhaseLibrary)))
    (success := qual_elab_success)
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

-- Only named phase facts occur in this graph transport. The kernel need not
-- recheck a single existential proof containing all normalized source trees.
private theorem translation_qual_phases :
    lexL translationQualText.toList = .ok translationQualTokens ∧
    parseTopTief translationQualTokens = .ok translationQualItems ∧
    translationQualMembers[6]? = some (.fnT translationQualCaller translationQualCallerBody) ∧
    ∃ library unit, libraryDecl translationQualMembers translationQualCall = .ok library ∧
      elabU (pre108 (translatorItems translationQualMembers library)) = .ok unit ∧
      (lowerAllg unit).toOption.isSome = true := by
  unfold translationQualMembers translationQualItems translationQualTokens
  simp only [translation_qual_text, String.toList_ofList]
  refine certifyPhases translationQualCharacters translationQualCall
    (fun members => members[6]? = some (.fnT translationQualCaller translationQualCallerBody)) ?_
  exact ⟨qualPhaseTokens, qualPhaseItems, qualPhaseMembers, qualPhaseLibrary, qualPhaseUnit,
    qual_lexed, except_ok_get qual_parse_success, rfl, qual_retained,
    except_ok_get qual_library_success, except_ok_get qual_elab_success, qual_lower_success⟩

/-- The exact caller is at member 6 (two opened modules) and its call at statement path `[0]`. -/
def translationQualSource : LibrarySource where
  characters := translationQualText.toList
  tokens := translationQualTokens
  items := translationQualItems
  lexed := by exact translation_qual_phases.1
  parsed := by exact translation_qual_phases.2.1
  callerIndex := 6
  caller := translationQualCaller
  callerBody := translationQualCallerBody
  atCaller := by exact translation_qual_phases.2.2.1
  path := [0]
  call := translationQualCall
  atCall := rfl

theorem translation_qual_library_zeuge :
    (libraryDecl translationQualMembers translationQualCall).toOption.isSome = true := by
  obtain ⟨library, unit, found, _, _⟩ := translation_qual_phases.2.2.2
  rw [found]
  rfl

def translationQualLibrary : ULibrary :=
  (libraryDecl translationQualMembers translationQualCall).toOption.get translation_qual_library_zeuge

def translationQualUnit : UProg :=
  (elabU (pre108 (translatorItems translationQualMembers translationQualLibrary))).toOption.getD
    { tabs := [], locks := [], fns := [] }

theorem translation_qual_lower_zeuge :
    (lowerAllg translationQualUnit).toOption.isSome = true := by
  exact lowerFromPhases translationQualMembers translationQualCall
    translation_qual_library_zeuge translation_qual_phases.2.2.2

def translationQualLowered :
    Programm (declOf translationQualUnit) × List (declOf translationQualUnit).Fn :=
  (lowerAllg translationQualUnit).toOption.get translation_qual_lower_zeuge

private theorem qual_phase_data :
    DeclarationData qualPhaseLibrary qualPhaseUnit
      ((lowerAllg qualPhaseUnit).toOption.get qual_lower_success)
      (⟨0, 10, 2⟩ : IntegerSchema) (fun input => input) := by
  refine certifyResults qualPhaseMembers translationQualCall
    (fun library unit image => DeclarationData library unit image
      (⟨0, 10, 2⟩ : IntegerSchema) (fun input => input)) ?_
    qual_library_success qual_elab_success qual_lower_success
  refine ⟨?library, ?found, ?unit, ?made, ?imageData⟩
  case found => cbv <;> exact Eq.refl _
  case made => cbv <;> exact Eq.refl _
  case imageData => library_emitted

/-- Preserve the complete qualified phase result before typed projections. -/
theorem translation_qual_export_data :
    elabU (pre108 (translatorItems translationQualMembers translationQualLibrary)) =
      .ok translationQualUnit ∧
    DeclarationData translationQualLibrary translationQualUnit translationQualLowered
      (⟨0, 10, 2⟩ : IntegerSchema) (fun input => input) := by
  have members : translationQualMembers = qualPhaseMembers := by
    simp only [translationQualMembers, translationQualItems, translationQualTokens,
      translation_qual_text, String.toList_ofList, qual_lexed, except_ok_get qual_parse_success]
    rfl
  exact certifyData translationQualMembers translationQualCall translation_qual_library_zeuge
    (fun library unit image => DeclarationData library unit image
      (⟨0, 10, 2⟩ : IntegerSchema) (fun input => input)) qualPhaseLibrary qualPhaseUnit
    (by rw [members]; exact except_ok_get qual_library_success)
    (by rw [members]; exact except_ok_get qual_elab_success)
    qual_lower_success qual_phase_data translation_qual_lower_zeuge

end Gabbro.Grammatik.Uebersetzung

