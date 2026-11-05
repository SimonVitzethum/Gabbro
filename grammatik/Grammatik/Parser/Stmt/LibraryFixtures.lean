module

public import Grammatik.Logik.Vertraege.Uebersetzung
import Grammatik.Parser.Stmt.LibraryFixtureProofs
public import Grammatik.Parser.Stmt.LibraryQualifiedFixtures
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


/-- Both fixtures retain the whole source. The second translator reverses two rows, rather than
    returning the input unchanged. Runtime library expansion is deliberately still refused. -/
def translationText (reverse : Bool) : String :=
  "module sample { table Rows count 2 { slot { v : u8 in 0 .. 10, } } " ++
  "library fn consume(p : ptr<normal, r> Rows) payload Rows { return; } " ++
  "translator build for consume(region : [u8 in 0 .. 10; 2]) -> [u8 in 0 .. 10; 2] " ++
  "effects { pure } { return " ++ (if reverse then "[region[1], region[0]]" else "region") ++
  "; } impl fn caller() { @sample#consume() { 3 5 }; return; } }"

-- The source equality below encodes these exact characters; later phases never
-- decode the complete UTF-8 source literal again.
private def translationCharacters (reverse : Bool) : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 's', 'a', 'm', 'p', 'l', 'e', ' ', '{', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'R',
   'o', 'w', 's', ' ', 'c', 'o', 'u', 'n', 't', ' ', '2', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ',
   ':', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', ',', ' ', '}', ' ', '}', ' ', 'l', 'i',
   'b', 'r', 'a', 'r', 'y', ' ', 'f', 'n', ' ', 'c', 'o', 'n', 's', 'u', 'm', 'e', '(', 'p', ' ', ':', ' ', 'p', 't',
   'r', '<', 'n', 'o', 'r', 'm', 'a', 'l', ',', ' ', 'r', '>', ' ', 'R', 'o', 'w', 's', ')', ' ', 'p', 'a', 'y', 'l',
   'o', 'a', 'd', ' ', 'R', 'o', 'w', 's', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ';', ' ', '}', ' ', 't', 'r',
   'a', 'n', 's', 'l', 'a', 't', 'o', 'r', ' ', 'b', 'u', 'i', 'l', 'd', ' ', 'f', 'o', 'r', ' ', 'c', 'o', 'n', 's',
   'u', 'm', 'e', '(', 'r', 'e', 'g', 'i', 'o', 'n', ' ', ':', ' ', '[', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.',
   '.', ' ', '1', '0', ';', ' ', '2', ']', ')', ' ', '-', '>', ' ', '[', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.',
   '.', ' ', '1', '0', ';', ' ', '2', ']', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'p', 'u', 'r', 'e',
   ' ', '}', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' '] ++
  (if reverse then ['[', 'r', 'e', 'g', 'i', 'o', 'n', '[', '1', ']', ',', ' ', 'r', 'e', 'g', 'i', 'o', 'n', '[', '0', ']', ']'] else ['r', 'e', 'g', 'i', 'o', 'n']) ++
  [';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'c', 'a', 'l', 'l', 'e', 'r', '(', ')', ' ', '{', ' ',
   '@', 's', 'a', 'm', 'p', 'l', 'e', '#', 'c', 'o', 'n', 's', 'u', 'm', 'e', '(', ')', ' ', '{', ' ', '3', ' ', '5',
   ' ', '}', ';', ' ', 'r', 'e', 't', 'u', 'r', 'n', ';', ' ', '}', ' ', '}']

private theorem translation_text (reverse : Bool) :
    translationText reverse = String.ofList (translationCharacters reverse) := by
  cases reverse <;> cbv

def translationTokens (reverse : Bool) : List Token :=
  (lexL (translationText reverse).toList).toOption.getD []

def translationItems (reverse : Bool) : List SItemTief :=
  (parseTopTief (translationTokens reverse)).toOption.getD []

def translationMembers (reverse : Bool) : List SItemTief :=
  Aufloesung.loeseL (Aufloesung.quelle (translationItems reverse)) [] (translationItems reverse)

def translationCall : SLibraryCall := ⟨["sample"], ["consume"], [], [.num 3, .num 5]⟩

def translationCaller : FnSig :=
  { art := "impl", name := "caller", params := [], res := none, fehler := none, klauseln := [] }

def translationCallerBody : SAnw := .block [.lcall translationCall] (some (.ret none))

-- Each phase is cut at a named success theorem. Extracted values have a
-- success witness, so no default participates in the certificate.
private theorem translation_lex_success (reverse : Bool) :
    (lexL (translationCharacters reverse)).toOption.isSome = true := by
  cases reverse <;> cbv

private def translationPhaseTokens (reverse : Bool) : List Token :=
  (lexL (translationCharacters reverse)).toOption.get (translation_lex_success reverse)

private theorem translation_parse_success (reverse : Bool) :
    (parseTopTief (translationPhaseTokens reverse)).toOption.isSome = true := by
  cases reverse <;> cbv

private def translationPhaseItems (reverse : Bool) : List SItemTief :=
  (parseTopTief (translationPhaseTokens reverse)).toOption.get (translation_parse_success reverse)

private def translationPhaseMembers (reverse : Bool) : List SItemTief :=
  Aufloesung.loeseL (Aufloesung.quelle (translationPhaseItems reverse)) [] (translationPhaseItems reverse)

private theorem translation_retained (reverse : Bool) :
    (translationPhaseMembers reverse)[3]? = some (.fnT translationCaller translationCallerBody) := by
  cases reverse <;> cbv

private theorem translation_library_success (reverse : Bool) :
    (libraryDecl (translationPhaseMembers reverse) translationCall).toOption.isSome = true := by
  cases reverse <;> cbv

private def translationPhaseLibrary (reverse : Bool) : ULibrary :=
  (libraryDecl (translationPhaseMembers reverse) translationCall).toOption.get
    (translation_library_success reverse)

private theorem translation_elab_success (reverse : Bool) :
    (elabU (pre108 (translatorItems (translationPhaseMembers reverse)
      (translationPhaseLibrary reverse)))).toOption.isSome = true := by
  cases reverse <;> cbv

private def translationPhaseUnit (reverse : Bool) : UProg :=
  (elabU (pre108 (translatorItems (translationPhaseMembers reverse)
    (translationPhaseLibrary reverse)))).toOption.get (translation_elab_success reverse)

-- The indexed facts are established at the concrete successful unit, then
-- transported together. Introducing its Fin index earlier unfolds the pipeline.
private theorem translation_lower_success (reverse : Bool) :
    (lowerAllg (translationPhaseUnit reverse)).toOption.isSome = true := by
  cases reverse with
  | false =>
    apply lowering_from_elaboration
      (source := elabU (pre108 (translatorItems (translationPhaseMembers false)
        (translationPhaseLibrary false))))
      (success := translation_elab_success false)
    refine ⟨?unitFalse, ?elaboratedFalse, ?invsFalse, ?contractsFalse, ?functionsFalse⟩
    case elaboratedFalse => cbv <;> exact Eq.refl _
    case invsFalse => cbv
    case contractsFalse => cbv
    case functionsFalse =>
      rintro ⟨index, bound⟩
      have small : index < 1 := bound
      have zero : index = 0 := by omega
      subst index
      constructor <;> cbv
  | true =>
    apply lowering_from_elaboration
      (source := elabU (pre108 (translatorItems (translationPhaseMembers true)
        (translationPhaseLibrary true))))
      (success := translation_elab_success true)
    refine ⟨?unitTrue, ?elaboratedTrue, ?invsTrue, ?contractsTrue, ?functionsTrue⟩
    case elaboratedTrue => cbv <;> exact Eq.refl _
    case invsTrue => cbv
    case contractsTrue => cbv
    case functionsTrue =>
      rintro ⟨index, bound⟩
      have small : index < 1 := bound
      have zero : index = 0 := by omega
      subst index
      constructor <;> cbv

private theorem translation_phases (reverse : Bool) :
    lexL (translationText reverse).toList = .ok (translationTokens reverse) ∧
    parseTopTief (translationTokens reverse) = .ok (translationItems reverse) ∧
    (translationMembers reverse)[3]? = some (.fnT translationCaller translationCallerBody) ∧
    ∃ library unit, libraryDecl (translationMembers reverse) translationCall = .ok library ∧
      elabU (pre108 (translatorItems (translationMembers reverse) library)) = .ok unit ∧
      (lowerAllg unit).toOption.isSome = true := by
  unfold translationMembers translationItems translationTokens
  simp only [translation_text, String.toList_ofList]
  refine certifyPhases (translationCharacters reverse) translationCall
    (fun members => members[3]? = some (.fnT translationCaller translationCallerBody)) ?_
  exact ⟨translationPhaseTokens reverse, translationPhaseItems reverse, translationPhaseMembers reverse,
    translationPhaseLibrary reverse, translationPhaseUnit reverse,
    except_ok_get (translation_lex_success reverse), except_ok_get (translation_parse_success reverse),
    rfl, translation_retained reverse, except_ok_get (translation_library_success reverse),
    except_ok_get (translation_elab_success reverse), translation_lower_success reverse⟩

/-- The exact caller is at member 3 and its call at statement path `[0]`. -/
def translationSource (reverse : Bool) : LibrarySource where
  characters := (translationText reverse).toList
  tokens := translationTokens reverse
  items := translationItems reverse
  lexed := by exact (translation_phases reverse).1
  parsed := by exact (translation_phases reverse).2.1
  callerIndex := 3
  caller := translationCaller
  callerBody := translationCallerBody
  atCaller := by exact (translation_phases reverse).2.2.1
  path := [0]
  call := translationCall
  atCall := rfl

theorem translation_library_exists (reverse : Bool) :
    (libraryDecl (translationMembers reverse) translationCall).toOption.isSome = true := by
  obtain ⟨library, unit, found, _, _⟩ := (translation_phases reverse).2.2.2
  rw [found]
  rfl

def translationLibrary (reverse : Bool) : ULibrary :=
  (libraryDecl (translationMembers reverse) translationCall).toOption.get (translation_library_exists reverse)

def translationUnit (reverse : Bool) : UProg :=
  (elabU (pre108 (translatorItems (translationMembers reverse) (translationLibrary reverse)))).toOption.getD
    { tabs := [], locks := [], fns := [] }

theorem translation_lower_exists (reverse : Bool) :
    (lowerAllg (translationUnit reverse)).toOption.isSome = true := by
  exact lowerFromPhases (translationMembers reverse) translationCall
    (translation_library_exists reverse) (translation_phases reverse).2.2.2

def translationLowered (reverse : Bool) :
    Programm (declOf (translationUnit reverse)) × List (declOf (translationUnit reverse)).Fn :=
  (lowerAllg (translationUnit reverse)).toOption.get (translation_lower_exists reverse)

def translationSchema : IntegerSchema := ⟨0, 10, 2⟩

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

private theorem rek_lex_success :
    (lexL translationRekCharacters).toOption.isSome = true := by cbv

private def rekPhaseTokens : List Token :=
  (lexL translationRekCharacters).toOption.get rek_lex_success

private theorem rek_parse_success :
    (parseTopTief rekPhaseTokens).toOption.isSome = true := by cbv

private def rekPhaseItems : List SItemTief :=
  (parseTopTief rekPhaseTokens).toOption.get rek_parse_success

private def rekPhaseMembers : List SItemTief :=
  Aufloesung.loeseL (Aufloesung.quelle rekPhaseItems) [] rekPhaseItems

private theorem rek_library_success :
    (libraryDecl rekPhaseMembers ⟨["sample"], ["consume"], [], [.num 3]⟩).toOption.isSome = true := by cbv

private def rekPhaseLibrary : ULibrary :=
  (libraryDecl rekPhaseMembers ⟨["sample"], ["consume"], [], [.num 3]⟩).toOption.get rek_library_success

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
    except_ok_get rek_lex_success, except_ok_get rek_parse_success, rfl, True.intro,
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
