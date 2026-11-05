module

public import Grammatik.Logik.Vertraege.Uebersetzung
import Grammatik.Parser.Stmt.LibraryFixtureProofs
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

-- The two source branches have separate proof terms and independent phase witnesses.
private theorem translation_false_phases :
    lexL (translationText false).toList = .ok (translationTokens false) ∧
    parseTopTief (translationTokens false) = .ok (translationItems false) ∧
    (translationMembers false)[3]? = some (.fnT translationCaller translationCallerBody) ∧
    ∃ library unit, libraryDecl (translationMembers false) translationCall = .ok library ∧
      elabU (pre108 (translatorItems (translationMembers false) library)) = .ok unit ∧
      (lowerAllg unit).toOption.isSome = true := by
  unfold translationMembers translationItems translationTokens
  refine certifyPhases (translationText false).toList translationCall
    (fun (members : List SItemTief) =>
      members[3]? = some (SItemTief.fnT translationCaller translationCallerBody)) ?_
  refine ⟨?tokensfalse, ?itemsfalse, ?membersfalse, ?libraryfalse, ?unitfalse,
    ?lexedfalse, ?parsedfalse, ?resolvedfalse, ?keptfalse,
    ?foundfalse, ?elaboratedfalse, ?loweredfalse⟩
  case lexedfalse =>
    rw [translation_text, String.toList_ofList]
    cbv <;> exact Eq.refl _
  case parsedfalse => cbv <;> exact Eq.refl _
  case resolvedfalse => cbv <;> exact Eq.refl _
  case keptfalse => cbv
  case foundfalse => cbv <;> exact Eq.refl _
  case elaboratedfalse => cbv <;> exact Eq.refl _
  case loweredfalse =>
    apply lowering_ok
    · cbv
    · cbv
    · rintro ⟨index, bound⟩
      have small : index < 1 := bound
      have zero : index = 0 := by omega
      subst index
      constructor <;> cbv

private theorem translation_true_phases :
    lexL (translationText true).toList = .ok (translationTokens true) ∧
    parseTopTief (translationTokens true) = .ok (translationItems true) ∧
    (translationMembers true)[3]? = some (.fnT translationCaller translationCallerBody) ∧
    ∃ library unit, libraryDecl (translationMembers true) translationCall = .ok library ∧
      elabU (pre108 (translatorItems (translationMembers true) library)) = .ok unit ∧
      (lowerAllg unit).toOption.isSome = true := by
  unfold translationMembers translationItems translationTokens
  refine certifyPhases (translationText true).toList translationCall
    (fun (members : List SItemTief) =>
      members[3]? = some (SItemTief.fnT translationCaller translationCallerBody)) ?_
  refine ⟨?tokenstrue, ?itemstrue, ?memberstrue, ?librarytrue, ?unittrue,
    ?lexedtrue, ?parsedtrue, ?resolvedtrue, ?kepttrue,
    ?foundtrue, ?elaboratedtrue, ?loweredtrue⟩
  case lexedtrue =>
    rw [translation_text, String.toList_ofList]
    cbv <;> exact Eq.refl _
  case parsedtrue => cbv <;> exact Eq.refl _
  case resolvedtrue => cbv <;> exact Eq.refl _
  case kepttrue => cbv
  case foundtrue => cbv <;> exact Eq.refl _
  case elaboratedtrue => cbv <;> exact Eq.refl _
  case loweredtrue =>
    apply lowering_ok
    · cbv
    · cbv
    · rintro ⟨index, bound⟩
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
  cases reverse with
  | false => exact translation_false_phases
  | true => exact translation_true_phases

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

private theorem translation_qual_phases :
    lexL translationQualText.toList = .ok translationQualTokens ∧
    parseTopTief translationQualTokens = .ok translationQualItems ∧
    translationQualMembers[6]? = some (.fnT translationQualCaller translationQualCallerBody) ∧
    ∃ library unit, libraryDecl translationQualMembers translationQualCall = .ok library ∧
      elabU (pre108 (translatorItems translationQualMembers library)) = .ok unit ∧
      (lowerAllg unit).toOption.isSome = true := by
  unfold translationQualMembers translationQualItems translationQualTokens
  refine certifyPhases translationQualText.toList translationQualCall
    (fun (members : List SItemTief) =>
      members[6]? = some (SItemTief.fnT translationQualCaller translationQualCallerBody)) ?_
  refine ⟨?tokens, ?items, ?members, ?library, ?unit,
    ?lexed, ?parsed, ?resolved, ?kept, ?found, ?elaborated, ?lowered⟩
  case lexed =>
    rw [translation_qual_text, String.toList_ofList]
    cbv <;> exact Eq.refl _
  case parsed => cbv <;> exact Eq.refl _
  case resolved => cbv <;> exact Eq.refl _
  case kept => cbv
  case found => cbv <;> exact Eq.refl _
  case elaborated => cbv <;> exact Eq.refl _
  case lowered =>
    apply lowering_ok
    · cbv
    · cbv
    · rintro ⟨index, bound⟩
      have small : index < 1 := bound
      have zero : index = 0 := by omega
      subst index
      constructor <;> cbv

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

private theorem translation_rek_phases :
    lexL translationRekText.toList = .ok translationRekTokens ∧
    parseTopTief translationRekTokens = .ok translationRekItems ∧ True ∧
    ∃ library unit,
      libraryDecl translationRekMembers ⟨["sample"], ["consume"], [], [.num 3]⟩ = .ok library ∧
      elabU (pre108 (translatorItems translationRekMembers library)) = .ok unit ∧
      (lowerAllg unit).toOption.isSome = true := by
  unfold translationRekMembers translationRekItems translationRekTokens
  refine certifyPhases translationRekText.toList ⟨["sample"], ["consume"], [], [.num 3]⟩
    (fun (_ : List SItemTief) => True) ?_
  refine ⟨?tokens, ?items, ?members, ?library, ?unit,
    ?lexed, ?parsed, ?resolved, ?kept, ?found, ?elaborated, ?lowered⟩
  case lexed =>
    rw [translation_rek_text, String.toList_ofList]
    cbv <;> exact Eq.refl _
  case parsed => cbv <;> exact Eq.refl _
  case resolved => cbv <;> exact Eq.refl _
  case kept => trivial
  case found => cbv <;> exact Eq.refl _
  case elaborated => cbv <;> exact Eq.refl _
  case lowered =>
    apply lowering_ok
    · cbv
    · cbv
    · rintro ⟨index, bound⟩
      have small : index < 1 := bound
      have zero : index = 0 := by omega
      subst index
      constructor <;> cbv

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
