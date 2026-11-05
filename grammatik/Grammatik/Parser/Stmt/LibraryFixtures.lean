module

public import Grammatik.Logik.Vertraege.Uebersetzung
-- Concrete phase certificates need the bodies of the canonical export gates.
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
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

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

-- Each computed phase supplies the next phase's concrete canonical input. The
-- public getD definitions are retained, but success never follows from a default.
private theorem certifyPhases (characters : List Char) (call : SLibraryCall)
    (retained : List SItemTief → Prop)
    (phases : ∃ tokens items members library unit,
      lexL characters = .ok tokens ∧ parseTopTief tokens = .ok items ∧
      Aufloesung.loeseL (Aufloesung.quelle items) [] items = members ∧ retained members ∧
      libraryDecl members call = .ok library ∧
      elabU (pre108 (translatorItems members library)) = .ok unit ∧
      (lowerAllg unit).toOption.isSome = true) :
    let tokens := (lexL characters).toOption.getD []
    let items := (parseTopTief tokens).toOption.getD []
    let members := Aufloesung.loeseL (Aufloesung.quelle items) [] items
    lexL characters = .ok tokens ∧ parseTopTief tokens = .ok items ∧ retained members ∧
      ∃ library unit, libraryDecl members call = .ok library ∧
        elabU (pre108 (translatorItems members library)) = .ok unit ∧
        (lowerAllg unit).toOption.isSome = true := by
  obtain ⟨tokens, items, members, library, unit, lexed, parsed, resolved, kept,
    found, elaborated, lowered⟩ := phases
  dsimp only
  have tokenEq : (lexL characters).toOption.getD [] = tokens := by rw [lexed]; rfl
  rw [tokenEq]
  have itemEq : (parseTopTief tokens).toOption.getD [] = items := by rw [parsed]; rfl
  rw [itemEq, resolved]
  exact ⟨lexed, parsed, kept, library, unit, found, elaborated, lowered⟩

private theorem lowerFromPhases (members : List SItemTief) (call : SLibraryCall)
    (present : (libraryDecl members call).toOption.isSome = true)
    (phases : ∃ library unit, libraryDecl members call = .ok library ∧
      elabU (pre108 (translatorItems members library)) = .ok unit ∧
      (lowerAllg unit).toOption.isSome = true) :
    (lowerAllg ((elabU (pre108 (translatorItems members
      ((libraryDecl members call).toOption.get present)))).toOption.getD
        { tabs := [], locks := [], fns := [] })).toOption.isSome = true := by
  obtain ⟨library, unit, found, elaborated, lowered⟩ := phases
  have selected : (libraryDecl members call).toOption.get present = library := by
    exact (Except.ok.inj (found.symm.trans (except_ok_get present))).symm
  rw [selected, elaborated]
  exact lowered

/-- Both fixtures retain the whole source. The second translator reverses two rows, rather than
    returning the input unchanged. Runtime library expansion is deliberately still refused. -/
def translationText (reverse : Bool) : String :=
  "module sample { table Rows count 2 { slot { v : u8 in 0 .. 10, } } " ++
  "library fn consume(p : ptr<normal, r> Rows) payload Rows { return; } " ++
  "translator build for consume(region : [u8 in 0 .. 10; 2]) -> [u8 in 0 .. 10; 2] " ++
  "effects { pure } { return " ++ (if reverse then "[region[1], region[0]]" else "region") ++
  "; } impl fn caller() { @sample#consume() { 3 5 }; return; } }"

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

private theorem translation_phases (reverse : Bool) :
    lexL (translationText reverse).toList = .ok (translationTokens reverse) ∧
    parseTopTief (translationTokens reverse) = .ok (translationItems reverse) ∧
    (translationMembers reverse)[3]? = some (.fnT translationCaller translationCallerBody) ∧
    ∃ library unit, libraryDecl (translationMembers reverse) translationCall = .ok library ∧
      elabU (pre108 (translatorItems (translationMembers reverse) library)) = .ok unit ∧
      (lowerAllg unit).toOption.isSome = true := by
  apply certifyPhases (translationText reverse).toList translationCall
    (fun members => members[3]? = some (.fnT translationCaller translationCallerBody))
  cases reverse
  all_goals
    refine ⟨?tokens, ?items, ?members, ?library, ?unit,
      ?lexed, ?parsed, ?resolved, ?kept, ?found, ?elaborated, ?lowered⟩
    case lexed => cbv
    case parsed => cbv
    case resolved => cbv
    case kept => cbv
    case found => cbv
    case elaborated => cbv
    case lowered => cbv

/-- The exact caller is at member 3 and its call at statement path `[0]`. -/
def translationSource (reverse : Bool) : LibrarySource where
  characters := (translationText reverse).toList
  tokens := translationTokens reverse
  items := translationItems reverse
  lexed := (translation_phases reverse).1
  parsed := (translation_phases reverse).2.1
  callerIndex := 3
  caller := translationCaller
  callerBody := translationCallerBody
  atCaller := (translation_phases reverse).2.2.1
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
  apply certifyPhases translationQualText.toList translationQualCall
    (fun members => members[6]? = some (.fnT translationQualCaller translationQualCallerBody))
  refine ⟨?tokens, ?items, ?members, ?library, ?unit,
    ?lexed, ?parsed, ?resolved, ?kept, ?found, ?elaborated, ?lowered⟩
  case lexed => cbv
  case parsed => cbv
  case resolved => cbv
  case kept => cbv
  case found => cbv
  case elaborated => cbv
  case lowered => cbv

/-- The exact caller is at member 6 (two opened modules) and its call at statement path `[0]`. -/
def translationQualSource : LibrarySource where
  characters := translationQualText.toList
  tokens := translationQualTokens
  items := translationQualItems
  lexed := translation_qual_phases.1
  parsed := translation_qual_phases.2.1
  callerIndex := 6
  caller := translationQualCaller
  callerBody := translationQualCallerBody
  atCaller := translation_qual_phases.2.2.1
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
  apply certifyPhases translationRekText.toList ⟨["sample"], ["consume"], [], [.num 3]⟩
    (fun _ => True)
  refine ⟨?tokens, ?items, ?members, ?library, ?unit,
    ?lexed, ?parsed, ?resolved, ?kept, ?found, ?elaborated, ?lowered⟩
  case lexed => cbv
  case parsed => cbv
  case resolved => cbv
  case kept => trivial
  case found => cbv
  case elaborated => cbv
  case lowered => cbv

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
