module

public import Grammatik.Logik.Vertraege.Uebersetzung
public import Grammatik.Parser.Stmt.LibraryFixtureProofs
import Grammatik.Parser.Stmt.LibraryFixtureScanning
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

-- These translators have no statement prefix. Select that actual reader
-- equation before normalization can construct the unused million-fuel mutual.
private theorem empty_row (tabs : List UTab) (heads : List UFnKopf)
    (fuel : Nat) (ctx : UCtx) :
    uAnwReihe tabs heads (fuel + 1) ctx [] = .ok ([], ctx) := by
  simp only [uAnwReihe]

theorem LibraryFixtureProofs.empty_function (ctx : UCtx) (heads : List UFnKopf)
    (clauses : List SKlausel) (ending : Option SEnde) :
    elabFn ctx heads clauses (.block [] ending) = (do
      let (gives, needs) ← elabKlauseln ctx clauses
      let (beforeFold, ctxEnd, ending) ← expandFoldEnd ctx ending
      let (beforeCall, ctxReturn, returning) ← expandReturnCall ctxEnd heads ending
      let result ← uEnde ctxReturn returning
      pure (gives, needs, beforeFold ++ beforeCall, result)) := by
  simp only [elabFn, empty_row, List.getLast?_nil, Bool.and_false,
    Bool.false_eq_true, ite_false, List.nil_append, bind, Except.bind, pure, Except.pure]
  repeat' first | rfl | split
  all_goals simp_all <;> subst_vars <;> simp_all

attribute [local cbv_opaque] elabFn
attribute [local cbv_eval] empty_function

/-- The actual statement dispatcher reads both ordered array elements and
    their nested indices, retaining the untouched trailing token. -/
theorem translation_array_return_parser (fuel : Nat) (rest : List Token) :
    parseStmt (fuel + 128)
      ([.wort "return", .zeichen "[", .ident "region", .zeichen "[", .num 1,
       .zeichen "]", .zeichen ",", .ident "region", .zeichen "[", .num 0,
       .zeichen "]", .zeichen "]", .zeichen ";"] ++ rest) =
      .ok (.ret (some (.ext .array []
        [.index (.variable "region") (.lit 1), .index (.variable "region") (.lit 0)])),
        rest) := by cbv

/-- A soft-keyword indexed place keeps its assignment form when it is not
    an array-valued return. No other statement head changes classification. -/
theorem translation_return_place_parser (fuel : Nat) :
    parseStmt (fuel + 128)
      [.wort "return", .zeichen "[", .num 0, .zeichen "]", .zeichen "=", .num 1,
       .zeichen ";", .ende] =
      .ok (.set (.index (.variable "return") (.lit 0)) "=" (.lit 1), [.ende]) := by cbv

-- Preserve every previously successful indexed soft-keyword place, not only
-- the concrete assignment above, including its exact continuation and fuel.
private theorem return_place_preserved (fuel : Nat) (tail : List Token)
    (result : SAnw × List Token)
    (placed : parsePlatzStmt fuel (.wort "return" :: .zeichen "[" :: tail) = .ok result) :
    parseStmt (fuel + 1) (.wort "return" :: .zeichen "[" :: tail) = .ok result := by
  cases returned : parseRueck fuel (.zeichen "[" :: tail) <;>
    simp only [parseStmt, returned, placed]

attribute [local cbv_eval] translation_array_return_parser

-- Reduce only the selected operation of the canonical fuel record. Evaluating
-- its unused fields eagerly would construct all 100000 recursive levels.
theorem LibraryFixtureProofs.seq_succ (u : UProg) (caller : Fin u.fns.length) (n : Nat)
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
private def translationChunks (reverse : Bool) : List LibraryFixtureScanning.Chunk :=
  [LibraryFixtureScanning.Chunk.moduleSample, .tableTwo, .slot, .libraryHead, .libraryTail,
    .translatorHead, .inputTwo, .outputTwo, .effects] ++
  [if reverse then LibraryFixtureScanning.Chunk.reverseResult else LibraryFixtureScanning.Chunk.plainResult] ++
  [LibraryFixtureScanning.Chunk.callerHead, .callSample, .valuesTwo, .close]

private def translationPhaseTokens (reverse : Bool) : List Token :=
  LibraryFixtureScanning.tokens (translationChunks reverse)

private theorem translation_lexed (reverse : Bool) :
    lexL (translationCharacters reverse) = .ok (translationPhaseTokens reverse) := by
  have source : translationCharacters reverse =
      LibraryFixtureScanning.characters (translationChunks reverse) := by cases reverse <;> rfl
  rw [source]
  exact LibraryFixtureScanning.lex_chunks (translationChunks reverse) (by cases reverse <;> decide +kernel)

-- These are ordinary canonical parser data, connected by the full success
-- equations below. Later projections consume those equations, not the parser again.
def LibraryFixtureProofs.parsedFixture (count : Nat) (result : SExpr) (values : List Token) : List SItemTief :=
  let scalar := STyp.range (.atom "u8") (.lit 0) (.lit 10) false
  let region := STyp.array scalar (.lit count)
  [.modT "sample"
    [.tableT "Rows" none (some (.lit count)) none none false
      [.tSlot [⟨"v", scalar, none, none, none, false, false⟩]],
     .fnT {
       art := "library", name := "consume", params := [("p", .ptr "normal" "r" (.atom "Rows"))],
       res := none, fehler := none, klauseln := [.load ["Rows"]] } (.block [] (some (.ret none))),
     .transT "consume" {
       art := "", name := "build", params := [("region", region)],
       res := some region, fehler := none, klauseln := [.effs [.pure]] }
       (.block [] (some (.ret (some result)))),
     .fnT translationCaller (.block [.lcall ⟨["sample"], ["consume"], [], values⟩]
       (some (.ret none)))]]

private def translationResult (reverse : Bool) : SExpr :=
  if reverse then .ext .array []
    [.index (.variable "region") (.lit 1), .index (.variable "region") (.lit 0)]
  else .variable "region"

private theorem translation_parsed (reverse : Bool) :
    parseTopTief (translationPhaseTokens reverse) =
      .ok (parsedFixture 2 (translationResult reverse) [.num 3, .num 5]) := by
  cases reverse <;> cbv

private theorem translation_parse_success (reverse : Bool) :
    (parseTopTief (translationPhaseTokens reverse)).toOption.isSome = true := by
  rw [translation_parsed]
  rfl

private def translationPhaseItems (reverse : Bool) : List SItemTief :=
  (parseTopTief (translationPhaseTokens reverse)).toOption.get (translation_parse_success reverse)

private theorem translation_items (reverse : Bool) :
    translationPhaseItems reverse = parsedFixture 2 (translationResult reverse) [.num 3, .num 5] := by
  simp only [translationPhaseItems, translation_parsed]
  rfl

attribute [local cbv_opaque] translationPhaseItems
attribute [local cbv_eval] translation_items

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
    translation_lexed reverse, except_ok_get (translation_parse_success reverse),
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


-- Compute only over the already certified phase values. The result packages
-- the complete typed image, including execution for every by-value input.
private theorem translation_phase_data (reverse : Bool) :
    DeclarationData (translationPhaseLibrary reverse) (translationPhaseUnit reverse)
      ((lowerAllg (translationPhaseUnit reverse)).toOption.get (translation_lower_success reverse))
      translationSchema (fun input => if reverse then fun index => input index.rev else input) := by
  cases reverse with
  | false =>
    refine certifyResults (translationPhaseMembers false) translationCall
      (fun library unit image => DeclarationData library unit image translationSchema
        (fun input => input)) ?_ (translation_library_success false)
      (translation_elab_success false) (translation_lower_success false)
    refine ⟨?libraryFalse, ?foundFalse, ?unitFalse, ?madeFalse, ?imageDataFalse⟩
    case foundFalse => cbv <;> exact Eq.refl _
    case madeFalse => cbv <;> exact Eq.refl _
    case imageDataFalse => library_emitted
  | true =>
    refine certifyResults (translationPhaseMembers true) translationCall
      (fun library unit image => DeclarationData library unit image translationSchema
        (fun input index => input index.rev)) ?_ (translation_library_success true)
      (translation_elab_success true) (translation_lower_success true)
    refine ⟨?libraryTrue, ?foundTrue, ?unitTrue, ?madeTrue, ?imageDataTrue⟩
    case foundTrue => cbv <;> exact Eq.refl _
    case madeTrue => cbv <;> exact Eq.refl _
    case imageDataTrue => library_emitted

-- One shared opaque proof for metadata consumers. The selected phase value
-- stays private; no new data view of the source or resolver is exported.
private theorem translation_library_selected (reverse : Bool) :
    translationMembers reverse = translationPhaseMembers reverse ∧
      translationLibrary reverse = translationPhaseLibrary reverse := by
  have members : translationMembers reverse = translationPhaseMembers reverse := by
    simp only [translationMembers, translationItems, translationTokens, translation_text,
      String.toList_ofList, translation_lexed, translationPhaseMembers, translationPhaseItems,
      translation_parsed, Except.toOption, Option.getD_some] <;> rfl
  refine ⟨members, ?_⟩
  apply Except.ok.inj
  exact (except_ok_get (translation_library_exists reverse)).symm.trans
    (by rw [members]; exact except_ok_get (translation_library_success reverse))

/-- Full phase success and typed image facts for the public selected values.
    The substitutions happen before any finite index or result projection. -/
theorem translation_export_data (reverse : Bool) :
    elabU (pre108 (translatorItems (translationMembers reverse) (translationLibrary reverse))) =
      .ok (translationUnit reverse) ∧
    DeclarationData (translationLibrary reverse) (translationUnit reverse) (translationLowered reverse)
      translationSchema (fun input => if reverse then fun index => input index.rev else input) := by
  have members := (translation_library_selected reverse).1
  exact certifyData (translationMembers reverse) translationCall (translation_library_exists reverse)
    (fun library unit image => DeclarationData library unit image translationSchema
      (fun input => if reverse then fun index => input index.rev else input))
    (translationPhaseLibrary reverse) (translationPhaseUnit reverse)
    (by rw [members]; exact except_ok_get (translation_library_success reverse))
    (by rw [members]; exact except_ok_get (translation_elab_success reverse))
    (translation_lower_success reverse) (translation_phase_data reverse) (translation_lower_exists reverse)

/-- The selected source declaration supplies its actual name and omitted
    payload arity; expansion does not inspect the elaborated program. -/
theorem translation_library_shape (reverse : Bool) :
    (translationLibrary reverse).function.name = "consume" ∧
    translationCall.args.length + 1 = (translationLibrary reverse).function.params.length := by
  rw [(translation_library_selected reverse).2]
  cases reverse <;> constructor <;> cbv

/-- Source-selected names and bodies are compared after selection success,
    without reevaluating the public lexical/default graph. -/
theorem translation_library_change_data :
    strEq (translationLibrary false).translator.name (translationLibrary true).translator.name = true ∧
    beqSAnw (translationLibrary false).translatorBody (translationLibrary true).translatorBody = false := by
  rw [(translation_library_selected false).2, (translation_library_selected true).2]
  constructor <;> cbv

end Gabbro.Grammatik.Uebersetzung
