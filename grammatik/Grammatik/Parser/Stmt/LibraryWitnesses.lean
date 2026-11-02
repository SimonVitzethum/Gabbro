module

public import Grammatik.Logik.Vertraege.Uebersetzung
public import Grammatik.Parser.Print.Stmt
public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil2
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

def translationCall : SLibraryCall := ⟨"sample", "consume", [], [.num 3, .num 5]⟩

def translationCaller : FnSig :=
  { art := "impl", name := "caller", params := [], res := none, fehler := none, klauseln := [] }

def translationCallerBody : SAnw := .block [.lcall translationCall] (some (.ret none))

/-- The exact caller is at member 3 and its call at statement path `[0]`. -/
def translationSource (reverse : Bool) : LibrarySource where
  characters := (translationText reverse).toList
  tokens := translationTokens reverse
  items := translationItems reverse
  lexed := by cases reverse <;> rfl
  parsed := by cases reverse <;> rfl
  callerIndex := 3
  caller := translationCaller
  callerBody := translationCallerBody
  atCaller := by cases reverse <;> rfl
  path := [0]
  call := translationCall
  atCall := rfl

theorem translation_library_exists (reverse : Bool) :
    (libraryDecl (translationMembers reverse) translationCall).toOption.isSome = true := by
  cases reverse <;> decide +kernel

def translationLibrary (reverse : Bool) : ULibrary :=
  (libraryDecl (translationMembers reverse) translationCall).toOption.get (translation_library_exists reverse)

def translationUnit (reverse : Bool) : UProg :=
  (elabU (pre108 (translatorItems (translationMembers reverse) (translationLibrary reverse)))).toOption.getD
    { tabs := [], locks := [], fns := [] }

theorem translation_lower_exists (reverse : Bool) :
    (lowerAllg (translationUnit reverse)).toOption.isSome = true := by
  cases reverse <;> decide +kernel

def translationLowered (reverse : Bool) :
    Programm (declOf (translationUnit reverse)) × List (declOf (translationUnit reverse)).Fn :=
  (lowerAllg (translationUnit reverse)).toOption.get (translation_lower_exists reverse)

def translationSchema : IntegerSchema := ⟨0, 10, 2⟩

/-- Joint declaration fixture: source identity, exact typed exporter, bounded call graph and
    immutable by-value array signature all hold for both translator bodies. -/
def translationDeclaration (reverse : Bool) : TranslationDecl (translationSource reverse) (translationUnit reverse) where
  library := translationLibrary reverse
  resolved := except_ok_get (translation_library_exists reverse)
  elaborated := by cases reverse <;> decide +kernel
  program := (translationLowered reverse).1
  functions := (translationLowered reverse).2
  lowered := except_ok_get (translation_lower_exists reverse)
  translator := ⟨0, by cases reverse <;> decide +kernel⟩
  translatorName := by cases reverse <;> rfl
  schema := translationSchema
  parameters := by cases reverse <;> rfl
  outputType := translationSchema.ty
  result := by cases reverse <;> rfl
  immutable := .arr _ _ (.int _ _)
  noCalls := by cases reverse <;> decide +kernel
  noIndirectCalls := by cases reverse <;> decide +kernel
  bounded := by cases reverse <;> decide +kernel
  noCycle := by
    intro callee
    rcases callee with ⟨index, bound⟩
    have zero : index = 0 := by
      cases reverse <;> change index < 1 at bound <;> omega
    subst index
    cases reverse <;> decide +kernel

def translationInput (reverse : Bool) : Wert (declOf (translationUnit reverse)) translationSchema.ty :=
  fun index => ([⟨3, by decide, by decide⟩, ⟨5, by decide, by decide⟩] : List (Zahl 0 10)).get index

def translationOutput (reverse : Bool) : Wert (declOf (translationUnit reverse)) translationSchema.ty :=
  if reverse then
    fun index => ([⟨5, by decide, by decide⟩, ⟨3, by decide, by decide⟩] : List (Zahl 0 10)).get index
  else translationInput reverse

/-- A complete exact-execution certificate, including the nonidentity bounded map. -/
def translationCertificate (reverse : Bool) : TranslationCertificate (translationDeclaration reverse) where
  input := translationInput reverse
  decoded := by cases reverse <;> rfl
  output := translationOutput reverse
  fuel := 1
  execution := by intro oracle passes world; cases reverse <;> rfl

theorem translation_result_unique_zeuge :
    ((translationCertificate false).output ⟨0, by decide⟩).n = 3 ∧
    ((translationCertificate true).output ⟨0, by decide⟩).n = 5 := by
  constructor <;> rfl

/-- A well-typed identity output is wrong for the source-selected reversing translator. -/
theorem translation_wrong_output_zeuge :
    (translationOutput true ⟨0, by decide⟩).n ≠ (translationInput true ⟨0, by decide⟩).n := by decide +kernel

theorem translation_body_change_zeuge :
    strEq (translationLibrary false).translator.name (translationLibrary true).translator.name = true ∧
    beqSAnw (translationLibrary false).translatorBody (translationLibrary true).translatorBody = false := by
  decide +kernel

/-- Typing alone cannot certify identity output for the reversing source body. -/
theorem translation_wrong_execution_zeuge
    (oracle : Orakel (declOf (translationUnit true))) (passes : Nat)
    (world : World (declOf (translationUnit true))) :
    rufAt (translationDeclaration true).program oracle passes 1
      (translationDeclaration true).translator world
      ((translationDeclaration true).arguments (translationInput true)) ≠
      .ok world ((translationDeclaration true).answer (translationInput true)) := by
  intro wrong
  have equal := translation_result_unique (translationCertificate true) oracle passes world _ wrong
  change translationInput true = translationOutput true at equal
  have first := congrArg (fun value => (value ⟨0, by decide⟩).n) equal
  have distinct : (3 : Int) ≠ 5 := by decide
  exact distinct first

/-- Count, range and token-schema errors all refuse before execution. -/
theorem translation_decoder_refusals_zeuge :
    (decodeIntegerRows (declOf (translationUnit false)) translationSchema [.num 3]).isNone = true ∧
    (decodeIntegerRows (declOf (translationUnit false)) translationSchema [.num 3, .num 11]).isNone = true ∧
    (decodeIntegerRows (declOf (translationUnit false)) translationSchema [.text "3 5"]).isNone = true := by
  decide +kernel

/-- Reordering ordinary arguments or changing a region preserves its token kinds and changes the
    source call's identity. Both call forms share that identity; nested regions survive printing. -/
theorem library_lossless_zeuge :
    let call : SLibraryCall := ⟨"sample", "consume", [.lit 7, .variable "n"],
      [.zeichen "{", .num 3, .zeichen "}", .text "5"]⟩
    beqTopStmt (parseTopStmt (druckAnw (.lcall call))) (.ok (.lcall call)) = true ∧
    beqTopStmt (parseTopStmt (druckAnw (.bindLib false "x" none call)))
      (.ok (.bindLib false "x" none call)) = true ∧
    beqSLibraryCall call { call with args := [.variable "n", .lit 7] } = false ∧
    beqSLibraryCall call { call with region := [.num 3, .num 5] } = false := by
  decide +kernel

/-- The generic round-trip theorems apply jointly to a call with an actual argument and region. -/
theorem library_round_zeuge :
    let call : SLibraryCall := ⟨"sample", "consume", [.lit 7], [.num 3]⟩
    LibraryCallGut call ∧ AnwBein (.lcall call) ∧ AnwBein (.bindLib false "value" none call) := by
  let call : SLibraryCall := ⟨"sample", "consume", [.lit 7], [.num 3]⟩
  have good : LibraryCallGut call := by
    constructor
    · intro value member
      simp only [call, List.mem_cons, List.not_mem_nil, or_false] at member
      subst value
      exact ⟨legs_tok _ rfl, rfl⟩
    · intro rest
      rfl
  exact ⟨good, anw_lcall call good, anw_bindLib false "value" (by decide) none call trivial good⟩

/-- Two source occurrences keep distinct regions; selecting one cannot reuse the other's input. -/
theorem library_site_identity_zeuge :
    let first : SLibraryCall := ⟨"sample", "consume", [], [.num 3, .num 5]⟩
    let second : SLibraryCall := ⟨"sample", "consume", [], [.num 2, .num 7]⟩
    let body := SAnw.block [.lcall first, .lcall second] none
    (libraryCallAt [0] body).map (fun call => beqSLibraryCall call first) = some true ∧
    (libraryCallAt [1] body).map (fun call => beqSLibraryCall call second) = some true ∧
    (libraryCallAt [1] body).map (fun call => beqSLibraryCall call first) = some false := by
  decide +kernel

theorem translation_measure_zeuge (passes : Nat) (Q : AxEns (declOf (translationUnit true)))
    (S : SperrInv (declOf (translationUnit true)))
    (T : (declOf (translationUnit true)).Tab ⊕ (declOf (translationUnit true)).Glob → Prop) :
    MassPflicht (translationDeclaration true).program passes Q S T Mass.leer
      (zykS (translationDeclaration true).program (translationDeclaration true).functions)
      (translationDeclaration true).translator :=
  translation_measure (translationDeclaration true) passes Q S T

end Gabbro.Grammatik.Uebersetzung
