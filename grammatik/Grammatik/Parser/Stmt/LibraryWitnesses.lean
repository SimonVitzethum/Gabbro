module

public import Grammatik.Logik.Vertraege.Uebersetzung
public import Grammatik.Parser.Print.Stmt
public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil2
public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil2a
public import Grammatik.Parser.Stmt.LibraryFixtures
import all Grammatik.Parser.Stmt.LibraryFixtures
import all Grammatik.Parser.Stmt.LibraryQualifiedFixtures
import all Grammatik.Parser.Stmt.LibraryTranslationFixtures
import all Grammatik.Parser.Stmt.LibraryFixtureProofs
import Init.Data.String.Lemmas.Intercalate
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

/-! ## Parser-level library witnesses: losslessness, site identity and selection refusals.

    Fixtures live in `LibraryFixtures.lean`, certificates in `LibraryCertificates.lean`, and the
    connected export witness in `LibraryExport.lean`. -/

/-- Reordering ordinary arguments or changing a region preserves its token kinds and changes the
    source call's identity. Both call forms share that identity; nested regions survive printing. -/
theorem library_lossless_zeuge :
    let call : SLibraryCall := ⟨["sample"], ["consume"], [.lit 7, .variable "n"],
      [.zeichen "{", .num 3, .zeichen "}", .text "5"]⟩
    beqTopStmt (parseTopStmt (druckAnw (.lcall call) ++ [.ende])) (.ok (.lcall call)) = true ∧
    beqTopStmt (parseTopStmt (druckAnw (.bindLib false "x" none call) ++ [.ende]))
      (.ok (.bindLib false "x" none call)) = true ∧
    beqSLibraryCall call { call with args := [.variable "n", .lit 7] } = false ∧
    beqSLibraryCall call { call with region := [.num 3, .num 5] } = false := by
  decide +kernel

/-- The generic round-trip theorems apply jointly to a call with an actual argument and region. -/
theorem library_round_zeuge :
    let call : SLibraryCall := ⟨["sample"], ["consume"], [.lit 7], [.num 3]⟩
    LibraryCallGut call ∧ AnwBein (.lcall call) ∧ AnwBein (.bindLib false "value" none call) := by
  let call : SLibraryCall := ⟨["sample"], ["consume"], [.lit 7], [.num 3]⟩
  have good : LibraryCallGut call := by
    refine ⟨by decide, by decide, ?_, ?_⟩
    · intro value member
      simp only [call, List.mem_cons, List.not_mem_nil, or_false] at member
      subst value
      exact ⟨legs_tok _ rfl, rfl⟩
    · intro rest
      rfl
  exact ⟨good, anw_lcall call good, anw_bindLib false "value" (by decide) none call trivial good⟩

/-- Two source occurrences keep distinct regions; selecting one cannot reuse the other's input. -/
theorem library_site_identity_zeuge :
    let first : SLibraryCall := ⟨["sample"], ["consume"], [], [.num 3, .num 5]⟩
    let second : SLibraryCall := ⟨["sample"], ["consume"], [], [.num 2, .num 7]⟩
    let body := SAnw.block [.lcall first, .lcall second] none
    (libraryCallAt [0] body).map (fun call => beqSLibraryCall call first) = some true ∧
    (libraryCallAt [1] body).map (fun call => beqSLibraryCall call second) = some true ∧
    (libraryCallAt [1] body).map (fun call => beqSLibraryCall call first) = some false := by
  decide +kernel

/-- A qualified library call prints and parses back with its paths intact. -/
theorem library_qualifiziert_rund_zeuge :
    let call : SLibraryCall := ⟨["m", "lib"], ["f"], [.lit 7], [.num 3]⟩
    beqTopStmt (parseTopStmt (druckAnw (.lcall call) ++ [.ende])) (.ok (.lcall call)) = true := by
  decide +kernel

-- Reuse the actual scanner and phase certificates. Only their normalized
-- parser/member values are inspected by the selection witnesses below.
attribute [local cbv_eval] String.intercalate_singleton

private def qualifiedItems :
    { items : List SItemTief // parseTopTief qualPhaseTokens = .ok items } := by
  refine ⟨?items, ?parsed⟩
  case parsed => cbv <;> exact Eq.refl _

private def qualifiedMembers :
    { members : List SItemTief //
      Aufloesung.loeseL (Aufloesung.quelle qualifiedItems.val) [] qualifiedItems.val = members } := by
  refine ⟨?members, ?resolved⟩
  case resolved => cbv <;> exact Eq.refl _

private theorem qualified_members_selected : translationQualMembers = qualifiedMembers.val := by
  have tokens : translationQualTokens = qualPhaseTokens := by
    unfold translationQualTokens
    rw [translation_qual_text, String.toList_ofList, qual_lexed]
    rfl
  have items : translationQualItems = qualifiedItems.val := by
    unfold translationQualItems
    rw [tokens]
    exact congrArg (fun result : Except String (List SItemTief) => result.toOption.getD [])
      qualifiedItems.property
  unfold translationQualMembers
  rw [items]
  exact qualifiedMembers.property

-- Certify the existing finite parser separately; its inferred result is data,
-- not a supplied AST and not a second translator parser.
private def qualifiedTranslator :
    { items : List SItemTief // parseTopTief ttQual = .ok items } := by
  refine ⟨?items, ?parsed⟩
  case parsed => cbv <;> exact Eq.refl _

theorem tQual : beqTopTief (parseTopTief ttQual)
    (.ok [.transT "a::sum"
      { art := "", name := "build",
        params := [("region", .atom "SumTab")],
        res := .some (.atom "SumTab"), fehler := .none,
        klauseln := [.effs [.pure], .cost (.lit 8),
          .drops (.field (.variable "region") "v")] }
      (.block [] (.some (.ret (.some (.variable "region")))))]) = true := by
  rw [qualifiedTranslator.property]
  cbv

private def qualified_b_selected :
    { library : ULibrary // libraryDecl qualifiedMembers.val
      ⟨["b"], ["b::consume"], [], [.num 3, .num 5]⟩ = .ok library } := by
  refine ⟨?library, ?selected⟩
  case selected => cbv <;> exact Eq.refl _

private theorem qualified_unknown :
    libraryDecl qualifiedMembers.val ⟨["x"], ["consume"], [], [.num 3, .num 5]⟩ =
      .error "C02: library function is unresolved" := by cbv

-- The empty-path refusal precedes any member lookup, for arbitrary members.
private theorem library_empty_path (members : List SItemTief) (function : List String)
    (args : List SExpr) (region : List Token) :
    libraryDecl members ⟨[], function, args, region⟩ =
      .error "C02: library call without library path" := rfl

private theorem duplicate_selected :
    libraryDecl doppeltMembers ⟨["m"], ["consume"], [], []⟩ =
      .error "C02: library function is ambiguous" := by cbv

private theorem translator_absent :
    libraryDecl ohneTranslatorMembers ⟨["m"], ["solo"], [], []⟩ =
      .error "C02: library function has no translator" := by cbv

/-- The same members select module `b` under its qualifier. -/
theorem translation_qual_b_zeuge :
    (libraryDecl translationQualMembers ⟨["b"], ["b::consume"], [], [.num 3, .num 5]⟩).toOption.isSome = true := by
  rw [qualified_members_selected, qualified_b_selected.property]
  rfl

/-- An unknown qualifier refuses: no declaration matches. -/
theorem translation_qual_unbekannt_zeuge :
    (libraryDecl translationQualMembers ⟨["x"], ["consume"], [], [.num 3, .num 5]⟩).toOption.isNone = true := by
  rw [qualified_members_selected, qualified_unknown]
  rfl

/-- An empty path refuses by name: the reader never produces one. -/
theorem translation_leer_verweigert_zeuge :
    (libraryDecl translationQualMembers ⟨[], ["a::consume"], [], []⟩).toOption.isNone = true := by
  rw [library_empty_path]
  rfl

theorem translation_doppelt_verweigert_zeuge :
    (libraryDecl doppeltMembers ⟨["m"], ["consume"], [], []⟩).toOption.isNone = true := by
  rw [duplicate_selected]
  rfl

theorem translation_ohne_translator_zeuge :
    (libraryDecl ohneTranslatorMembers ⟨["m"], ["solo"], [], []⟩).toOption.isNone = true := by
  rw [translator_absent]
  rfl

-- The recursive fixture already certifies every source phase and lowering.
-- Select its parser output equation rather than re-entering its public lexer
-- and parser getters while proving facts about the typed program.
attribute [local cbv_opaque] rekPhaseItems elabFn uFloatLimit
  lowStufe lowSeqL lowStructL lowEndL
attribute [local cbv_eval] rek_items LibraryFixtureProofs.empty_function
  LibraryFixtureProofs.seq_succ lowStructL_succ lowEndL_succ
  lowStufe_seq lowStufe_struct lowStufe_ende

private theorem recursive_members_selected : translationRekMembers = rekPhaseMembers := by
  have tokens : translationRekTokens = rekPhaseTokens := by
    unfold translationRekTokens
    rw [translation_rek_text, String.toList_ofList, rek_lexed]
    rfl
  have parsed : parseTopTief rekPhaseTokens = .ok rekPhaseItems :=
    except_ok_get rek_parse_success
  have items : translationRekItems = rekPhaseItems := by
    unfold translationRekItems
    rw [tokens, parsed]
    rfl
  unfold translationRekMembers
  rw [items]
  rfl

private def recursiveLibrary :
    { library : ULibrary // libraryDecl rekPhaseMembers
      ⟨["sample"], ["consume"], [], [.num 3]⟩ = .ok library } := by
  refine ⟨?library, ?found⟩
  case found => cbv <;> exact Eq.refl _

private theorem recursive_library_selected : rekPhaseLibrary = recursiveLibrary.val :=
  Except.ok.inj ((except_ok_get rek_library_success).symm.trans recursiveLibrary.property)

private def recursiveUnit :
    { unit : UProg // elabU (pre108 (translatorItems rekPhaseMembers recursiveLibrary.val)) =
      .ok unit } := by
  refine ⟨?unit, ?elaborated⟩
  case elaborated => cbv <;> exact Eq.refl _

private theorem recursive_unit_selected : rekPhaseUnit = recursiveUnit.val := by
  have produced : elabU (pre108 (translatorItems rekPhaseMembers rekPhaseLibrary)) =
      .ok rekPhaseUnit := except_ok_get rek_elab_success
  rw [recursive_library_selected] at produced
  exact Except.ok.inj (produced.symm.trans recursiveUnit.property)

private theorem recursive_lowered : (lowerAllg recursiveUnit.val).toOption.isSome = true := by
  exact Eq.mp (congrArg (fun unit : UProg => (lowerAllg unit).toOption.isSome = true)
    recursive_unit_selected) rek_lower_success

private theorem recursive_positive : 0 < recursiveUnit.val.fns.length := by cbv

private def recursiveFunction :
    { value : EnsTy recursiveUnit.val ⟨0, recursive_positive⟩ ×
        RumpTy recursiveUnit.val ⟨0, recursive_positive⟩ ×
        ReqTy recursiveUnit.val ⟨0, recursive_positive⟩ //
      lowerFnAt recursiveUnit.val ⟨0, recursive_positive⟩ = .ok value } := by
  refine ⟨?value, ?lowered⟩
  case lowered => cbv <;> exact Eq.refl _

private theorem recursive_body_calls :
    ((befE false false recursiveFunction.val.2.1).rufe == []) = false := by cbv

-- The assembler is left abstract: its existing field theorem supplies the
-- exact body. Only the canonical function result and its call metadata have
-- been evaluated; no complete lowerAllg program is reduced here.
private theorem first_function_calls {u : UProg}
    (image : Programm (declOf u) × List (declOf u).Fn)
    (emitted : lowerAllg u = .ok image) (positive : 0 < u.fns.length)
    (result : { value : EnsTy u ⟨0, positive⟩ × RumpTy u ⟨0, positive⟩ ×
        ReqTy u ⟨0, positive⟩ // lowerFnAt u ⟨0, positive⟩ = .ok value })
    (calls : ((befE false false result.val.2.1).rufe == []) = false) :
    ((befund image.1 ⟨0, positive⟩).rufe == []) = false := by
  obtain ⟨value, origin, _, body, _⟩ :=
    lowerAllg_fields u image.1 image.2 emitted ⟨0, positive⟩
  have same : value = result.val := Except.ok.inj (origin.symm.trans result.property)
  subst value
  change ((befE false false (image.1.rumpf ⟨0, positive⟩)).rufe == []) = false
  rw [body]
  exact calls

private theorem recursive_program_calls :
    ∃ positive : 0 < translationRekUnit.fns.length,
      ((befund translationRekLowered.1 ⟨0, positive⟩).rufe == []) = false := by
  have facts := LibraryFixtureProofs.certifyData translationRekMembers
    ⟨["sample"], ["consume"], [], [.num 3]⟩ translation_rek_library_zeuge
    (fun _ unit image => ∃ positive : 0 < unit.fns.length,
      ((befund image.1 ⟨0, positive⟩).rufe == []) = false)
    recursiveLibrary.val recursiveUnit.val
    (by rw [recursive_members_selected]; exact recursiveLibrary.property)
    (by rw [recursive_members_selected]; exact recursiveUnit.property)
    recursive_lowered
    ⟨recursive_positive, first_function_calls _ (except_ok_get recursive_lowered)
      recursive_positive recursiveFunction recursive_body_calls⟩
    translation_rek_lower_zeuge
  exact facts.2

private theorem recursive_public_positive : 0 < translationRekUnit.fns.length :=
  recursive_program_calls.elim (fun positive _ => positive)

/-- The recursive body calls, so `TranslationDecl.noCalls` is unprovable: the general-map path
    is refused under `allgemeineAbbildungVerweigert`. -/
theorem translation_rek_verweigert_zeuge :
    ((befund translationRekLowered.1 ⟨0, by exact recursive_public_positive⟩).rufe == []) = false := by
  obtain ⟨positive, calls⟩ := recursive_program_calls
  exact calls

end Gabbro.Grammatik.Uebersetzung
