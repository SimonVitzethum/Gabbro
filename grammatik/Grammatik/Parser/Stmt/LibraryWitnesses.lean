module

public import Grammatik.Logik.Vertraege.Uebersetzung
public import Grammatik.Parser.Print.Stmt
public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil2
public import Grammatik.Parser.Stmt.LibraryFixtures
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
    beqTopStmt (parseTopStmt (druckAnw (.lcall call))) (.ok (.lcall call)) = true ∧
    beqTopStmt (parseTopStmt (druckAnw (.bindLib false "x" none call)))
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
    beqTopStmt (parseTopStmt (druckAnw (.lcall call))) (.ok (.lcall call)) = true := by
  decide +kernel

theorem tQual : beqTopTief (parseTopTief ttQual)
    (.ok [.transT "a::sum"
      { art := "", name := "build",
        params := [("region", .atom "SumTab")],
        res := .some (.atom "SumTab"), fehler := .none,
        klauseln := [.effs [.pure], .cost (.lit 8),
          .drops (.field (.variable "region") "v")] }
      (.block [] (.some (.ret (.some (.variable "region")))))]) = true := by
  decide

/-- The same members select module `b` under its qualifier. -/
theorem translation_qual_b_zeuge :
    (libraryDecl translationQualMembers ⟨["b"], ["b::consume"], [], [.num 3, .num 5]⟩).toOption.isSome = true := by
  decide +kernel

/-- An unknown qualifier refuses: no declaration matches. -/
theorem translation_qual_unbekannt_zeuge :
    (libraryDecl translationQualMembers ⟨["x"], ["consume"], [], [.num 3, .num 5]⟩).toOption.isNone = true := by
  decide +kernel

/-- An empty path refuses by name: the reader never produces one. -/
theorem translation_leer_verweigert_zeuge :
    (libraryDecl translationQualMembers ⟨[], ["a::consume"], [], []⟩).toOption.isNone = true := by
  decide +kernel

theorem translation_doppelt_verweigert_zeuge :
    (libraryDecl doppeltMembers ⟨["m"], ["consume"], [], []⟩).toOption.isNone = true := by
  decide

theorem translation_ohne_translator_zeuge :
    (libraryDecl ohneTranslatorMembers ⟨["m"], ["solo"], [], []⟩).toOption.isNone = true := by
  decide

/-- The recursive body calls, so `TranslationDecl.noCalls` is unprovable: the general-map path
    is refused under `allgemeineAbbildungVerweigert`. -/
theorem translation_rek_verweigert_zeuge :
    ((befund translationRekLowered.1 ⟨0, by decide +kernel⟩).rufe == []) = false := by
  decide +kernel

end Gabbro.Grammatik.Uebersetzung
