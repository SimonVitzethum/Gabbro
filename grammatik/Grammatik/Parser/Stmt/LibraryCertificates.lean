module

public import Grammatik.Logik.Vertraege.Uebersetzung
public import Grammatik.Parser.Stmt.LibraryFixtures
import Grammatik.Parser.Stmt.LibraryFixtureProofs
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

/-- Joint declaration fixture: source identity, exact typed exporter, bounded call graph and
    immutable by-value array signature all hold for both translator bodies. -/
def translationDeclaration (reverse : Bool) : TranslationDecl (translationSource reverse) (translationUnit reverse) where
  library := translationLibrary reverse
  resolved := except_ok_get (translation_library_exists reverse)
  elaborated := (translation_export_data reverse).1
  program := (translationLowered reverse).1
  functions := (translationLowered reverse).2
  lowered := except_ok_get (translation_lower_exists reverse)
  translator := ⟨0, (translation_export_data reverse).2.positive⟩
  translatorName := (translation_export_data reverse).2.name
  schema := translationSchema
  parameters := (translation_export_data reverse).2.parameters
  outputType := translationSchema.ty
  result := (translation_export_data reverse).2.result
  immutable := .arr _ _ (.int _ _)
  noCalls := (translation_export_data reverse).2.noCalls
  noIndirectCalls := (translation_export_data reverse).2.noIndirectCalls
  bounded := (translation_export_data reverse).2.bounded
  noCycle := (translation_export_data reverse).2.noCycle

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
  execution := by
    intro oracle passes world
    have executed := (translation_export_data reverse).2.execution oracle passes world (translationInput reverse)
    have output : (if reverse then fun index => translationInput reverse index.rev else translationInput reverse) =
        translationOutput reverse := by
      cases reverse with
      | false => rfl
      | true =>
        funext index
        rcases index with ⟨position, bound⟩
        have choices : position = 0 ∨ position = 1 := by change position < 2 at bound; omega
        rcases choices with rfl | rfl <;> rfl
    rw [output] at executed
    exact executed

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
  exact translation_library_change_data

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
  have equal := answer_injective (translationDeclaration true) equal
  have first := congrArg (fun value => (value ⟨0, by decide⟩).n) equal
  have distinct : (3 : Int) ≠ 5 := by decide
  exact distinct first

/-- Count, range and token-schema errors all refuse before execution. -/
theorem translation_decoder_refusals_zeuge :
    (decodeIntegerRows (declOf (translationUnit false)) translationSchema [.num 3]).isNone = true ∧
    (decodeIntegerRows (declOf (translationUnit false)) translationSchema [.num 3, .num 11]).isNone = true ∧
    (decodeIntegerRows (declOf (translationUnit false)) translationSchema [.text "3 5"]).isNone = true := by
  decide +kernel

theorem translation_measure_zeuge (passes : Nat) (Q : AxEns (declOf (translationUnit true)))
    (S : SperrInv (declOf (translationUnit true)))
    (T : (declOf (translationUnit true)).Tab ⊕ (declOf (translationUnit true)).Glob → Prop) :
    MassPflicht (translationDeclaration true).program passes Q S T Mass.leer
      (zykS (translationDeclaration true).program (translationDeclaration true).functions)
      (translationDeclaration true).translator :=
  translation_measure (translationDeclaration true) passes Q S T

/-- Joint qualified declaration fixture: the qualifier selects module `a` through typed export,
    bounded call graph and immutable by-value array signature. -/
def translationQualDeclaration : TranslationDecl translationQualSource translationQualUnit where
  library := translationQualLibrary
  resolved := except_ok_get translation_qual_library_zeuge
  elaborated := translation_qual_export_data.1
  program := translationQualLowered.1
  functions := translationQualLowered.2
  lowered := except_ok_get translation_qual_lower_zeuge
  translator := ⟨0, translation_qual_export_data.2.positive⟩
  translatorName := translation_qual_export_data.2.name
  schema := translationSchema
  parameters := translation_qual_export_data.2.parameters
  outputType := translationSchema.ty
  result := translation_qual_export_data.2.result
  immutable := .arr _ _ (.int _ _)
  noCalls := translation_qual_export_data.2.noCalls
  noIndirectCalls := translation_qual_export_data.2.noIndirectCalls
  bounded := translation_qual_export_data.2.bounded
  noCycle := translation_qual_export_data.2.noCycle

def translationQualInput : Wert (declOf translationQualUnit) translationSchema.ty :=
  fun index => ([⟨3, by decide, by decide⟩, ⟨5, by decide, by decide⟩] : List (Zahl 0 10)).get index

/-- A complete exact-execution certificate for the qualified selection. -/
def translationQualCertificate : TranslationCertificate translationQualDeclaration where
  input := translationQualInput
  decoded := by rfl
  output := translationQualInput
  fuel := 1
  execution := by
    intro oracle passes world
    exact translation_qual_export_data.2.execution oracle passes world translationQualInput

/-- The per-site payload of the identity translation: site `[0]`, content the certified output. -/
def translationPayload : LibraryPayload (translationCertificate false) where
  site := [0]
  amStandort := rfl
  inhalt := (translationCertificate false).output
  vollstaendig := rfl

/-- Every payload row is the certified row. -/
theorem translationPayload_zeilen_zeuge :
    (translationPayload.inhalt ⟨0, by decide⟩).n = 3 ∧ (translationPayload.inhalt ⟨1, by decide⟩).n = 5 := by
  constructor <;> rfl

/-- Payloads are per site: this one is not at site `[1]`. -/
theorem translationPayload_standort_zeuge : translationPayload.site ≠ [1] := by decide

/-- The certified `lcall` expansion: ordinary call, payload last, caller arity met. -/
def translationExpansion : LibraryExpansion translationPayload where
  nutzlastArg := .variable "sample_payload_0"
  aufruf := .call "consume" (translationCall.args ++ [.variable "sample_payload_0"])
  erweitert := Or.inl (by
    change .call "consume" (translationCall.args ++ [.variable "sample_payload_0"]) =
      .call (translationLibrary false).function.name (translationCall.args ++ [.variable "sample_payload_0"])
    rw [(translation_library_shape false).1])
  stelligkeit := by
    simpa only [List.length_append, List.length_singleton] using (translation_library_shape false).2

/-- The certified `bindLib` expansion: the ordinary call value bound as usual. -/
def translationExpansionBind : LibraryExpansion translationPayload where
  nutzlastArg := .variable "sample_payload_0"
  aufruf := .bind false "value" none (.call "consume" (translationCall.args ++ [.variable "sample_payload_0"]))
  erweitert := Or.inr ⟨false, "value", (none : Option STyp), by
    change .bind false "value" none
      (.call "consume" (translationCall.args ++ [.variable "sample_payload_0"])) =
      .bind false "value" none
        (.call (translationLibrary false).function.name (translationCall.args ++ [.variable "sample_payload_0"]))
    rw [(translation_library_shape false).1]⟩
  stelligkeit := by
    simpa only [List.length_append, List.length_singleton] using (translation_library_shape false).2

/-- Both expansions are ordinary: no library construct remains for the lowering. -/
theorem translationExpansion_ohne_zeuge :
    ohneBibliothekAnw translationExpansion.aufruf = true ∧
    ohneBibliothekAnw translationExpansionBind.aufruf = true :=
  ⟨libraryExpansion_ohneBibliothek translationExpansion,
   libraryExpansion_ohneBibliothek translationExpansionBind⟩

/-- The pre-expansion gate refuses products under the C01 name and callees under the C17 name. -/
theorem torZurErweiterung_zeuge :
    torZurErweiterung true true = .ok () ∧
    torZurErweiterung false true = .error produktZeilenVerweigert ∧
    torZurErweiterung true false = .error allgemeineAbbildungVerweigert := by
  exact ⟨rfl, rfl, rfl⟩

/-- The generated translator program is library-closed. -/
theorem translation_libraryB_zeuge :
    Gabbro.Grammatik.Zielsatz.libraryB (translationLowered false).1
      (translationLowered false).2 = true :=
  Gabbro.Grammatik.Zielsatz.libraryB_immer _ _

/-- The library admission holds on the generated program, through the checker binding. -/
theorem translation_libraryAdmission_zeuge :
    Gabbro.Grammatik.Zielsatz.LibraryAdmission (translationLowered false).1 :=
  (Gabbro.Grammatik.Zielsatz.libraryB_iff _ _).mp translation_libraryB_zeuge

end Gabbro.Grammatik.Uebersetzung
