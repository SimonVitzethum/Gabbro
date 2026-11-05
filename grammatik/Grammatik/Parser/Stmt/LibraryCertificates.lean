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

-- Assemble records while the unit and image are abstract. Concrete consumers
-- supply whole phase certificates, never projections of a recomputed pipeline.
section PhaseCertificates
variable {source : LibrarySource} {unit : UProg} {library : ULibrary}
  {image : Programm (declOf unit) × List (declOf unit).Fn} {schema : IntegerSchema}
  {reorder : Wert (declOf unit) schema.ty → Wert (declOf unit) schema.ty}
  (data : DeclarationData library unit image schema reorder)
  (resolved : libraryDecl (Aufloesung.loeseL (Aufloesung.quelle source.items) [] source.items)
    source.call = .ok library)
  (elaborated : elabU (pre108 (translatorItems
    (Aufloesung.loeseL (Aufloesung.quelle source.items) [] source.items) library)) = .ok unit)
  (lowered : lowerAllg unit = .ok image)

def declarationFromData : TranslationDecl source unit where
  library := library
  resolved := resolved
  elaborated := elaborated
  program := image.1
  functions := image.2
  lowered := lowered
  translator := ⟨0, data.positive⟩
  translatorName := data.name
  schema := schema
  parameters := data.parameters
  outputType := schema.ty
  result := data.result
  immutable := .arr _ _ (.int _ _)
  noCalls := data.noCalls
  noIndirectCalls := data.noIndirectCalls
  bounded := data.bounded
  noCycle := data.noCycle

private theorem declarationFromData_library :
    (declarationFromData data resolved elaborated lowered).library = library := rfl

variable (input output : Wert (declOf unit) schema.ty)
  (decoded : decodeIntegerRows (declOf unit) schema source.call.region = some input)
  (produced : reorder input = output)

def certificateFromData :
    TranslationCertificate (declarationFromData data resolved elaborated lowered) where
  input := input
  decoded := decoded
  output := output
  fuel := 1
  execution := by
    intro oracle passes world
    have executed := data.execution oracle passes world input
    rw [produced] at executed
    exact executed

private theorem certificateFromData_input :
    (certificateFromData data resolved elaborated lowered input output decoded produced).input = input := rfl

private theorem certificateFromData_output :
    (certificateFromData data resolved elaborated lowered input output decoded produced).output = output := rfl

private theorem certificateFromData_fuel :
    (certificateFromData data resolved elaborated lowered input output decoded produced).fuel = 1 := rfl
end PhaseCertificates

private theorem certificate_rejects_other {source : LibrarySource} {unit : UProg}
    {declaration : TranslationDecl source unit} (certificate : TranslationCertificate declaration)
    (other : Wert (declOf unit) declaration.outputType) (different : certificate.output ≠ other)
    (oracle : Orakel (declOf unit)) (passes : Nat) (world : World (declOf unit)) :
    rufAt declaration.program oracle passes certificate.fuel declaration.translator world
      (declaration.arguments certificate.input) ≠ .ok world (declaration.answer other) := by
  intro executed
  have same := translation_result_unique certificate oracle passes world _ executed
  exact different (answer_injective declaration same).symm

-- Fixed row arithmetic is independent of the declaration's function carrier.
def sampleRows (D : Deklaration) (reverse : Bool) : Wert D translationSchema.ty :=
  if reverse then
    fun index => ([⟨5, by decide, by decide⟩, ⟨3, by decide, by decide⟩] : List (Zahl 0 10)).get index
  else
    fun index => ([⟨3, by decide, by decide⟩, ⟨5, by decide, by decide⟩] : List (Zahl 0 10)).get index

private theorem sampleRows_decoded (D : Deklaration) :
    decodeIntegerRows D translationSchema [.num 3, .num 5] = some (sampleRows D false) := rfl

private theorem sampleRows_reorder (D : Deklaration) (reverse : Bool) :
    (if reverse then fun index => sampleRows D false index.rev else sampleRows D false) =
      sampleRows D reverse := by
  cases reverse with
  | false => rfl
  | true =>
    funext index
    rcases index with ⟨position, bound⟩
    have choices : position = 0 ∨ position = 1 := by change position < 2 at bound; omega
    rcases choices with zero | one
    · subst position
      rfl
    · subst position
      rfl

private theorem sampleRows_first (D : Deklaration) :
    (sampleRows D false ⟨0, by decide⟩).n = 3 ∧
    (sampleRows D true ⟨0, by decide⟩).n = 5 := ⟨rfl, rfl⟩

private theorem sampleRows_second (D : Deklaration) :
    (sampleRows D false ⟨1, by decide⟩).n = 5 := rfl

private theorem sampleRows_wrong (D : Deklaration) :
    (sampleRows D true ⟨0, by decide⟩).n ≠ (sampleRows D false ⟨0, by decide⟩).n := by
  simpa only [(sampleRows_first D).1, (sampleRows_first D).2] using
    (by decide : (5 : Int) ≠ 3)

private theorem sampleRows_distinct (D : Deklaration) :
    sampleRows D true ≠ sampleRows D false := by
  intro same
  exact sampleRows_wrong D
    (congrArg (fun (value : Wert D translationSchema.ty) => (value ⟨0, by decide⟩).n) same)

private theorem sampleRows_refusals (D : Deklaration) :
    (decodeIntegerRows D translationSchema [.num 3]).isNone = true ∧
    (decodeIntegerRows D translationSchema [.num 3, .num 11]).isNone = true ∧
    (decodeIntegerRows D translationSchema [.text "3 5"]).isNone = true := by cbv

/-- Joint declaration fixture: source identity, exact typed exporter, bounded call graph and
    immutable by-value array signature all hold for both translator bodies. -/
def translationDeclaration (reverse : Bool) : TranslationDecl (translationSource reverse) (translationUnit reverse) :=
  declarationFromData (source := translationSource reverse) (translation_export_data reverse).2
    (except_ok_get (translation_library_exists reverse)) (translation_export_data reverse).1
    (except_ok_get (translation_lower_exists reverse))

def translationInput (reverse : Bool) : Wert (declOf (translationUnit reverse)) translationSchema.ty :=
  sampleRows (declOf (translationUnit reverse)) false

def translationOutput (reverse : Bool) : Wert (declOf (translationUnit reverse)) translationSchema.ty :=
  sampleRows (declOf (translationUnit reverse)) reverse

/-- A complete exact-execution certificate, including the nonidentity bounded map. -/
def translationCertificate (reverse : Bool) : TranslationCertificate (translationDeclaration reverse) :=
  certificateFromData (source := translationSource reverse) (translation_export_data reverse).2
    (except_ok_get (translation_library_exists reverse)) (translation_export_data reverse).1
    (except_ok_get (translation_lower_exists reverse)) (translationInput reverse) (translationOutput reverse)
    (by exact sampleRows_decoded (declOf (translationUnit reverse)))
    (by exact sampleRows_reorder (declOf (translationUnit reverse)) reverse)

private theorem translationCertificate_input (reverse : Bool) :
    (translationCertificate reverse).input = translationInput reverse := by rfl

private theorem translationCertificate_output (reverse : Bool) :
    (translationCertificate reverse).output = translationOutput reverse := by rfl

private theorem translationCertificate_fuel (reverse : Bool) :
    (translationCertificate reverse).fuel = 1 := by rfl

private theorem translationDeclaration_library (reverse : Bool) :
    (translationDeclaration reverse).library = translationLibrary reverse := by rfl

theorem translation_result_unique_zeuge :
    ((translationCertificate false).output ⟨0, by decide⟩).n = 3 ∧
    ((translationCertificate true).output ⟨0, by decide⟩).n = 5 := by
  simpa only [translationCertificate_output, translationOutput] using
    And.intro (sampleRows_first (declOf (translationUnit false))).1
      (sampleRows_first (declOf (translationUnit true))).2

/-- A well-typed identity output is wrong for the source-selected reversing translator. -/
theorem translation_wrong_output_zeuge :
    (translationOutput true ⟨0, by decide⟩).n ≠ (translationInput true ⟨0, by decide⟩).n :=
  sampleRows_wrong (declOf (translationUnit true))

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
  exact certificate_rejects_other (translationCertificate true) (translationInput true)
    (sampleRows_distinct (declOf (translationUnit true))) oracle passes world

/-- Count, range and token-schema errors all refuse before execution. -/
theorem translation_decoder_refusals_zeuge :
    (decodeIntegerRows (declOf (translationUnit false)) translationSchema [.num 3]).isNone = true ∧
    (decodeIntegerRows (declOf (translationUnit false)) translationSchema [.num 3, .num 11]).isNone = true ∧
    (decodeIntegerRows (declOf (translationUnit false)) translationSchema [.text "3 5"]).isNone = true :=
  sampleRows_refusals (declOf (translationUnit false))

theorem translation_measure_zeuge (passes : Nat) (Q : AxEns (declOf (translationUnit true)))
    (S : SperrInv (declOf (translationUnit true)))
    (T : (declOf (translationUnit true)).Tab ⊕ (declOf (translationUnit true)).Glob → Prop) :
    MassPflicht (translationDeclaration true).program passes Q S T Mass.leer
      (zykS (translationDeclaration true).program (translationDeclaration true).functions)
      (translationDeclaration true).translator :=
  translation_measure (translationDeclaration true) passes Q S T

/-- Joint qualified declaration fixture: the qualifier selects module `a` through typed export,
    bounded call graph and immutable by-value array signature. -/
def translationQualDeclaration : TranslationDecl translationQualSource translationQualUnit :=
  declarationFromData (source := translationQualSource) translation_qual_export_data.2
    (except_ok_get translation_qual_library_zeuge) translation_qual_export_data.1
    (except_ok_get translation_qual_lower_zeuge)

def translationQualInput : Wert (declOf translationQualUnit) translationSchema.ty :=
  sampleRows (declOf translationQualUnit) false

/-- A complete exact-execution certificate for the qualified selection. -/
def translationQualCertificate : TranslationCertificate translationQualDeclaration :=
  certificateFromData (source := translationQualSource) translation_qual_export_data.2
    (except_ok_get translation_qual_library_zeuge) translation_qual_export_data.1
    (except_ok_get translation_qual_lower_zeuge) translationQualInput translationQualInput
    (by exact sampleRows_decoded (declOf translationQualUnit)) rfl

/-- The per-site payload of the identity translation: site `[0]`, content the certified output. -/
def translationPayload : LibraryPayload (translationCertificate false) where
  site := [0]
  amStandort := by simp only [translationSource]
  inhalt := translationOutput false
  vollstaendig := by exact (translationCertificate_output false).symm

/-- Every payload row is the certified row. -/
theorem translationPayload_zeilen_zeuge :
    (translationPayload.inhalt ⟨0, by decide⟩).n = 3 ∧ (translationPayload.inhalt ⟨1, by decide⟩).n = 5 := by
  simpa only [translationPayload, translationOutput] using
    And.intro (sampleRows_first (declOf (translationUnit false))).1
      (sampleRows_second (declOf (translationUnit false)))

/-- Payloads are per site: this one is not at site `[1]`. -/
theorem translationPayload_standort_zeuge : translationPayload.site ≠ [1] := by
  simpa only [translationPayload] using (by decide : ([0] : List Nat) ≠ [1])

/-- The certified `lcall` expansion: ordinary call, payload last, caller arity met. -/
def translationExpansion : LibraryExpansion translationPayload where
  nutzlastArg := .variable "sample_payload_0"
  aufruf := .call "consume" (translationCall.args ++ [.variable "sample_payload_0"])
  erweitert := Or.inl (by
    simp only [expandLibraryCall, translationDeclaration_library]
    rw [(translation_library_shape false).1])
  stelligkeit := by
    simpa only [List.length_append, List.length_singleton, translationDeclaration_library] using
      (translation_library_shape false).2

/-- The certified `bindLib` expansion: the ordinary call value bound as usual. -/
def translationExpansionBind : LibraryExpansion translationPayload where
  nutzlastArg := .variable "sample_payload_0"
  aufruf := .bind false "value" none (.call "consume" (translationCall.args ++ [.variable "sample_payload_0"]))
  erweitert := Or.inr ⟨false, "value", (none : Option STyp), by
    simp only [expandBindLibraryCall, translationDeclaration_library]
    rw [(translation_library_shape false).1]⟩
  stelligkeit := by
    simpa only [List.length_append, List.length_singleton, translationDeclaration_library] using
      (translation_library_shape false).2

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
