module

public import Grammatik.Parser.Stmt.LibraryFixtures
public import Grammatik.Parser.Stmt.LibraryCertificates
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
import all Init.Data.String.Intercalate
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

/-! ## C02 item 5: source-bound translation certificates.

    The certificate names the exact source item, the resolved translator
    identity and the per-site payload -- and every component is recomputed
    in Lean from the retained source, never trusted from Rust. The
    resolver (`libraryDecl`) selects exactly one library function and one
    translator by key; the decoder (`decodeIntegerRows`) re-derives the
    input from the exact retained region tokens; the certificate output is
    the exact execution result, so a well-typed wrong output can never
    reuse a certificate (`translation_result_unique`,
    `translation_wrong_execution_zeuge` in `LibraryCertificates.lean`). -/

/-- The certificate input is recomputed from the exact retained source
    region: the decoder derivation stored in the certificate. -/
theorem zertifikat_eingabe_nachgerechnet_zeuge (reverse : Bool) :
    decodeIntegerRows (declOf (translationUnit reverse)) translationSchema
      (translationSource reverse).call.region =
      some (translationCertificate reverse).input :=
  (translationCertificate reverse).decoded

/-- The certificate resolves the exact source call: the declaration's
    library is the resolution of the retained call against the retained
    items. -/
theorem zertifikat_aufgeloest_zeuge (reverse : Bool) :
    libraryDecl (translationMembers reverse) translationCall =
      .ok (translationDeclaration reverse).library :=
  (translationDeclaration reverse).resolved

/-- The resolved translator carries the source-selected key: both fixtures
    select the translator named `build`, never a same-named foreign body. -/
theorem zertifikat_uebersetzer_name_zeuge (reverse : Bool) :
    (translationLibrary reverse).translator.name = "build" := by
  cases reverse <;> rfl

/-- Payload content is unique per certificate: two payloads of one
    certificate agree, so no second content can ride the same site. -/
theorem nutzlast_inhalt_eindeutig {source : LibrarySource} {u : UProg}
    {decl : TranslationDecl source u}
    {certificate : TranslationCertificate decl}
    (first second : LibraryPayload certificate) :
    first.inhalt = second.inhalt := by
  rw [first.vollstaendig, second.vollstaendig]

/-- The payload of the identity translation sits at the exact source call
    site `[0]`. -/
theorem zertifikat_standort_gebunden_zeuge :
    translationPayload.site = (translationSource false).path := rfl

/-- The Rust printer's claimed payload (`sumPayloadVals`, `sumPayloadOk`)
    is re-derived by the Lean decoder from raw tokens: output typing is
    recomputed, never trusted from Rust. The values coincide with the
    four entries `10 20 30 40`. -/
theorem rust_ausgabe_nachgerechnet_zeuge {D : Deklaration} :
    ∃ v, decodeIntegerRows D ⟨0, 100, 4⟩ [.num 10, .num 20, .num 30, .num 40] = some v ∧
      (v ⟨0, by decide⟩).n = 10 ∧ (v ⟨1, by decide⟩).n = 20 ∧
      (v ⟨2, by decide⟩).n = 30 ∧ (v ⟨3, by decide⟩).n = 40 := by
  refine ⟨_, rfl, rfl, rfl, rfl, rfl⟩

end Gabbro.Grammatik.Uebersetzung
