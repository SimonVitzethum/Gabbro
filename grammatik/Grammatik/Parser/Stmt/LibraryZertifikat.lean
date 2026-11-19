module

public import Grammatik.Logik.Vertraege.Uebersetzung
public import Grammatik.Parser.Stmt.LibraryCertificates
import all Grammatik.Parser.Stmt.LibraryTranslationFixtures
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
public import Grammatik.Parser.Stmt.LibraryFixtures

@[expose] public section

namespace Gabbro.Grammatik.Uebersetzung

open Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

attribute [local cbv_opaque] translationPhaseItems
attribute [local cbv_eval] translation_items

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

/-- Payload content is unique per certificate: two payloads of one
    certificate agree, so no second content can ride the same site. -/
theorem nutzlast_inhalt_eindeutig {source : LibrarySource} {u : UProg}
    {decl : TranslationDecl source u}
    {certificate : TranslationCertificate decl}
    (first second : LibraryPayload certificate) :
    first.inhalt = second.inhalt := by
  rw [first.vollstaendig, second.vollstaendig]

end Gabbro.Grammatik.Uebersetzung
