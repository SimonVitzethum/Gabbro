module

public import Grammatik.Parser.Stmt.LibraryFixtures
public import Grammatik.Parser.Stmt.LibrarySource
public import Grammatik.Parser.Stmt.LibraryWitnesses
public import Grammatik.Parser.Print.Stmt
public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil2
public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil2a
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

/-! ## C02 items 1-2-4: resolved identity, export metadata and payload position.

    The lossless call (`SLibraryCall`, `libraryRegion`, `parseLibRuf`) keeps
    ordered arguments and the balanced region tokens; resolution
    (`libraryDecl`) selects exactly one library function and exactly one
    translator by key, never by first match or reconstructed arity. This
    module pins that identity on the non-degenerate fixtures: the payload
    parameter position, the translator-to-function key correspondence, the
    export normalization (`library` to `impl`, payload clause consumed) and
    the translator-free expanded unit. Nested regions round-trip with their
    token kinds intact. -/

/-- The caller omits exactly the final payload parameter: the resolved
    library takes one more parameter than the source call supplies. -/
theorem translation_payload_letzt_zeuge :
    (translationLibrary false).function.params.length =
      translationCall.args.length + 1 := by
  decide +kernel

/-- The payload parameter position: the final parameter, filled once per
    site by the export (`libraryPayloadArg`). -/
theorem translation_payload_position_zeuge :
    (translationLibrary false).function.params.length - 1 =
      translationCall.args.length := by
  decide +kernel

/-- The translator belongs to the resolved function: both carry the same
    selected key, so a changed translator body under that key is a different
    map (`translation_body_change_zeuge` in `LibraryCertificates.lean`). -/
theorem translation_schluessel_zeuge :
    strEq (translationLibrary false).translator.name
      (translationLibrary false).function.name = true := by
  decide +kernel

/-- The export normalizes a `library` head to an ordinary implemented
    function: its body elaborates like `impl`. -/
theorem translation_kopf_zeuge :
    (exportLibraryKopf (translationLibrary false).function).art = "impl" := by
  decide +kernel

/-- The normalization consumes the payload clause into the call-site
    expansions: no `load` clause survives on the exported head. -/
theorem translation_kopf_ohne_last_zeuge :
    ((exportLibraryKopf (translationLibrary false).function).klauseln.all
      fun | .load _ => false | _ => true) = true := by
  decide +kernel

/-- Whether an item list still holds a translator: translators are
    certificate input, never runtime items. -/
def ohneTranslator : List SItemTief → Bool
  | [] => true
  | .transT _ _ _ :: _ => false
  | _ :: rest => ohneTranslator rest

/-- The pre-pass consumes every translator of the expanded fixture unit. -/
theorem translation_erweitert_ohne_translator_zeuge :
    ohneTranslator
      ((exportLibraryUnit (translationMembers false)).toOption.getD []) = true := by
  decide +kernel

/-- The qualified selection resolves through the qualifier: module `a`
    selects its own library, never the same-named one of module `b`. -/
theorem translation_qual_index_zeuge :
    (translationQualLibrary).functionIndex ≠
      (libraryDecl translationQualMembers
        ⟨["b"], ["b::consume"], [], [.num 3, .num 5]⟩).toOption.get
          translation_qual_b_zeuge := by
  decide +kernel

/-- Nested regions round-trip with their token kinds intact: braces nest,
    they are never flattened or re-lexed. -/
theorem library_region_geschachtelt_zeuge :
    let call : SLibraryCall := ⟨["sample"], ["consume"], [.lit 7],
      [.zeichen "{", .num 1, .zeichen "}", .num 2]⟩
    beqTopStmt (parseTopStmt (druckAnw (.lcall call))) (.ok (.lcall call)) = true := by
  decide +kernel

end Gabbro.Grammatik.Uebersetzung
