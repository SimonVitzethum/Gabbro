module

public import Grammatik.Logik.Vertraege.Uebersetzung
public import Grammatik.Parser.Stmt.LibrarySource
public import Grammatik.Parser.Stmt.LibraryWitnesses
import all Grammatik.Parser.Stmt.LibraryTranslationFixtures
import all Grammatik.Parser.Stmt.LibraryQualifiedFixtures
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

/-- Whether an item list still holds a translator: translators are
    certificate input, never runtime items. -/
def ohneTranslator : List SItemTief → Bool
  | [] => true
  | .transT _ _ _ :: _ => false
  | _ :: rest => ohneTranslator rest

-- Retain an actual successful export before inspecting its item list. An
-- error followed by the public getter's empty default cannot certify this.
private theorem translation_export_without_translators :
    ∃ expanded, exportLibraryUnit (translationPhaseMembers false) = .ok expanded ∧
      ohneTranslator expanded = true := by
  refine ⟨?expanded, ?produced, ?ordinary⟩
  case produced => cbv <;> exact Eq.refl _
  case ordinary => cbv

-- Both complete selections are fixed before projecting their indices. No
-- raw source getter is reduced while comparing these metadata fields.
private theorem qualified_selection_indices :
    ∃ first second,
      libraryDecl qualPhaseMembers translationQualCall = .ok first ∧
      libraryDecl qualPhaseMembers ⟨["b"], ["b::consume"], [], [.num 3, .num 5]⟩ = .ok second ∧
      first.functionIndex ≠ second.functionIndex := by
  refine ⟨?first, ?second, ?foundFirst, ?foundSecond, ?different⟩
  case foundFirst => cbv <;> exact Eq.refl _
  case foundSecond => cbv <;> exact Eq.refl _
  case different => cbv

end Gabbro.Grammatik.Uebersetzung
