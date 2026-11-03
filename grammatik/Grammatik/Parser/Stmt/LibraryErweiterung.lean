module

public import Grammatik.Logik.Vertraege.UebersetzungReinheit
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

/-! ## C02 item 7: immutable payload initialization and ordinary call expansion.

    The certified expansion runs in the ACTUAL compiler path:
    `exportLibraryUnit` (called by `exportDeclarationUnitDetailed`, hence
    by `Modules.prepare`, `expandU` and `elabU`) rewrites every source
    library call to the certified shape with the export's payload place,
    and the lowering (`uAnwReiheCore`) refuses unexpanded `lcall`/`bindLib`
    by name -- so an elaborated unit can only contain the ordinary call.
    The payload channel is a read-only table capability: a writable
    payload parameter and a caller-supplied payload both refuse at
    resolution, so payload mutation has no interface. -/

/-- The actual pre-pass expands the fixture caller to the export shape:
    ordinary call, payload last. -/
theorem translation_erweitert_form_zeuge :
    (exportLibraryStmt (translationMembers false) translationCallerBody).toOption.map
      (fun s => beqSAnw s
        (exportLibraryCall (translationLibrary false) translationCall)) =
      some true := by
  decide +kernel

/-- The export shape is the certified shape with the export's payload
    place (`libraryPayloadArg`). -/
theorem translation_erweitert_zertifikat_form_zeuge :
    exportLibraryCall (translationLibrary false) translationCall =
      expandLibraryCall (translationLibrary false)
        (libraryPayloadArg (translationLibrary false)) translationCall :=
  exportLibraryCall_form _ _

/-- The actual pre-pass expands the `let`-bound fixture caller the same
    way: the ordinary call value bound as usual. -/
theorem translation_erweitert_bind_zeuge :
    (exportLibraryStmt (translationMembers false)
      (.block [.bindLib false "value" none translationCall]
        (some (.ret none)))).toOption.map
      (fun s => beqSAnw s
        (exportLibraryBind false "value" none (translationLibrary false)
          translationCall)) =
      some true := by
  decide +kernel

/-- The `let`-bound export shape is the certified `let`-bound shape. -/
theorem translation_erweitert_bind_zertifikat_form_zeuge :
    exportLibraryBind false "value" none (translationLibrary false) translationCall =
      expandBindLibraryCall false "value" none (translationLibrary false)
        (libraryPayloadArg (translationLibrary false)) translationCall :=
  exportLibraryBind_form _ _ _ _ _

/-- Both fixture translators declare pure effects: no reads, writes,
    locks or loops at the source-effect level. -/
theorem translation_translator_rein_zeuge :
    effekteRein (translationLibrary false).translator.klauseln = true ∧
    effekteRein (translationLibrary true).translator.klauseln = true := by
  decide +kernel

/-- A writable payload parameter refuses: the payload channel is a
    read-only table capability, so payload mutation has no interface. -/
def translationSchreibText : String :=
  "module sample { table Rows count 2 { slot { v : u8 in 0 .. 10, } } " ++
  "library fn consume(p : ptr<normal, w> Rows) payload Rows { return; } " ++
  "translator build for consume(region : [u8 in 0 .. 10; 2]) -> [u8 in 0 .. 10; 2] " ++
  "effects { pure } { return region; } impl fn caller() { @sample#consume() { 3 5 }; return; }"

def translationSchreibTokens : List Token :=
  (lexL translationSchreibText.toList).toOption.getD []

def translationSchreibItems : List SItemTief :=
  (parseTopTief translationSchreibTokens).toOption.getD []

def translationSchreibMembers : List SItemTief :=
  Aufloesung.loeseL (Aufloesung.quelle translationSchreibItems) [] translationSchreibItems

theorem translation_schreib_nutzlast_verweigert_zeuge :
    (libraryDecl translationSchreibMembers translationCall).toOption.isNone = true := by
  decide +kernel

/-- A caller-supplied payload refuses: the caller omits exactly the final
    payload parameter, which the export fills once per site. -/
theorem translation_nutzlast_stelligkeit_verweigert_zeuge :
    (libraryDecl (translationMembers false)
      { translationCall with args := [.lit 7] }).toOption.isNone = true := by
  decide +kernel

/-- An ambiguous library function refuses through the actual pre-pass:
    resolution never picks the first match. -/
def mehrdeutigRufer : SItemTief :=
  .fnT { art := "impl", name := "caller", params := [], res := none,
    fehler := none, klauseln := [] }
    (.block [.lcall ⟨["m"], ["consume"], [], []⟩] (some (.ret none)))

theorem export_mehrdeutig_verweigert_zeuge :
    (exportLibraryUnit (doppeltMembers ++ [mehrdeutigRufer])).isErr = true := by
  decide +kernel

end Gabbro.Grammatik.Uebersetzung
