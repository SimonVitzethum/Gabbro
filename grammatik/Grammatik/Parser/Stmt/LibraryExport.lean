module

public import Grammatik.Logik.Vertraege.Uebersetzung
public import Grammatik.Parser.Stmt.LibraryFixtures
public import Grammatik.Parser.Stmt.LibraryCertificates
public import Grammatik.Zielsatz.Kern.Akzeptiert
public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem
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

/-! ## Connected export witness: a qualified library call through the pipeline.

    Source text with a qualified library call elaborates (through the certified expansion) to an
    ordinary unit, lowers, and the checker Bool holds -- on the non-degenerate two-module
    fixture with a real call, not a degenerate empty unit. Layout and image, C14/C08 and Stage-0
    closure stay with their owners. -/

/-- The qualified caller unit through the export: the two-module source with a qualified library
    call elaborates to an ordinary unit. -/
def exportQualEinheit : UProg :=
  (elabU (pre108 translationQualItems)).toOption.getD { tabs := [], locks := [], fns := [] }

theorem export_qual_elab_zeuge :
    (elabU (pre108 translationQualItems)).toOption.isSome = true := by
  decide +kernel

/-- The export leaves no ignored source duty behind on the fixture. -/
theorem export_qual_tor_zeuge : exportQualEinheit.exportGate = .ok () := by
  decide +kernel

/-- Whether every function body of an item list is ordinary (no library construct remains). -/
def alleOhneBibliothek : List SItemTief → Bool
  | [] => true
  | .fnT _ body :: rest => ohneBibliothekAnw body && alleOhneBibliothek rest
  | _ :: rest => alleOhneBibliothek rest

/-- The expanded source: the pre-pass output on the fixture members. -/
def exportQualErweitert : List SItemTief :=
  (exportLibraryUnit (uMembers (pre108 translationQualItems))).toOption.getD []

/-- The pre-pass ran: every expanded body is ordinary. -/
theorem export_qual_ohne_zeuge : alleOhneBibliothek exportQualErweitert = true := by
  decide +kernel

theorem export_qual_lower_ok :
    (lowerAllg exportQualEinheit).toOption.isSome = true := by
  decide +kernel

def exportQualGesenkert :
    Programm (declOf exportQualEinheit) × List (declOf exportQualEinheit).Fn :=
  (lowerAllg exportQualEinheit).toOption.get export_qual_lower_ok

/-- The connected verdict: source text with a qualified library call elaborates, lowers, and the
    checker Bool holds. The enumerations are complete by construction (`finRange` over the
    elaborated tables, statics and locks; the lowered functions; no starts, since the fixture
    declares no `concurrent` item). -/
theorem export_qual_akzeptiert_zeuge :
    Gabbro.Grammatik.Akzeptiert exportQualGesenkert.1 (Gabbro.Grammatik.SperrInv.leer _)
      exportQualGesenkert.2 (List.finRange exportQualEinheit.locks.length)
      ((List.finRange exportQualEinheit.tabs.length).map Sum.inl ++
        (List.finRange exportQualEinheit.globs.length).map Sum.inr) [] = true := by
  decide +kernel

end Gabbro.Grammatik.Uebersetzung
