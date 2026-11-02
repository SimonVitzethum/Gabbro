module

public import Grammatik.Parser.Profil.Auswahl
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

/-!
  File:      Grammatik/Parser/Profil/AuswahlZeuge.lean
  Subject:   WITNESSES for the build selection (C14): a tree with a top-level gate and a gate inside a
             module, selected in both modes to the exact expected trees; the generic theorems instantiated
             on it; a gate-free tree with a module and a `pub` that is its own selection; the reserved name.
-/

namespace Gabbro.Grammatik.Parser.Auswahl

set_option maxRecDepth 100000

/-- A constant item of the fixture. -/
def zeugeK (n : String) (v : Nat) : SItemTief := .constT n (.atom "u32") (.one (.lit v))

/-- Gates at the top and inside a module. -/
def zeugeG : List SItemTief :=
  [ zeugeK "N" 1, .gateT (zeugeK "T" 2),
    .modT "m" [.gateT (zeugeK "U" 3), zeugeK "V" 4] ]

/-- The test build keeps every item and removes the gate, module scope kept. -/
theorem zeugeG_pruefbau :
    beqSItemTiefList (waehleL .pruefbau zeugeG)
      [ zeugeK "N" 1, zeugeK "T" 2, .modT "m" [zeugeK "U" 3, zeugeK "V" 4] ] = true := by decide

/-- The shipping build keeps only the ungated items, module scope kept. -/
theorem zeugeG_auslieferung :
    beqSItemTiefList (waehleL .auslieferung zeugeG)
      [ zeugeK "N" 1, .modT "m" [zeugeK "V" 4] ] = true := by decide

/-- The fixture has gates; its selection in both modes has none (the generic theorem, instantiated). -/
theorem zeugeG_gatefrei (m : BauModus) :
    gatefreiL zeugeG = false ∧ gatefreiL (waehleL m zeugeG) = true :=
  ⟨by decide, waehleL_gatefrei m zeugeG⟩

/-- The fixture declares no reserved name, so the certificate is admitted in both modes. -/
theorem zeugeG_zulaessig (m : BauModus) : (Selection.von m zeugeG).zulaessig = true := by
  cases m <;> decide

/-- A gate-free tree with a module and a `pub` item. -/
def zeugeF : List SItemTief := [.modT "a" [.pubT (zeugeK "P" 5), zeugeK "Q" 6]]

/-- JOINT witness of `Selection.von_gatefrei`: the premise holds on the fixture and the selection in either
    mode IS the tree. -/
theorem zeugeF_eigene_auswahl (m : BauModus) :
    gatefreiL zeugeF = true ∧ (Selection.von m zeugeF).ausgewaehlt = zeugeF :=
  ⟨by decide, Selection.von_gatefrei m (by decide)⟩

/-- The reserved word declared as a constant is refused (`G003`), also under a module and under a gate. -/
theorem zeuge_reserviert :
    reserviertL [zeugeK "TESTBUILD" 1] = true ∧
    reserviertL [.modT "m" [.gateT (zeugeK "TESTBUILD" 1)]] = true ∧
    (Selection.von .pruefbau [zeugeK "TESTBUILD" 1]).zulaessig = false := by
  refine ⟨by decide, by decide, by decide⟩

#print axioms Gabbro.Grammatik.Parser.Auswahl.waehleL_gatefrei
#print axioms Gabbro.Grammatik.Parser.Auswahl.waehleL_id

end Gabbro.Grammatik.Parser.Auswahl
