/-
  File:      Grammatik/X86/OptRangeElim.lean
  Subject:   Range/bound/overflow-check elimination rule lemma (lane 867).

  DESIGN section 7 row: local premise "source extent proof AT the site
  (N571/N463/N506: gate ensures over once-bound name; constant
  fixed-size)", certificate "B+C", failure cases "entry invariant
  removes check inside writer's own mutating loop; entry range across a
  writing call", phase M, cost O(sites).
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Validator-decided side conditions for one range-check site. -/
structure RangeElimCert where
  extentAmOrt : Bool
  einmalGebunden : Bool
  keinSchreiberDazwischen : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. -/
def rangeElimZulassen (c : RangeElimCert) : Bool :=
  c.extentAmOrt && c.einmalGebunden && c.keinSchreiberDazwischen

/-- No at-site extent proof: refuse. -/
theorem rangeElimVerweigert_ohneAusmass (c : RangeElimCert)
    (h : c.extentAmOrt = false) :
    rangeElimZulassen c = false := by
  simp [rangeElimZulassen, h]

/-- Twice-bound name carries no extent (N571): refuse. -/
theorem rangeElimVerweigert_zweitbindung (c : RangeElimCert)
    (h : c.einmalGebunden = false) :
    rangeElimZulassen c = false := by
  simp [rangeElimZulassen, h]

/-- An intervening writer (writing call; writer's own mutating loop): refuse. -/
theorem rangeElimVerweigert_schreiberDazwischen (c : RangeElimCert)
    (h : c.keinSchreiberDazwischen = false) :
    rangeElimZulassen c = false := by
  simp [rangeElimZulassen, h]

/- CUTS:
    - Connection and witness follow in the next piece.
-/

#print axioms rangeElimZulassen
#print axioms rangeElimVerweigert_ohneAusmass
#print axioms rangeElimVerweigert_zweitbindung
#print axioms rangeElimVerweigert_schreiberDazwischen

end Gabbro.Grammatik.X86
