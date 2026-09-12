/-
  Lane-21 audit probe 1: the deprecated `MaschinenLauf` reachability wrapper.

  Claim under test: several theorems in `Maschine.lean` §§1-5 look like
  derivations of W1/W2/W3/W4 and "real reduction", but under unfolding they
  re-emit the premises that `MaschinenLauf` already carries as structure
  fields. This file demonstrates the representation-change case for the
  W3/W4-bearing wrappers.
-/
import Grammatik.Maschine

open Gabbro.Grammatik

variable {D : Deklaration}

/-- `gesittet_aus_maschine` is the bridge applied to the machine's own fields:
    W3 (`hausschluss`), W4 (`hEin`), W5 (`hungeteilt`) travel unchanged.
    Demonstrated here: projecting the result recovers exactly the fields. -/
theorem audit21_gesittet_is_bridge (M : MaschinenLauf (D := D)) :
    (gesittet_aus_maschine M).ausschluss = M.hausschluss :=
  -- `gesittet_aus_maschine` is `bruecke_exec_gesittet` applied to the
  -- machine's own fields; definitional unfolding exposes the packing.
  rfl

/-- Same for the W4 component: the conclusion's `marke_eindeutig` field is
    `marke_eindeutig_aus_einfaedig` applied to the premise `M.hEin`. -/
theorem audit21_marke_is_hEin (M : MaschinenLauf (D := D)) :
    (gesittet_aus_maschine M).marke_eindeutig =
      marke_eindeutig_aus_einfaedig M.code M.run M.hEin := by
  rfl

/-- Same for W5: the conclusion's `ungeteilt` field is the premise. -/
theorem audit21_ungeteilt_is_hungeteilt (M : MaschinenLauf (D := D)) :
    (gesittet_aus_maschine M).ungeteilt = M.hungeteilt := by
  rfl

/-
CUTS:
- No claim about generated runs (§§7-11); this probe covers only the
  deprecated §§1-5 wrapper and its field-preserving shape.
- Whether field-preservation counts as "progress" is an audit judgement, not
  a Lean verdict; the equalities above are the checked evidence.
-/
#print axioms audit21_gesittet_is_bridge
#print axioms audit21_marke_is_hEin
#print axioms audit21_ungeteilt_is_hungeteilt
