/-
  Audit probe F1: `invErhalt_aus_Kontext` returns a full `↔` from only one side.

  Claim: the proof `⟨fun _ => hInv c nach hkn, fun _ => hInv c vor hkv⟩`
  never inspects the incoming hypothesis `Q vor` / `Q nach`. Each direction
  holds because `hInv` holds at EVERY chain world. The conclusion is NOT
  "vor is preserved across the step"; it is "inv holds at vor AND inv holds
  at nach", repackaged as an iff. Demonstrated below by rebuilding the same
  conclusion from the two membership facts alone.
-/
import Grammatik.InterferenzAllgemein

namespace Gabbro.Grammatik

open Gabbro.Grammatik

variable {D : Deklaration}

/-- Same conclusion as `invErhalt_aus_Kontext`, rebuilt without using the
    step relation: forward and backward maps both ignore their argument. -/
theorem audit_invErhalt_ignores_argument
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (hInv : InvariantenKontext Nb J I)
    (c : D.Tab ⊕ D.Glob) (vor nach : World D)
    (hkv : vor ∈ J.welten) (hkn : nach ∈ J.welten) :
    I.inv c vor ↔ I.inv c nach :=
  ⟨fun _ => hInv c nach hkn, fun _ => hInv c vor hkv⟩

/-- Strengthening the demonstration: the conclusion follows from
    `I.inv c vor ∧ I.inv c nach`, i.e. it is a conjunction in iff clothing. -/
example (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (hInv : InvariantenKontext Nb J I)
    (c : D.Tab ⊕ D.Glob) (vor nach : World D)
    (hkv : vor ∈ J.welten) (hkn : nach ∈ J.welten) :
    (I.inv c vor ∧ I.inv c nach) ∧
      (I.inv c vor ↔ I.inv c nach) :=
  ⟨⟨hInv c vor hkv, hInv c nach hkn⟩,
   audit_invErhalt_ignores_argument Nb J I hInv c vor nach hkv hkn⟩

/-
CUTS:
- No claim about steps, frames, or disjointness is made here; that is the point.
- `hInv : InvariantenKontext` (invariant at EVERY chain world) is the load-bearing
  premise; whether ordinary critical sections satisfy it is out of scope for this probe.
-/
#print axioms Gabbro.Grammatik.audit_invErhalt_ignores_argument
