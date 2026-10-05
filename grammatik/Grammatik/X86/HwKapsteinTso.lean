/-
  File:      Grammatik/X86/HwKapsteinTso.lean
  Subject:   Capstone: every classified union step projects to the TSO
             store-buffer model.

  Lane 1295: projection `kapTso` of `HwMaschine` to the TSO-only machine
  (memory, per-core buffers, forwarding) and the refinement that underlies
  every per-access bridge. The base step classifies exactly (silent,
  single issue, single flush, forward-read observation); word/drain/fwd/
  stack family steps reach via `TSOErreichbar`. Remaining tags are FINDINGs.
  Every accepted definition is reused unchanged, never redefined.
-/
import Grammatik.X86.HwKapstein

namespace Gabbro.Grammatik.X86

/-- Projection of the coherent machine to the TSO-only machine:
    shared memory plus per-core store buffers. -/
def kapTso (m : HwMaschine) : TSOZustand :=
  tsoAnsicht m

/-- Core-data updates leave the projection unchanged. -/
theorem kapTso_setKernDaten (m : HwMaschine) (c : Nat) (k : HwKern) :
    kapTso (setKernDaten m c k) = kapTso m := by
  rfl

/- CUTS:
   Skeleton only: projection and core-data silence.
   NOT proved yet: base classification, word/drain/fwd/stack reachability,
   locked RMW guard, joint witness, remaining-tag findings.
   No W/GX, no whole-word atomicity beyond guarded drains, no silicon claim.
-/

#print axioms kapTso
#print axioms kapTso_setKernDaten

end Gabbro.Grammatik.X86
