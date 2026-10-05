/-
  File:      Grammatik/X86/HwKapsteinTsoIsaAddr.lean
  Subject:   TSO projection of the isa, addr and muldiv union tags.

  Lane 1327: every classified union step of `HwKapsteinTso` (lane 1295)
  projects to the TSO store-buffer model; isa/addr/muldiv were left as
  FINDINGs there. This file classifies exactly those three tags over
  the reused projection `kapTso` (never redefined): isa register steps
  are silent, isa loads observe with forwarding, isa stores are single
  `issueByte` events; muldiv steps are silent (register-only); addr
  stores are folds of byte issues (`concIssue` over `entriesOf`) and
  addr loads are silent forwarding observations. Widths 1/2/4/8 bytes;
  a split across a group boundary stays the accepted tearing refusal.
  Every accepted definition is reused unchanged, never redefined.
-/
import Grammatik.X86.HwKapsteinTso

namespace Gabbro.Grammatik.X86

/-- Re-embedded ISA successors leave the TSO projection unchanged:
    only core data moves, never memory or buffers. -/
theorem kapTso_setKernVonZustand (m : HwMaschine) (c : Nat)
    (s' : Zustand) :
    kapTso (setKernVonZustand m c s') = kapTso m := by
  rfl

/- CUTS:
    Proved here so far: `kapTso_setKernVonZustand` (ISA register
    re-embedding is silent on the TSO projection).
    NOT proved here (next pieces): isa/addr/muldiv classification,
    `concIssue` fold lemmas, union lifts, joint witness.
-/

#print axioms kapTso_setKernVonZustand

end Gabbro.Grammatik.X86
