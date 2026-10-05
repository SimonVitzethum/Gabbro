/-
  File:      Grammatik/X86/HwKapsteinTsoRest.lean
  Subject:   Capstone rest: TSO projection for the device, FP, vector,
             fault, gate, interrupt and image tags.

  Lane 1329: classify the ten remaining union tags of `HwVollSchritt`
  (`HwKapstein.lean`) against the TSO store-buffer projection `kapTso`
  (`HwKapsteinTso.lean`, lane 1295):
  - uc, port: device paths are NOT store-buffered in the stated model.
    Both are projection-unchanged for the TSO buffers, with the device
    effect named (posted UC write on the extended machine; accepted
    bus latch for ports, gated on the drained buffer).
  - fp, vec: register, load-observation and refusal legs are
    projection-unchanged; byte stores are single `issueByte` events and
    drains single `flushKern` events; a 16-byte vector row is sixteen
    issues (no whole-vector atomicity).
  - fehler, tor, bild, instanzen: projection-unchanged (a faulting or
    refused step has no buffer effect; a fetch/register step changes
    core data only).
  - nested, int: FINDING. Delivery is explicitly NOT a buffered push
    (S3 in `HwNestedInterrupts.lean`, `asyncMasch_puffer_still`): the
    frame lands in canonical memory through direct `write64` pushes
    (`schiebeRahmen`) with every store buffer untouched. The exhibited
    NMI run provably changes memory (`witNmi_aendert_ss`) while no
    buffer grows (`witNmi_puffer_0/1`). A memory write by a path other
    than the TSO events is therefore classified as a FINDING of high
    priority, never as stack-push events: the per-access bridge needs
    a drained-own-buffer guard for delivery.

  Every accepted definition is reused unchanged, never redefined.
  Vendor neutral (rule 17): no silicon value is pinned; Intel SDM
  provenance is cited from the family files, never restated.
-/
import Grammatik.X86.HwKapsteinTso
import Grammatik.X86.HwKapsteinSteps

namespace Gabbro.Grammatik.X86

end Gabbro.Grammatik.X86
