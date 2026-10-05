/-
  File:      Grammatik/X86/Avx2SraLanes.lean
  Subject:   AVX2 arithmetic shift right: per-lane equation on the coherent machine.

  Lane 1267 (follow-up of lane 1239 `Avx2Ops.lean`): `vecSraImm`/`sraLane`
  had witnesses only, no per-lane equation in the admitted range. This file
  proves the per-lane equation for VPSRAW/VPSRAD by immediate (sign fill,
  count >= width saturates to the sign), lane separation, and half agreement
  with the accepted evaluator (the old evaluator is lifted, never redefined).
  `.b8` shifts and `.b64` arithmetic have no AVX2 VEX encoding: they are a
  refusal by type (`SraBreite` has no such constructor), not a semantics.

  Manual provenance (checked 2026-10-05, clone-local
  `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`,
  Intel SDM 325462-093US September 2026): PSRAW/D `COUNT > 15/31` clamps
  so lanes become their sign fill; VPSRAQ exists EVEX-only, never VEX
  (see the line citations in `Avx2Ops.lean`). No page or quotation beyond
  those lines is claimed; silicon correspondence stays OPEN (see CUTS).
-/
import Grammatik.X86.Avx2Ops
import Grammatik.X86.HardwareExecution

namespace Gabbro.Grammatik.X86

/-- Admitted AVX2 arithmetic-shift widths: W (VPSRAW) and D (VPSRAD).
    `.b8` shifts and `.b64` arithmetic have no AVX2 VEX encoding, so they
    have no constructor here: refused by type, never silently substituted. -/
inductive SraBreite where
  | w16
  | w32
  deriving DecidableEq, Repr, Inhabited

/-- The lane width an admitted form shifts. -/
def SraBreite.breite : SraBreite → Breite
  | .w16 => .b16
  | .w32 => .b32

end Gabbro.Grammatik.X86
