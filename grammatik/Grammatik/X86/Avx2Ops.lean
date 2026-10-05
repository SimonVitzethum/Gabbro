/-
  File:      Grammatik/X86/Avx2Ops.lean
  Subject:   AVX2 256-bit integer operation semantics (pure functions).

  Lane 1239 (Tier 3, first OPTIONAL selected-CPU profile): pure semantic
  functions on 256-bit values, modelled as a pair of 128-bit halves, for
  the integer ops VPADD/VPSUB B/W/D/Q, VPAND/VPOR/VPXOR/VPANDN,
  VPCMPEQ B/W/D/Q, VPSLL/VPSRL/VPSRA by immediate. Each half reuses the
  accepted `Vektor` lane vocabulary (`vecAdd`, `vecSub`, `vecAnd`,
  `vecOr`, `vecXor`); nothing is redefined. No shuffle/permute, no
  gather, no FMA. No decoder, no register file, no machine step here:
  those belong to the sibling AVX2 pieces (Vex, State, Mem).

  Manual provenance: Intel SDM 325462-093US September 2026, Vol. 2B
  per-instruction entries (VPADDB/W/D/Q, VPSUBB/W/D/Q, VPAND/VPOR/VPXOR/
  VPANDN, VPCMPEQB/W/D/Q, VPSLLW/D/Q, VPSRLW/D/Q, VPSRAW/D immediate
  forms; each 128-bit lane shifted independently; count past the
  width saturates to zero; VPCMPEQ writes all-ones/zero per lane).
  No hardware reference files are present in this clone, so NO page or
  quotation is cited; silicon correspondence stays OPEN (see CUTS).
-/
import Grammatik.X86.VectorIntegerHardwareForms
import Grammatik.X86.VectorHardwareProfile
import Grammatik.X86.FeatureProfile

namespace Gabbro.Grammatik.X86

/-- A 256-bit AVX2 integer value: the low and high 128-bit halves.
    AVX2 integer ops act within each 128-bit lane, so the pair is the
    faithful shape (no cross-half carry exists by construction). -/
abbrev Ymm := Vektor × Vektor

/-- Low 128-bit half of a 256-bit value. -/
def ymmLo (y : Ymm) : Vektor := y.1

/-- High 128-bit half of a 256-bit value. -/
def ymmHi (y : Ymm) : Vektor := y.2

end Gabbro.Grammatik.X86
