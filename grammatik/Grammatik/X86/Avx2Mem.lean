/-
  File:      Grammatik/X86/Avx2Mem.lean
  Subject:   AVX2 32-byte memory accesses (VMOVDQU/VMOVDQA) on the coherent
             TSO machine.

  Lane 1243 (Tier 3, first OPTIONAL selected-CPU profile): the two 256-bit
  memory shapes -- unaligned VMOVDQU (no alignment requirement) and aligned
  VMOVDQA (32-byte alignment, else #GP) -- as footprint-checked accesses on
  `HwMaschine`/`HwSchritt` (lane 660) over the accepted canonical TSO byte
  equations (`TSO`: `issueByte`/`loadByte`/`flushKern`). A 32-byte store is
  a sequence of byte issues in the acting core's buffer with the accepted
  forwarding and partial-overlap rules; page-crossing (permission) faults
  leave memory unchanged; NO whole-vector atomicity is claimed (tearing
  table: the access may be observed in parts, as the accepted byte model
  says). Values are two accepted 128-bit halves (`Vektor`); entry bytes ARE
  accepted chunk bytes by construction. Enabled only by the NAMED CPU
  profile plus CPUID/XCR0/OS-state gates; absent form = refused encoding
  (DIRECT-COMPILER-DESIGN §§2C/2D/6). Sibling AVX2 lanes (Vex, Ops, State)
  are not used here; YMM register-file binding stays with the State lane.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.TSO
import Grammatik.X86.HardwareExecution
import Grammatik.X86.WordAccessGrouping
import Grammatik.X86.Vektor
import Grammatik.X86.FeatureProfile
import Grammatik.X86.VectorHardwareProfile
import Grammatik.X86.VectorFootprints
import Grammatik.X86.Ausfuehrung

namespace Gabbro.Grammatik.X86

/-- The two selected 256-bit memory shapes: aligned (VMOVDQA) and
    unaligned (VMOVDQU). No other AVX2 memory form is admitted here. -/
inductive Avx2MemForm where
  | ausgerichtet
  | unausgerichtet
  deriving DecidableEq, Repr

/- CUTS:
   Skeleton only: forms are named, nothing is proved yet.
-/

#print axioms Avx2MemForm

end Gabbro.Grammatik.X86
