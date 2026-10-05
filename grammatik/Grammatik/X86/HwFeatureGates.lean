/-
  File:      Grammatik/X86/HwFeatureGates.lean
  Subject:   CPUID/feature enabled-state gating inside the coherent
             machine `HwMaschine`/`HwSchritt`.

  Lane 1135: connect ONE family strand (CPUID/XCR0 observation from
  `CpuFeatureHardwareForms`, finite admission from `FeatureProfile`,
  per-image closing from `ComposeFeatureGate`) to the coherent
  machine from `HardwareExecution`, reusing every accepted definition
  unchanged (never a copied model; only lifted equations). The
  architectural fault vocabulary is `ArchFehler` (`HardwareFaults`).
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.HardwareFaults
import Grammatik.X86.ComposeFeatureGate

namespace Gabbro.Grammatik.X86

/-- Feature row behind one unified instruction: scalar FP needs the
    scalar-double row, packed integer the packed tier; every other
    dispatcher family needs no feature bit (always admitted). -/
def hwTorMerkmal : ExtInstr → Option PerfMerkmal
  | .fp _ => some .sseDoppel
  | .vec _ => some .paketInt128
  | _ => none

/- CUTS:
   Skeleton only: the feature-row mapping. Gate predicates, generic
   refusal over all dispatcher families, the #UD classification, the
   adapter/embedding, planted refusals and the joint witness are OPEN.
-/

#print axioms hwTorMerkmal

end Gabbro.Grammatik.X86
