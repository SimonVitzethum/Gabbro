/-
  File:      Grammatik/X86/PipelineAtomicsBind.lean
  Subject:   Pipeline atomics: register-address binding for RMW/fence byte
             forms, SFENCE/LFENCE lowering, and the 8-issue word-install
             proof.

  Lane 1203 (follow-up of lane 1163 `PipelineAtomics.lean`): the three
  open gaps named in its CUTS -- (a) which (base, disp) names which
  address for the locked byte forms, (b) SFENCE/LFENCE lowering, (c) the
  whole-word store install from bytes -- closed over REUSED accepted
  definitions only. No new machine, no new decoder row, no second IR,
  no source/checker/goal change. Unsupported shapes are REFUSED.
-/
import Grammatik.X86.PipelineAtomics
import Grammatik.X86.SfenceStoreNarrow
import Grammatik.X86.LfenceLoadNarrow
import Grammatik.X86.WordAccessGrouping

namespace Gabbro.Grammatik.X86.PipelineAtomicsBind

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.PipelineAtomics

/-- Fence kind: full MFENCE plus the two narrow forms. -/
inductive ZaunArt where
  | mfence
  | sfence
  | lfence
  deriving DecidableEq, Repr

/-- Canonical bytes of one fence kind (all reused, never redefined). -/
def zaunBytes : ZaunArt → List Byte
  | .mfence => pinMfence
  | .sfence => pinSfence
  | .lfence => lfenceBytes

/-- MFENCE bytes are the accepted locked fence pin. -/
theorem zaunBytes_mfence : zaunBytes .mfence = pinMfence := rfl

/-- SFENCE bytes are the accepted narrow-store pin. -/
theorem zaunBytes_sfence : zaunBytes .sfence = pinSfence := rfl

/-- LFENCE bytes are the accepted narrow-load pin. -/
theorem zaunBytes_lfence : zaunBytes .lfence = lfenceBytes := rfl

/- CUTS: what is not proved here (skeleton; extended with each piece)
    NOT proved here, and not claimed:
    - No seq_cst total order, no fairness, no CAS retry bound.
    - No full source `execBlock` correspondence for atomics.
-/

#print axioms zaunBytes_mfence
#print axioms zaunBytes_sfence
#print axioms zaunBytes_lfence

end Gabbro.Grammatik.X86.PipelineAtomicsBind
