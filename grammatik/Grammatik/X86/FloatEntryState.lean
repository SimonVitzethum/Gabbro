/-
  File:      Grammatik/X86/FloatEntryState.lean
  Subject:   Entry control-state admission for admitted scalar FP execution.

  Lane 626: connects the actual `ScalarFloat` extended state
  (`FpZustand`/`fpEintritt` over the `mxcsrGueltig` profile), the
  `EntryState` entry control-state discipline (`mxcsrOk` over the
  per-entry `EintrittZustand` word) and the `FeatureProfile`
  silicon/readiness admission (`bereit`/`merkmalZugelassen`).
  Proves MXCSR word validity decomposition and preservation across
  actual admitted FP steps, and refuses FTZ/DAZ, non-nearest rounding
  and unsupported exception/control encodings at the entry predicate.
  No new executor, no second decoder, no source/checker/emitter change.
-/
import Grammatik.X86.ScalarFloat
import Grammatik.X86.EntryState
import Grammatik.X86.FeatureProfile
import Grammatik.X86.ContractSites

namespace Gabbro.Grammatik.X86

/-- The entry's FP context: the entry state's own MXCSR word as the
    per-context control word (software establishment is ordinary data
    movement of this word; no OS/hardware switch semantics claimed). -/
def eintrittFp (z : EintrittZustand) : FPKontext := ⟨z.mxcsr⟩

/-- Entry admission at the control word IS the FP profile admission:
    the entry word as a context meets `fpEintritt` exactly when the
    word is profile-valid. -/
theorem eintrittFp_profil (z : EintrittZustand) :
    fpEintritt (eintrittFp z) = mxcsrGueltig z.mxcsr := rfl

/- CUTS:
   - Skeleton only: decomposition, bridge, preservation, refusals and
     the joint witness follow in small increments.
-/

#print axioms eintrittFp
#print axioms eintrittFp_profil

end Gabbro.Grammatik.X86
