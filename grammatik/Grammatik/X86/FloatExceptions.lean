/-
  File:      Grammatik/X86/FloatExceptions.lean
  Subject:   Guarded binary64 divide exceptions: masked IEEE values, no traps.

  Lane 425: masked invalid/divide-by-zero produce model VALUES under a valid
  MXCSR context; a refused context refuses the lowering slot (none), not a
  hardware fault. Reuses Gleitkomma/Gleitprofil/Speicher, claims no hardware.
-/
import Grammatik.X86.Gleitprofil

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik.Gleitkomma

/-- Lowering guard: the owning context meets the accepted MXCSR profile. -/
def floatGuard (k : FPKontext) : Bool :=
  mxcsrGueltig k.mxcsr

/-- Guarded binary64 division: model value under a valid context, refusal
    (`none`) otherwise. IEEE masked exceptions are values, never traps. -/
def guardedDiv64 (k : FPKontext)
    (a b : Gleitkomma.GBits Gleitkomma.f64) :
    Option (Gleitkomma.GBits Gleitkomma.f64) :=
  if floatGuard k then some (fdiv64 a b) else none

/-- Valid context delivers the model value (premise used to take the branch). -/
theorem guardedDiv_gueltig (k : FPKontext)
    (a b : Gleitkomma.GBits Gleitkomma.f64)
    (h : floatGuard k = true) :
    guardedDiv64 k a b = some (fdiv64 a b) := by
  unfold guardedDiv64
  simp [h]

/- CUTS: bounded skeleton; exception classes, refused case, memory
   observation, witnesses and axiom prints arrive next.
-/

#print axioms guardedDiv_gueltig

end Gabbro.Grammatik.X86
