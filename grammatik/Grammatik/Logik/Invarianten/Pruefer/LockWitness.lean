module

public import Grammatik.Logik.Invarianten.Pruefer.Locks
public import Grammatik.Nebenlaeufigkeit.Allgemein.MehrfadenZeuge.Teil1Basis

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Pruefer.LockWitness

/-- A real lock identifier from the existing concurrent fixture. The source
    evidence states correspondence, not truth of arbitrary memory. -/
def sources : LockSources (SperrInv.leer mD) := fun _ => some
  { resources := []
    expression := .tru
    correct := fun _ => rfl }

theorem reified_zeuge :
    (lockFormula (SperrInv.leer mD) sources ()).toOption.isSome = true := by rfl

/-- Absence of syntax does not become a fabricated true predicate. -/
theorem opaque_zeuge :
    (lockFormula (SperrInv.leer mD) (fun _ => none) ()).toOption.isSome = false := by rfl

end Gabbro.Grammatik.Invarianten.Pruefer.LockWitness
