module

public import Core.Beobachtung.Fluss.Fragment
public import Core.Beobachtung.Fluss.Antwort

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Fragment Befehl)

def AggregatNIAussage : Prop :=
  FamilienNI .aggregat

/-- Aggregat steps are silent: the coupling is preserved through the lockstep. -/
theorem aggregatNI : AggregatNIAussage := by
  classical
  intro p plattform f _ _ h₁ h₂ ρ₁ ρ₂ vergleich predictor t c w spur vor
    zustand kopf spurGlied kopplung
  exact stummer_schritt_koppelt vergleich zustand kopf spurGlied
    (antwortNI p plattform h₂ ρ₂ vergleich.rechts t · ·) kopplung

end Gabbro.Core.Beobachtung
