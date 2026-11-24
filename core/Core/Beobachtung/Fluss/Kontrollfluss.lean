module

public import Core.Beobachtung.Fluss.Fragment
public import Core.Beobachtung.Fluss.Antwort

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Fragment Befehl)

def KontrollflussNIAussage : Prop :=
  FamilienNI .kontrollfluss

/-- Control-flow steps are silent: the coupling is preserved through the lockstep.
    Every context step of a source fragment changes only the local frame: its plan is
    the internal plan and the machine protocol contributes no event. Control-flow forms
    are exactly the forms whose only effect is the program counter and the local bindings. -/
theorem kontrollflussNI : KontrollflussNIAussage := by
  classical
  intro p plattform f _ _ h₁ h₂ ρ₁ ρ₂ vergleich predictor t c w spur vor
    zustand kopf spurGlied kopplung
  exact stummer_schritt_koppelt vergleich zustand kopf spurGlied
    (antwortNI p plattform h₂ ρ₂ vergleich.rechts t · ·) kopplung

end Gabbro.Core.Beobachtung
