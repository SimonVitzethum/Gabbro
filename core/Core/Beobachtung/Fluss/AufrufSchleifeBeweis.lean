module

public import Core.Beobachtung.Fluss.AufrufSchleife
public import Core.Beobachtung.Fluss.Antwort

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Fragment Befehl)

/-- Call and loop steps are silent: a canonical fragment's context step runs the
    internal plan and emits no low event. The coupling is therefore transported
    to the next cut by `stummer_schritt_koppelt`, the right run taking the same
    silent step at the entry context. -/
theorem aufrufSchleifeNI : AufrufSchleifeNIAussage := by
  classical
  intro p plattform f _ _ h₁ h₂ ρ₁ ρ₂ vergleich predictor t c w spur vor
    zustand kopf spurGlied kopplung
  exact stummer_schritt_koppelt vergleich zustand kopf spurGlied
    (antwortNI p plattform h₂ ρ₂ vergleich.rechts t · ·) kopplung

end Gabbro.Core.Beobachtung
