module

public import Core.Beobachtung.Fluss.Fragment
public import Core.Beobachtung.Fluss.Beweise.Antwort

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Fragment Befehl)

def VarianteNIAussage : Prop :=
  FamilienNI .variante

/-- Variant steps are silent: the coupling is preserved through the lockstep. -/
theorem varianteNI : VarianteNIAussage := by
  classical
  intro p plattform f familie _ h₁ h₂ ρ₁ ρ₂ vergleich predictor t c w spur vor
    zustand kopf spurGlied kopplung
  exact stummer_schritt_koppelt vergleich zustand kopf spurGlied
    (antwortNI p plattform h₂ ρ₂ vergleich.rechts t · ·) (Befehl.privat_von_familie (fun e => by rw [familie] at e; cases e)) kopplung

end Gabbro.Core.Beobachtung
