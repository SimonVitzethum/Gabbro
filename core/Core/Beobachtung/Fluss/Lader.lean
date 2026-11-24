module

public import Core.Beobachtung.Fluss.Fragment

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Fragment)

/-- The loader row of an admitted start yields the canonical initial state. -/
theorem fragment_lader_ni (p : Fragment) (plattform : Plattform)
    (quelle : StartFlussLokal (p.einheit plattform)) : LaderNIPflicht (p.einheit plattform) := by
  intro h₁ h₂ s₁ s₂ hw₁ hw₂ zul₁ zul₂ _ start
  rw [LaderSicht, LaderSicht, fragment_geladen p plattform hw₁ zul₁,
    fragment_geladen p plattform hw₂ zul₂]
  exact congrArg some (funext (quelle s₁ s₂ start).2.2.1)

end Gabbro.Core.Beobachtung
