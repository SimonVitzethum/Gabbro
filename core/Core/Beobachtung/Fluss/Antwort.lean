module

public import Core.Beobachtung.Fluss.Fragment

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Fragment)

/-- The current source fragment has no outside question instruction. Its runs
    cannot receive an answer, even if the hardware offers delivery. -/
def AntwortNIAussage : Prop :=
  ∀ (p : Fragment) (plattform : Plattform) (h : Umgebung) (ρ : Lauf (p.einheit plattform)),
    Laeufe (p.einheit plattform) h ρ → ∀ t a spur,
      ρ.zeit.spur t ≠ some (.antwort a, spur)

end Gabbro.Core.Beobachtung
