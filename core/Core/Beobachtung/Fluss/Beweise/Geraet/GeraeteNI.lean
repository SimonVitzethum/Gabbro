module

public import Core.Beobachtung.Fluss.Geraet
public import Core.Beobachtung.Fluss.Beweise.GeraetKopplung
public import Core.Beobachtung.Fluss.Beweise.Geraet.LockstepKopplungAlle

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast

/-- The device unit discharges its form duty: a context tick keeps the coupling.
    The strengthened coupling is rebuilt at the cut `t` from the comparison
    (`geraete_kopplung_alle`), the context preservation unit is applied once, and the
    result is projected back to `Kopplung`. The `RegelFluss` premise and the coupling
    premise are redundant: the step-level flow is already proved in `geraeteSchrittNI`
    and the run-level lifting in `geraete_kontext_erhalt`. -/
theorem geraeteNI : GeraeteNIAussage := by
  intro k scope locals d regelfluss h₁ h₂ ρ₁ ρ₂ vergleich predictor t c w spur vor zustand kopf spurGlied kopplung
  have gall := geraete_kopplung_alle (k := k) (scope := scope) (locals := locals) (d := d)
    h₁ h₂ ρ₁ ρ₂ vergleich predictor t
  exact geraeteKopplung_kopplung
    (geraete_kontext_erhalt (k := k) (scope := scope) locals d
      h₁ h₂ ρ₁ ρ₂ vergleich predictor t c w spur gall spurGlied)

end Gabbro.Core.Beobachtung
