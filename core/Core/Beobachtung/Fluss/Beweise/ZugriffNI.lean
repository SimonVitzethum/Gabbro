/-
  THE ACCESS-STEP TWO-RUN PRESERVATION, WITH NO OPEN PREMISE. The concrete memory form is the
  observable step case of M9: the run-level coupling proof `zugriff_schritt_koppelt` needs the
  step-existence of every access form and the graph coupling of public cells; both are proved.
  The packet below fixes the form to `.zugriff` (thread lifecycle and outside questions have their
  own label rules and are not claimed here) and discharges both premises once, for dependent use
  by the fragment NI leg.
-/
module

public import Core.Beobachtung.Fluss.Beweise.Zugriff.Lauf
public import Core.Beobachtung.Fluss.Beweise.Zugriff.GraphKopplungBeweis
public import Core.Ziel.Korrektheit.Beweise2.ZugriffSchrittExistiert

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Fragment Befehl)

/-- Two-run preservation of one concrete memory instruction, under its flow rule. -/
def ZugriffFormNIAussage : Prop :=
  ∀ (p : Fragment) (plattform : Plattform) (z : Ast.Semantik.Zugriffsform),
    RegelFluss (p.einheit plattform) (Befehl.zugriff z) →
      RegelNIPflicht (p.einheit plattform) (Befehl.zugriff z)

theorem zugriffFormNI : ZugriffFormNIAussage := by
  intro p plattform z fluss
  intro h₁ h₂ ρ₁ ρ₂ vergleich predictor t c w spur vor
    zustand kopf spurGlied kopplung
  exact zugriff_schritt_koppelt
    Gabbro.Core.Ziel.Korrektheit.zugriffSchrittExistiert speicherGraphKopplung
    p plattform z vergleich fluss zustand kopf spurGlied kopplung

end Gabbro.Core.Beobachtung
