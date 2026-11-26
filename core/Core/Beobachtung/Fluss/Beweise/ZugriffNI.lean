module

public import Core.Beobachtung.Fluss.Beweise.Zugriff.Lauf
public import Core.Beobachtung.Fluss.Beweise.Zugriff.GraphKopplungBeweis
public import Core.Ziel.Korrektheit.Beweise2.ZugriffSchrittExistiert

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Fragment Befehl)

theorem zugriffNI : ZugriffNIAussage := by
  intro p plattform f familie fluss h₁ h₂ ρ₁ ρ₂ vergleich predictor t c w spur vor
    zustand kopf spurGlied kopplung
  cases f with
  | zugriff z =>
      exact zugriff_schritt_koppelt
        Gabbro.Core.Ziel.Korrektheit.zugriffSchrittExistiert speicherGraphKopplung
        p plattform z vergleich fluss zustand kopf spurGlied kopplung
  | _ => cases familie

end Gabbro.Core.Beobachtung
