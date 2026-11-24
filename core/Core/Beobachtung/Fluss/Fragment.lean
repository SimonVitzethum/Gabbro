module

public import Core.Beobachtung.Fluss.Satz
public import Core.Beobachtung.Fluss.Quellfragment
public import Core.Verfeinerung.Formen.Familie

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Fragment Befehl LokalFamilie)

def FamilienNI (familie : LokalFamilie) : Prop :=
  ∀ (p : Fragment) (plattform : Plattform) (f : Befehl), f.familie = familie →
    RegelFluss (p.einheit plattform) f → RegelNIPflicht (p.einheit plattform) f

def ProtokollwahlNI (form : SchrittWahl PUnit → Prop) : Prop :=
  ∀ (p : Fragment) (plattform : Plattform),
    let E := p.einheit plattform
    ∀ {h₁ h₂ ρ₁ ρ₂}, Vergleich E h₁ h₂ ρ₁ ρ₂ → ∀ predictor t w spur,
      ρ₁.zeit.spur t = some (w, spur) → form w →
      PraefixAbgedeckt E ρ₁ ρ₂ predictor t → PraefixAbgedeckt E ρ₁ ρ₂ predictor (t + 1)

/-- A form with an empty public event segment preserves prefix coverage even if the
    second execution has no corresponding hardware tick for the form. -/
theorem stummer_schritt_deckt {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type}
    {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    [DecidableEq L] {ρ₁ ρ₂ : Lauf E} {predictor t}
    (still : schrittBeob ρ₁ predictor t = []) (abgedeckt : PraefixAbgedeckt E ρ₁ ρ₂ predictor t) :
    PraefixAbgedeckt E ρ₁ ρ₂ predictor (t + 1) := by
  have gleich : NiedrigeBeob E ρ₁ predictor (t + 1) = NiedrigeBeob E ρ₁ predictor t := by
    change NiedrigeBeob E ρ₁ predictor t ++ schrittBeob ρ₁ predictor t = _
    rw [still, List.append_nil]
  unfold PraefixAbgedeckt
  rw [gleich]
  exact abgedeckt

end Gabbro.Core.Beobachtung
