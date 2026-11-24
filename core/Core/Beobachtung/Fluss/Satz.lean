module

public import Core.Beobachtung.Nichtinterferenz
public import Core.Annahme.Annahme

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
variable (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)

/-- The actual initial observation includes loader failure as well as the public initial memory. -/
def LaderSicht (h : Umgebung) (s : AussenStart) : Option (Ort → Option Wert) :=
  (E.laden s (h.lade E.bild)).map fun z x => sichtbar (E.etiketten.ort x) (z.initial x)

def LaderNIPflicht : Prop :=
  ∀ h₁ h₂ s₁ s₂, Hardware E.katalog h₁ → Hardware E.katalog h₂ →
    E.ZulStart h₁ s₁ → E.ZulStart h₂ s₂ →
    GleicheNiedrigeUmgebung E h₁ h₂ → NiedrigGleich E s₁ s₂ →
    LaderSicht E h₁ s₁ = LaderSicht E h₂ s₂

def ProtokollNIPflicht : Prop :=
  ∀ {h₁ h₂ ρ₁ ρ₂}, Vergleich E h₁ h₂ ρ₁ ρ₂ → ∀ predictor t w spur,
    ρ₁.zeit.spur t = some (w, spur) → ProtokollWahl w →
    PraefixAbgedeckt E ρ₁ ρ₂ predictor t → PraefixAbgedeckt E ρ₁ ρ₂ predictor (t + 1)

def Nichtinterferent : Prop :=
  ∀ h₁ h₂ ρ₁ s₂, Hardware E.katalog h₁ → Hardware E.katalog h₂ →
    Laeufe E h₁ ρ₁ → GleicheNiedrigeUmgebung E h₁ h₂ → E.ZulStart h₂ s₂ →
    NiedrigGleich E ρ₁.start s₂ →
    (∃ ρ₂, Laeufe E h₂ ρ₂ ∧ ρ₂.start = s₂ ∧ GleichePolitik E ρ₁ ρ₂) ∧
      ∀ ρ₂, Laeufe E h₂ ρ₂ → ρ₂.start = s₂ → GleichePolitik E ρ₁ ρ₂ →
        NiedrigAequiv E (NiedrigeBeob E ρ₁) (NiedrigeBeob E ρ₂)

private theorem anfangsbeob (ρ : Lauf E) (h : Umgebung) (lauf : Laeufe E h ρ) (p : Praediktor) :
    NiedrigeBeob E ρ p 0 =
      [match LaderSicht E h ρ.start with
        | none => .ladefehler
        | some inhalt => .anfangsspeicher inhalt] := by
  simp only [NiedrigeBeob, NiedrigeBeob.praefix, lauf.2.2.2, LaderSicht]
  cases E.laden ρ.start (h.lade E.bild) <;> rfl

theorem anfang_aus_lader (pflicht : LaderNIPflicht E) {h₁ h₂ ρ₁ ρ₂}
    (v : Vergleich E h₁ h₂ ρ₁ ρ₂) (p : Praediktor) : PraefixAbgedeckt E ρ₁ ρ₂ p 0 := by
  have gleich := pflicht h₁ h₂ ρ₁.start ρ₂.start
    v.links.1 v.rechts.1 v.links.2.2.1 v.rechts.2.2.1 v.umgebung v.start
  unfold PraefixAbgedeckt
  refine ⟨0, ?_⟩
  rw [anfangsbeob E ρ₁ h₁ v.links p, anfangsbeob E ρ₂ h₂ v.rechts p, gleich, List.take_length]
  exact .cons (.gleich _) .nil

/-- Source acceptance supplies the initialization and form rules. The two implementation
    bridges transport those rules to the admitted runs, including separate protocol steps. -/
theorem ni_akzeptierter_einheit (h : Akzeptiert E)
    (lader : StartFlussLokal E → LaderNIPflicht E)
    (formen : ∀ f, RegelFluss E f → RegelNIPflicht E f)
    (protokoll : ProtokollNIPflicht E) : Nichtinterferent E := by
  have fluss := akzeptiert_fluss h
  have pflichten : NIPflichten E :=
    ⟨anfang_aus_lader E (lader fluss.1), fun f => formen f (fluss.2 f), protokoll⟩
  intro _ _ _ _ _ hardware lauf umgebung zul start
  exact ni_aus_pflichten pflichten lauf hardware umgebung zul start

end Gabbro.Core.Beobachtung
