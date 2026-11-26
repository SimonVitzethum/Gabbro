module

public import Core.Ziel.Korrektheit.Instanz
public import Core.Beobachtung.Satz

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core

/-- The comparison run required by the existential half of the fixed NI statement.
    The concrete machine preserves the requested start and total public policy. -/
theorem zielNI_vergleichslauf (P : Katalog.Plattform) (B : FormBeleg)
    {E : (R₀ P B).Einheit} {H₁ H₂ : (R₀ P B).Umgebung}
    {ρ₁ : (R₀ P B).Lauf} {s₂ : (R₀ P B).Start}
    (lauf : (R₀ P B).Laeufe E H₁ ρ₁)
    (hardware : (R₀ P B).Hardware ((R₀ P B).katalog E) H₂)
    (umgebung : (R₀ P B).GleicheNiedrigeUmgebung E H₁ H₂)
    (zul : (R₀ P B).ZulStart E H₂ s₂) :
    ∃ ρ₂, (R₀ P B).Laeufe E H₂ ρ₂ ∧ (R₀ P B).start ρ₂ = s₂ ∧
      (R₀ P B).GleichePolitik E ρ₁ ρ₂ := by
  rcases ρ₁ with ⟨E₁, links⟩
  have tag : E₁ = E := lauf.1
  subst E₁
  obtain ⟨rechts, admitted, start, policy⟩ :=
    Beobachtung.vergleichslauf E lauf.2 hardware umgebung zul
  exact ⟨⟨E, rechts⟩, ⟨rfl, admitted⟩, start, ⟨rfl, rfl, policy⟩⟩

/-- The low traces of every admitted comparison of every accepted unit agree up to release. -/
def VergleichSpurenAussage : Prop :=
  ∀ (E : Ast.Semantik.Einheit), Annahme.Akzeptiert E →
    ∀ {H₁ H₂ : Katalog.Umgebung} {ρ₁ ρ₂ : Maschine.Lauf E},
      Beobachtung.Vergleich E H₁ H₂ ρ₁ ρ₂ →
      Beobachtung.NiedrigAequiv E (Beobachtung.NiedrigeBeob E ρ₁) (Beobachtung.NiedrigeBeob E ρ₂)

/-- Over the concrete frame, full NI is equivalent to the trace obligation.
    Existence follows from `zielNI_vergleichslauf`. -/
theorem zielNI_iff_vergleich (P : Katalog.Plattform) (B : FormBeleg) :
    Ziel.NI (R₀ P B) ↔ VergleichSpurenAussage := by
  constructor
  · intro ni E akzeptiert H₁ H₂ links rechts vergleich
    have result := ni E H₁ H₂ ⟨E, links⟩ rechts.start akzeptiert
      vergleich.links.1 vergleich.rechts.1 ⟨rfl, vergleich.links⟩ vergleich.umgebung
      vergleich.rechts.2.2.1 vergleich.start
    exact result.2 ⟨E, rechts⟩ ⟨rfl, vergleich.rechts⟩ rfl ⟨rfl, rfl, vergleich.politik⟩
  · intro vergleichsbeweis E H₁ H₂ ρ₁ s₂ akzeptiert _ hardware links umgebung zul niedrig
    refine ⟨zielNI_vergleichslauf P B links hardware umgebung zul, ?_⟩
    intro ρ₂ rechts start politik
    rcases ρ₁ with ⟨E₁, linksLauf⟩
    rcases ρ₂ with ⟨E₂, rechtsLauf⟩
    have tag₁ : E₁ = E := links.1
    have tag₂ : E₂ = E := rechts.1
    subst E₁
    subst E₂
    change rechtsLauf.start = s₂ at start
    rw [← start] at niedrig
    obtain ⟨_, tag, gleich⟩ := politik
    cases tag
    exact vergleichsbeweis E akzeptiert ⟨links.2, rechts.2, umgebung, niedrig, gleich⟩

end Gabbro.Core.Ziel.Korrektheit
