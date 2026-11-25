module

public import Core.Beobachtung.Nichtinterferenz

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}

/-- Ledger equality for the outside ledgers that `Kopplung` does not cover:
    the pending questions, the outside history, the arrived answers and the
    per-context consumption counters. -/
def GeraeteLedgerGleichAussage (v u : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  v.fragen = u.fragen ∧ v.verlauf = u.verlauf ∧ v.antworten = u.antworten ∧
    v.verbraucht = u.verbraucht

theorem GeraeteLedgerGleichAussage.refl (v : Zustand L Ort Wert Raum Lok Grund) :
    GeraeteLedgerGleichAussage v v :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem GeraeteLedgerGleichAussage.symm {v u : Zustand L Ort Wert Raum Lok Grund}
    (h : GeraeteLedgerGleichAussage v u) : GeraeteLedgerGleichAussage u v := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1.symm, h2.symm, h3.symm, h4.symm⟩

/-- The device-strengthened coupling: `Kopplung` plus ledger equality of the
    two states at the same cut `t`, plus booking equality (the device authority
    that enables issue and consume). The prefix and state parts are unchanged;
    only the four ledgers and the booking are added. `Kopplung` itself is untouched. -/
def GeraeteKopplungAussage (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (ρ₁ ρ₂ : Lauf E) (predictor : Praediktor) (t u : Nat) : Prop :=
  Kopplung E ρ₁ ρ₂ predictor t u ∧
    ∀ v w, ρ₁.zeit.zustand t = some v → ρ₂.zeit.zustand t = some w →
      GeraeteLedgerGleichAussage v w ∧ v.buchung = w.buchung

theorem geraeteKopplung_kopplung {ρ₁ ρ₂ : Lauf E} {predictor : Praediktor} {t u : Nat}
    (h : GeraeteKopplungAussage E ρ₁ ρ₂ predictor t u) :
    Kopplung E ρ₁ ρ₂ predictor t u :=
  h.1

theorem geraeteKopplung_ledger {ρ₁ ρ₂ : Lauf E} {predictor : Praediktor} {t u : Nat}
    (h : GeraeteKopplungAussage E ρ₁ ρ₂ predictor t u) {v w}
    (hv : ρ₁.zeit.zustand t = some v) (hw : ρ₂.zeit.zustand t = some w) :
    GeraeteLedgerGleichAussage v w :=
  (h.2 v w hv hw).1

theorem geraeteKopplung_buchung {ρ₁ ρ₂ : Lauf E} {predictor : Praediktor} {t u : Nat}
    (h : GeraeteKopplungAussage E ρ₁ ρ₂ predictor t u) {v w}
    (hv : ρ₁.zeit.zustand t = some v) (hw : ρ₂.zeit.zustand t = some w) :
    v.buchung = w.buchung :=
  (h.2 v w hv hw).2

end Gabbro.Core.Beobachtung
