/-
  File:      Core/Fortschritt/WarteBundle.lean
  Subject:   THE LOCK-WAIT PREMISE BUNDLE, JOINTLY SATISFIED (PERFECT-MODEL §3.7, step M8):
             a queued head waiter, a free lock with its take enabled, unit hold-bound data,
             and no owners — the witness that the bounds of `sperr_warte_schranke` hold together.
-/
module

public import Core.Fortschritt.WarteBeispiel

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Beobachtung

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

/-- The premise bundle of the waiting bound. -/
structure WartePraemissen (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F)
    (ρ : Maschine.Lauf E) (l : L) (c : Kontext) (i H : Nat) (a : Nat) : Prop where
  halte : E.schranken.halten l = some H
  hhalte : HalteSchranken E ρ
  hqueue : ∃ s, ρ.zeit.zustand a = some s ∧ (s.sperren l).schlange[i]? = some c
  hbleibt : ∀ t s, a ≤ t → ρ.zeit.zustand t = some s → (s.sperren l).besitzer ≠ some c →
    c ∈ (s.sperren l).schlange
  hgibt : ∀ h b s, a ≤ b → ρ.zeit.zustand b = some s → (s.sperren l).besitzer = some h →
    ∃ r, b ≤ r ∧
      (∃ s₁ s₂, ρ.zeit.zustand r = some s₁ ∧ ρ.zeit.zustand (r + 1) = some s₂ ∧
        (s₁.sperren l).Gibt h (s₂.sperren l)) ∧
      Kontextkosten ρ h b (r + 1 - b) ≤ H + 1
  hmono : ∀ t₁ t₂ s₁ s₂ (i₁ i₂ : Nat), a ≤ t₁ → t₁ ≤ t₂ → ρ.zeit.zustand t₁ = some s₁ →
    ρ.zeit.zustand t₂ = some s₂ → (s₁.sperren l).schlange[i₁]? = some c →
    (s₂.sperren l).schlange[i₂]? = some c → i₂ ≤ i₁

theorem e1_halte : HalteSchranken E_1 ρ' := by
  intro l c a n hcont
  cases l
  intro H' hH
  have h55 : (E_1).schranken.halten () = some 5 := rfl
  have hH5 : H' = 5 := Option.some.inj (hH.symm.trans h55)
  subst hH5
  by_cases hn : n = 0
  · subst hn
    have hkk : Kontextkosten ρ' c a 0 = 0 := rfl
    omega
  · have hlt : a < a + n := by omega
    obtain ⟨s, hzs, hown⟩ := hcont a (Nat.le_refl _) hlt
    have hfree := e1_besitzer_frei a s hzs
    rw [hfree] at hown
    cases hown

theorem e1_hbleibt : ∀ t s, 1 ≤ t → ρ'.zeit.zustand t = some s →
    (s.sperren ()).besitzer ≠ some A → A ∈ (s.sperren ()).schlange := by
  intro t s ht hzs _
  match t with
  | 0 => exact absurd ht (by decide)
  | 1 =>
    rw [ρ'_1] at hzs
    obtain rfl := Option.some.inj hzs
    exact List.mem_cons.mpr (Or.inl rfl)
  | _ + 2 =>
    rw [ρ'_ge _] at hzs
    obtain rfl := Option.some.inj hzs
    exact List.mem_cons.mpr (Or.inl rfl)

theorem e1_hgibt : ∀ h b s, 1 ≤ b → ρ'.zeit.zustand b = some s →
    (s.sperren ()).besitzer = some h →
    ∃ r, b ≤ r ∧
      (∃ s₁ s₂, ρ'.zeit.zustand r = some s₁ ∧ ρ'.zeit.zustand (r + 1) = some s₂ ∧
        (s₁.sperren ()).Gibt h (s₂.sperren ())) ∧
      Kontextkosten ρ' h b (r + 1 - b) ≤ 5 + 1 := by
  intro h b s hb hzs hown
  have hfree := e1_besitzer_frei b s hzs
  rw [hfree] at hown
  cases hown

theorem e1_hmono : ∀ t₁ t₂ s₁ s₂ (i₁ i₂ : Nat), 1 ≤ t₁ → t₁ ≤ t₂ → ρ'.zeit.zustand t₁ = some s₁ →
    ρ'.zeit.zustand t₂ = some s₂ → (s₁.sperren ()).schlange[i₁]? = some A →
    (s₂.sperren ()).schlange[i₂]? = some A → i₂ ≤ i₁ := by
  intro t₁ t₂ s₁ s₂ i₁ i₂ h1 h2 hz1 hz2 hq1 hq2
  have e1 : ∀ t s, 1 ≤ t → ρ'.zeit.zustand t = some s →
      (s.sperren ()) = ⟨none, [A]⟩ ∨ (s.sperren ()) = ⟨none, [A, B]⟩ := by
    intro t s ht hzs
    match t with
    | 0 => exact absurd ht (by decide)
    | 1 =>
      rw [ρ'_1] at hzs
      obtain rfl := Option.some.inj hzs
      exact Or.inl qc
    | _ + 2 =>
      rw [ρ'_ge _] at hzs
      obtain rfl := Option.some.inj hzs
      exact Or.inr qd
  rcases e1 t₁ s₁ h1 hz1 with h | h <;> rcases e1 t₂ s₂ (by omega) hz2 with h' | h'
  · rw [h] at hq1
    rw [h'] at hq2
    have i1 : i₁ = 0 := e1_index_null i₁ [A] (Or.inl rfl) hq1
    have i2 : i₂ = 0 := e1_index_null i₂ [A] (Or.inl rfl) hq2
    omega
  · rw [h] at hq1
    rw [h'] at hq2
    have i1 : i₁ = 0 := e1_index_null i₁ [A] (Or.inl rfl) hq1
    have i2 : i₂ = 0 := e1_index_null i₂ [A, B] (Or.inr rfl) hq2
    omega
  · rw [h] at hq1
    rw [h'] at hq2
    have i1 : i₁ = 0 := e1_index_null i₁ [A, B] (Or.inr rfl) hq1
    have i2 : i₂ = 0 := e1_index_null i₂ [A] (Or.inl rfl) hq2
    omega
  · rw [h] at hq1
    rw [h'] at hq2
    have i1 : i₁ = 0 := e1_index_null i₁ [A, B] (Or.inr rfl) hq1
    have i2 : i₂ = 0 := e1_index_null i₂ [A, B] (Or.inr rfl) hq2
    omega

/-- The premise bundle holds jointly: queued head waiter, free lock, take enabled,
    declared hold bound five, no owners. -/
theorem warte_praemissen_erfuellbar :
    ∃ (E : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit) (ρ : Maschine.Lauf E)
      (c : Kontext) (H a : Nat),
      WartePraemissen E ρ () c 0 H a ∧
      ∃ (b : Nat) (e : List Nat), a ≤ b ∧ (∃ s, ρ.zeit.zustand b = some s ∧
        ((s.sperren ()).besitzer = some c ∨
          (∃ h₀ r, (s.sperren ()).besitzer = none ∧ (s.sperren ()).schlange = h₀ :: r ∧
            ∃ s', (s.sperren ()).Nimmt h₀ s'))) ∧
        e.length ≤ 0 + 1 ∧ (∀ x ∈ e, x ≤ H + 1) ∧ e.sum ≤ (0 + 1) * (H + 1) := by
  refine ⟨E_1, ρ', A, 5, 1,
    ⟨e1halten, e1_halte, ⟨S_c, rfl, rfl⟩, e1_hbleibt, e1_hgibt, e1_hmono⟩, ?_⟩
  exact sperr_warte_schranke 0 0 1 (Nat.le_refl _) e1halten e1_halte ⟨S_c, rfl, rfl⟩
    e1_hbleibt e1_hgibt e1_hmono
end Gabbro.Core.Fortschritt
