module

public import Core.Sicherheit.Einheit

@[expose] public section

namespace Gabbro.Core.Sicherheit

open Maschine Katalog

variable {S Ev : Type}

def voran {schritt : Nat → S → Ev → S → Prop}
    (rest : Zeitlauf (fun t => schritt (t + 1))) (s : S) (e : Ev)
    (anfang : schritt 0 s e (rest.zustand 0)) : Zeitlauf schritt where
  zustand
    | 0 => s
    | t + 1 => rest.zustand t
  spur
    | 0 => some e
    | t + 1 => rest.spur t
  takt
    | 0 => .schritt rfl anfang
    | t + 1 => by
      cases rest.takt t with
      | schritt label step => exact .schritt label step
      | wartet label eq stuck => exact .wartet label eq stuck

/-- Extend a chosen two-transition prefix to a maximal run. -/
theorem praefix_erfuellbar {schritt : Nat → S → Ev → S → Prop}
    {s₀ s₁ s₂ : S} {e₀ e₁ : Ev} (h₀ : schritt 0 s₀ e₀ s₁) (h₁ : schritt 1 s₁ e₁ s₂) :
    ∃ ρ : Zeitlauf schritt, ρ.zustand 0 = s₀ ∧ ρ.spur 0 = some e₀ ∧
      ρ.zustand 1 = s₁ ∧ ρ.spur 1 = some e₁ ∧ ρ.zustand 2 = s₂ := by
  obtain ⟨rest, eq⟩ := Zeitlauf.existiert (fun t => schritt (t + 1 + 1)) s₂
  let after := voran (schritt := fun t => schritt (t + 1)) rest s₁ e₁ (eq.symm ▸ h₁)
  exact ⟨voran after s₀ e₀ h₀, rfl, rfl, rfl, rfl, eq⟩

theorem schritt_erfuellbar {schritt : Nat → S → Ev → S → Prop}
    {s₀ s₁ : S} {e₀ : Ev} (h₀ : schritt 0 s₀ e₀ s₁) :
    ∃ ρ : Zeitlauf schritt, ρ.zustand 0 = s₀ ∧ ρ.spur 0 = some e₀ ∧ ρ.zustand 1 = s₁ := by
  obtain ⟨rest, eq⟩ := Zeitlauf.existiert (fun t => schritt (t + 1)) s₁
  exact ⟨voran rest s₀ e₀ (eq.symm ▸ h₀), rfl, rfl, eq⟩

end Gabbro.Core.Sicherheit
