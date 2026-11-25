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

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
variable {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

/-- A fair tail spliced after one prefix step keeps scheduler fairness: duties and
    opportunities shift by one tick, and service in the tail serves the spliced run. -/
theorem voran1_fair {hw : Katalog.HwLauf} {s : Katalog.AussenStart}
    {s₀ : Option (Maschine.Zustand L Ort Wert Raum Lok Grund)}
    {e₀ : Maschine.SchrittWahl Wahl × Maschine.SchrittSpur Ort Wert}
    {tail : Zeitlauf (fun t => Maschine.Lauffolge E hw (t + 1))}
    (h₀ : Maschine.Lauffolge E hw 0 s₀ e₀ (tail.zustand 0))
    (tailFair : Maschine.ShiftFair E hw 1 s tail) :
    Maschine.SchedulerFair E ⟨s, hw, voran tail s₀ e₀ h₀⟩ := by
  intro a c dle oppd n hn
  have dle' : ∀ t, a ≤ t → ∃ z, tail.zustand t = some z ∧
      (∃ k, (z.kerne k).laeuft = some c) ∧ z.status c = .laeuft ∧
      (hw.angebot (t + 1)).crash = false ∧
      ∃ w plan u spur s', E.system.ImplSchritt c z w [plan] u ∧
        Maschine.FuehrtSchrittAus E.einrichtung (t + 1) c z u plan spur s' := by
    intro t ht
    obtain ⟨z, eq, disp, live, crash, w, plan, u, spur, s', regel, aus⟩ := dle (t + 1) (Nat.le_succ_of_le ht)
    have : (voran tail s₀ e₀ h₀).zustand (t + 1) = tail.zustand t := rfl
    rw [this] at eq
    exact ⟨z, eq, disp, live, crash, w, plan, u, spur, s', regel, aus⟩
  have oppd' : ∀ m, a ≤ m → ∃ t, m ≤ t ∧ ∃ k, hw.gelegenheit (t + 1) k ∧
      ∃ z, tail.zustand t = some z ∧ (z.kerne k).laeuft = some c := by
    intro m _
    obtain ⟨T, hT, k, opp, z, eq, disp⟩ := oppd (max (m + 1) a) (Nat.le_max_right _ _)
    obtain ⟨t', rfl⟩ : ∃ t', T = t' + 1 := ⟨T - 1, by omega⟩
    have : (voran tail s₀ e₀ h₀).zustand (t' + 1) = tail.zustand t' := rfl
    rw [this] at eq
    exact ⟨t', by omega, k, opp, z, eq, disp⟩
  obtain ⟨t', ht', w, spur, step⟩ := tailFair a c dle' oppd' n hn
  have spurEq : (voran tail s₀ e₀ h₀).spur (t' + 1) = tail.spur t' := rfl
  rw [← spurEq] at step
  exact ⟨t' + 1, Nat.le_trans ht' (Nat.le_succ _), w, spur, step⟩

/-- Two prefix steps spliced onto a fair tail. The inner step relation is pinned
    explicitly so higher-order unification never has to guess it. -/
def voran2 {hw : Katalog.HwLauf}
    {s₀ s₁ : Option (Maschine.Zustand L Ort Wert Raum Lok Grund)}
    {e₀ e₁ : Maschine.SchrittWahl Wahl × Maschine.SchrittSpur Ort Wert}
    {tail : Zeitlauf (fun t => Maschine.Lauffolge E hw (t + 2))}
    (h₁ : Maschine.Lauffolge E hw 1 s₁ e₁ (tail.zustand 0))
    (s₂ : Option (Maschine.Zustand L Ort Wert Raum Lok Grund))
    (e₂ : Maschine.SchrittWahl Wahl × Maschine.SchrittSpur Ort Wert)
    (h₀ : Maschine.Lauffolge E hw 0 s₂ e₂ s₁) : Zeitlauf (Maschine.Lauffolge E hw) :=
  voran (voran (schritt := fun t => Maschine.Lauffolge E hw (t + 1)) tail s₁ e₁ h₁) s₂ e₂ h₀

/-- A fair tail spliced after two prefix steps keeps scheduler fairness. -/
theorem voran2_fair {hw : Katalog.HwLauf} {s : Katalog.AussenStart}
    {s₀ s₁ : Option (Maschine.Zustand L Ort Wert Raum Lok Grund)}
    {e₀ e₁ : Maschine.SchrittWahl Wahl × Maschine.SchrittSpur Ort Wert}
    {tail : Zeitlauf (fun t => Maschine.Lauffolge E hw (t + 2))}
    (h₁ : Maschine.Lauffolge E hw 1 s₁ e₁ (tail.zustand 0))
    (h₀ : Maschine.Lauffolge E hw 0 s₀ e₀ s₁)
    (tailFair : Maschine.ShiftFair E hw 2 s tail) :
    Maschine.SchedulerFair E ⟨s, hw, voran2 tail s₁ e₁ h₁ s₀ e₀ h₀⟩ := by
  intro a c dle oppd n hn
  have dle' : ∀ t, a ≤ t → ∃ z, tail.zustand t = some z ∧
      (∃ k, (z.kerne k).laeuft = some c) ∧ z.status c = .laeuft ∧
      (hw.angebot (t + 2)).crash = false ∧
      ∃ w plan u spur s', E.system.ImplSchritt c z w [plan] u ∧
        Maschine.FuehrtSchrittAus E.einrichtung (t + 2) c z u plan spur s' := by
    intro t ht
    obtain ⟨z, eq, disp, live, crash, w, plan, u, spur, s', regel, aus⟩ :=
      dle (t + 2) (Nat.le_trans ht (Nat.le_add_right _ _))
    have : (voran2 tail s₁ e₁ h₁ s₀ e₀ h₀).zustand (t + 2) = tail.zustand t := rfl
    rw [this] at eq
    exact ⟨z, eq, disp, live, crash, w, plan, u, spur, s', regel, aus⟩
  have oppd' : ∀ m, a ≤ m → ∃ t, m ≤ t ∧ ∃ k, hw.gelegenheit (t + 2) k ∧
      ∃ z, tail.zustand t = some z ∧ (z.kerne k).laeuft = some c := by
    intro m _
    obtain ⟨T, hT, k, opp, z, eq, disp⟩ := oppd (max (m + 2) a) (Nat.le_max_right _ _)
    obtain ⟨t', rfl⟩ : ∃ t', T = t' + 2 := ⟨T - 2, by omega⟩
    have : (voran2 tail s₁ e₁ h₁ s₀ e₀ h₀).zustand (t' + 2) = tail.zustand t' := rfl
    rw [this] at eq
    exact ⟨t', by omega, k, opp, z, eq, disp⟩
  obtain ⟨t', ht', w, spur, step⟩ := tailFair a c dle' oppd' n hn
  have spurEq : (voran2 tail s₁ e₁ h₁ s₀ e₀ h₀).spur (t' + 2) = tail.spur t' := rfl
  rw [← spurEq] at step
  exact ⟨t' + 2, Nat.le_trans ht' (Nat.le_add_right _ _), w, spur, step⟩

end Gabbro.Core.Sicherheit
