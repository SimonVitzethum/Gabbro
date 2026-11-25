module

public import Core.Verfeinerung.Formpflichten

@[expose] public section

namespace Gabbro.Core.Maschine.I

open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

/-- A mass function is a proof device for the per-rule stutter bound. It is bounded
    at every ideal head, and every marked private tick that is neither an ideal
    step nor a crash spends one unit and cannot be replenished. No caller-supplied
    assertion remains: the conclusion is the language's `RegelStotterSchranke`. -/
theorem stotterSchranke_aus_mass {f : F}
    {mass : Maschine.Lauf E → Lauf E → Kontext → Nat → Nat}
    (schranke : ∀ h ρ η, Maschine.Laeufe E h ρ → Laufabgleich ρ η → BelegungGeprueft η →
      ∀ c t, E.system.kopf (η.zeit.zustand t) c = some f → mass ρ η c t ≤ E.stotterLaenge f)
    (verbrauch : ∀ h ρ η, Maschine.Laeufe E h ρ → Laufabgleich ρ η → BelegungGeprueft η →
      ∀ c t, E.system.kopf (η.zeit.zustand t) c = some f →
        (∀ w spur, η.zeit.spur t ≠ some (.kontext c w, spur)) →
        η.zeit.spur t ≠ some (.absturz, absturzSpur) →
        mass ρ η c (t + 1) + (if η.belegt t = some c then 1 else 0) ≤ mass ρ η c t) :
    RegelStotterSchranke E f := by
  intro h ρ η run matched checked c a n interval
  have budget (n : Nat) (int : Stotterintervall η c f a n) :
      zaehle (fun t => decide (η.belegt t = some c)) a n + mass ρ η c (a + n) ≤ mass ρ η c a := by
    induction n with
    | zero => simpa only [zaehle, Nat.add_zero, Nat.zero_add] using Nat.le_refl (mass ρ η c a)
    | succ n ih =>
      have prev := ih (fun t lo hi => int t lo (by omega))
      obtain ⟨head, noStep, noCrash⟩ := int (a + n) (by omega) (by omega)
      have spend := verbrauch h ρ η run matched checked c (a + n) head noStep noCrash
      by_cases mark : η.belegt (a + n) = some c
      · simp only [if_pos mark, Nat.add_assoc] at spend
        simp only [zaehle, decide_eq_true mark, if_true]
        omega
      · simp only [if_neg mark, Nat.add_zero, Nat.add_assoc] at spend
        simp only [zaehle, decide_eq_false mark, Bool.false_eq_true, if_false, Nat.add_zero]
        omega
  cases n with
  | zero => exact Nat.zero_le _
  | succ n =>
    have head := (interval a (Nat.le_refl _) (by omega)).1
    have spent := budget (n + 1) interval
    have bound := schranke h ρ η run matched checked c a head
    omega

end Gabbro.Core.Maschine.I
