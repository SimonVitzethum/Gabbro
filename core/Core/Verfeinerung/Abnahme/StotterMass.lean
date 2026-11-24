module

public import Core.Verfeinerung.Formpflichten

@[expose] public section

namespace Gabbro.Core.Maschine.I

open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

/-- A form bounds the remaining private work at every cut with that ideal
    head. A marked tick spends one unit; other ticks cannot replenish it.
    Reset is permitted at the context's ideal step or at a crash. -/
def StotterMassAussage (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F) (f : F)
    (mass : Maschine.Lauf E → Lauf E → Kontext → Nat → Nat) : Prop :=
  ∀ h ρ η, Maschine.Laeufe E h ρ → Laufabgleich ρ η → BelegungGeprueft η →
    ∀ c t, E.system.kopf (η.zeit.zustand t) c = some f →
      mass ρ η c t ≤ E.stotterLaenge f ∧
      ((∀ w spur, η.zeit.spur t ≠ some (.kontext c w, spur)) →
        η.zeit.spur t ≠ some (.absturz, absturzSpur) →
        mass ρ η c (t + 1) + (if η.belegt t = some c then 1 else 0) ≤ mass ρ η c t)

theorem StotterMassAussage.schranke {f : F}
    {mass : Maschine.Lauf E → Lauf E → Kontext → Nat → Nat}
    (pflicht : StotterMassAussage E f mass) : RegelStotterSchranke E f := by
  intro h ρ η run matched checked c a n interval
  have budget (n : Nat) (int : Stotterintervall η c f a n) :
      zaehle (fun t => decide (η.belegt t = some c)) a n + mass ρ η c (a + n) ≤ mass ρ η c a := by
    induction n with
    | zero => simpa only [zaehle, Nat.add_zero, Nat.zero_add] using Nat.le_refl (mass ρ η c a)
    | succ n ih =>
      have prev := ih (fun t lo hi => int t lo (by omega))
      obtain ⟨head, noStep, noCrash⟩ := int (a + n) (by omega) (by omega)
      have spend := (pflicht h ρ η run matched checked c (a + n) head).2 noStep noCrash
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
    have bound := (pflicht h ρ η run matched checked c a head).1
    omega

end Gabbro.Core.Maschine.I
