module

public import Core.Verfeinerung.Stottern
public import Mathlib.Data.Set.Card

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine

/-- An absent resource limit is open; an explicitly declared zero is a limit. -/
def UnterGrenze (grenze : Option Nat) (bedarf : Nat) : Prop :=
  ∀ n, grenze = some n → bedarf ≤ n

/-- Live allocation cells are identified by object and offset. Revoked allocations contribute
    nothing; an infinite population cannot satisfy a finite memory bound. -/
def LebendeZellen (s : Zustand L Ort Wert Raum Lok Grund) : Set (Nat × Nat) :=
  { z | s.rechte.lebt z.1 = true ∧ z.2 < (s.buchung.umfang z.1).length }

/-- The deadline is guaranteed only if a selected duration row entails it. The end check in
    the fallback case still uses the measured clock. The cost ceiling applies to the selected
    fallback from the check onward, irrespective of the hardware delay in the body. -/
def ZeitInSchranken (max : Option Nat) (d : Zeitdeklaration) (phase : Zeitphase)
    (anfang cut : Nat) (clock kosten : Nat → Nat) : Prop :=
  anfang ≤ cut ∧ clock anfang ≤ clock cut ∧
    match phase with
    | .rumpf => ∀ n, max = some n → n ≤ d.frist → clock cut - clock anfang ≤ n
    | .rechtzeitig t =>
      anfang ≤ t ∧ t ≤ cut ∧ clock anfang ≤ clock t ∧ clock t ≤ clock cut ∧
        clock t - clock anfang ≤ d.frist ∧
        (∀ n, max = some n → n ≤ d.frist → clock t - clock anfang ≤ n)
    | .late t =>
      anfang ≤ t ∧ t ≤ cut ∧ clock anfang ≤ clock t ∧ clock t ≤ clock cut ∧
        d.frist < clock t - clock anfang ∧
        (∀ n, max = some n → d.frist < n) ∧ kosten t ≤ d.lateKosten

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}

/-- One unit of abstract execution cost per occupied machine tick. An unused hardware
    opportunity has no abstract cost, even though its clock can advance. -/
def Laufkosten (ρ : Lauf E) (anfang laenge : Nat) : Nat :=
  I.zaehle (fun t => (ρ.zeit.spur t).isSome) anfang laenge

def Kontextkosten (ρ : Lauf E) (c : Kontext) (anfang laenge : Nat) : Nat :=
  I.zaehle (fun t =>
    match ρ.zeit.spur t with
    | some (.kontext d _, _) => decide (c = d)
    | some (.antwort _, _) | some (.interrupt _, _) | some (.absturz, _) | none => false)
    anfang laenge

/-- A declared hold bound counts the owning context's steps while it continuously holds the lock.
    This abstract hold cost is independent of delivery and core delays. -/
def HalteSchranken (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (ρ : Lauf E) : Prop :=
  ∀ l c a n, (∀ t, a ≤ t → t < a + n →
    ∃ s, ρ.zeit.zustand t = some s ∧ (s.sperren l).besitzer = some c) →
    UnterGrenze (E.schranken.halten l) (Kontextkosten ρ c a n)

/-- All finite prefixes of the same concrete run meet the unit's declarations, on unfair runs
    as well. Bounds cannot be chosen after seeing the run. A failed load has no live resources. -/
def ImSchranken (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (ρ : Lauf E) : Prop :=
  HalteSchranken E ρ ∧
  (∀ t, UnterGrenze E.schranken.kosten (Laufkosten ρ 0 t)) ∧
  ∀ t s, ρ.zeit.zustand t = some s →
    (∀ n, E.schranken.speicher = some n → (LebendeZellen s).encard ≤ n) ∧
    (∀ c, UnterGrenze E.schranken.stapel (E.schranken.stapelTiefe (s.lokal c))) ∧
    (∀ c m, m ∈ E.schranken.zeitstand (s.lokal c) →
      ∃ d, E.schranken.zeit m.block = some d ∧
        ZeitInSchranken (E.katalog.dauerMaximum d.zeile) d m.phase m.anfang t
          (fun i => (ρ.hw.angebot i).cycles) (fun i => Kontextkosten ρ c i (t - i)))

theorem zeit_rechtzeitig_erfuellbar :
    ZeitInSchranken (some 2) ⟨0, 2, 1⟩ (.rechtzeitig 2) 0 2 id (fun _ => 0) ∧
      ¬ ZeitInSchranken (some 1) ⟨0, 2, 1⟩ (.rechtzeitig 2) 0 2 id (fun _ => 0) := by
  refine ⟨⟨by decide, by decide, ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩⟩, ?_⟩
  · intro n equal _
    exact (Option.some.inj equal) ▸ Nat.le_refl 2
  · intro h
    exact (by decide : ¬ 2 ≤ 1) (h.2.2.2.2.2.2.2 1 rfl (by decide))

theorem zeit_late_erfuellbar :
    ZeitInSchranken none ⟨0, 2, 1⟩ (.late 3) 0 4 id (fun _ => 1) ∧
      ¬ ZeitInSchranken none ⟨0, 2, 1⟩ (.late 3) 0 4 id (fun _ => 2) ∧
      ¬ ZeitInSchranken (some 2) ⟨0, 2, 1⟩ (.late 3) 0 4 id (fun _ => 1) := by
  constructor
  · refine ⟨by decide, by decide, ?_⟩
    change 0 ≤ 3 ∧ 3 ≤ 4 ∧ 0 ≤ 3 ∧ 3 ≤ 4 ∧ 2 < 3 ∧
      (∀ n : Nat, none = some n → 2 < n) ∧ 1 ≤ 1
    exact ⟨by decide, by decide, by decide, by decide, by decide, (fun _ no => nomatch no), by decide⟩
  · constructor
    · intro h
      exact (by decide : ¬ 2 ≤ 1) h.2.2.2.2.2.2.2.2
    · intro h
      exact (Nat.lt_irrefl 2) (h.2.2.2.2.2.2.2.1 2 rfl)

end Gabbro.Core.Beobachtung
