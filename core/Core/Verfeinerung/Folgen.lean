module

public import Core.Ideal.Komposition
public import Core.Verfeinerung.Maschine

@[expose] public section

namespace Gabbro.Core.Maschine.I

open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F Obs : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}
variable {ρ : Maschine.Lauf E} {η : Lauf E}
variable {lokal : LokalerBezug Lok} {mass : PrivatMass L Ort Wert Raum Lok Grund}

/-- At the image of each concrete cut, the ideal state is the state at that
    hardware tick, even if the most recent ideal transition was earlier. -/
theorem Laufabgleich.schnitt (h : Laufabgleich ρ η lokal mass) (k : Maschine.Schnitt E ρ) :
    ∃ s, ρ.zeit.zustand k.val = some s ∧
      Zustandsbezug lokal s (η.zeit.zustand (Zeitlauf.schnittBild ρ.zeit η.zeit k).val) := by
  obtain ⟨s, load, rel⟩ := h.zustand k.val
  exact ⟨s, load, (η.zeit.letzterSchnitt_zustand k.val).symm ▸ rel⟩

theorem Laufabgleich.schnitt_deckt (h : Laufabgleich ρ η lokal mass) :
    Function.Surjective (Zeitlauf.schnittBild ρ.zeit η.zeit) :=
  Zeitlauf.schnittBild_deckt ρ.zeit η.zeit fun t pause => (h.spur t).gedeckt pause

theorem SpurAbgleich.beobachtung {v n : Nat} {c : Option (SchrittSpur Ort Wert)}
    {i : Option (SchrittWahl Wahl × SchrittSpur Ort Wert)} (h : SpurAbgleich v n c i)
    (sicht : SchrittSpur Ort Wert → List Obs) (privat : sicht ⟨[], []⟩ = []) :
    c.elim [] sicht = i.elim [] (sicht ∘ Prod.snd) := by
  cases h with
  | pause => rfl
  | privat _ => exact privat
  | schritt _ _ => rfl

/-- Equality of the entire ordered observed prefix. In particular either
    projection of the M4 step trace, or a projection keeping both, may be used. -/
theorem Laufabgleich.beobachtung (h : Laufabgleich ρ η lokal mass)
    (sicht : SchrittSpur Ort Wert → List Obs) (privat : sicht ⟨[], []⟩ = []) (k : Maschine.Schnitt E ρ) :
    Zeitlauf.praefix (fun t => (ρ.zeit.spur t).elim [] sicht) k.val =
      Zeitlauf.praefix (fun t => (η.zeit.spur t).elim [] (sicht ∘ Prod.snd))
        (Zeitlauf.schnittBild ρ.zeit η.zeit k).val := by
  let beob := fun t => (η.zeit.spur t).elim [] (sicht ∘ Prod.snd)
  have gleich : (fun t => (ρ.zeit.spur t).elim [] sicht) = beob :=
    funext fun t => (h.spur t).beobachtung sicht privat
  rw [gleich]
  exact (η.zeit.praefix_letzterSchnitt beob (fun t no => by simp only [beob, no, Option.elim]) k.val).symm

/-- The crash cut is matched at the same tick, with the same persistence event,
    and the recovery continuations start in one and the same state. -/
theorem Laufabgleich.absturz (h : Laufabgleich ρ η lokal mass) {t : Nat}
    (offer : AbsturzAngeboten E.katalog ρ.hw t) :
    ρ.zeit.spur t = some absturzSpur ∧ η.zeit.spur t = some (.absturz, absturzSpur) ∧
      ρ.zeit.zustand (t + 1) = some (η.zeit.zustand (t + 1)) := by
  obtain ⟨s, load, rel⟩ := h.zustand t
  have shared := rel.1
  change { s with lokal := (η.zeit.zustand t).lokal } = η.zeit.zustand t at shared
  exact absturz_im_lauf h.hardware.symm offer load rel.1.aussen
    (congrArg (fun z => nachAbsturz z.persistenz) shared)

/-- A persistent live dispatch on a fair physical core reaches an ideal
    progress alternative other than a withheld opportunity. -/
theorem Laufabgleich.fortschritt_am_angebot (h : Laufabgleich ρ η lokal mass) (run : Laeufe E η)
    (fair : FairLaeufe E.katalog η.umgebung ρ.hw)
    (fertig : ∀ s c, E.system.kopf s c = none → E.system.fertig s c)
    (regeln : ∀ i, Gabbro.Core.Ideal.RegelFortschritt E.system i)
    (komponierbar : ∀ i, RegelKomponierbar E.einrichtung E.system i)
    {kern t : Nat} {c : Kontext} (physical : kern < η.umgebung.kernzahl)
    (dispatch : ∀ i, t ≤ i → ∀ s, ρ.zeit.zustand i = some s →
      (s.kerne kern).laeuft = some c ∧ s.status c = .laeuft) :
    ∃ i, t ≤ i ∧ let s := η.zeit.zustand i
      (∃ spur next, Schritt E.einrichtung E.system E.katalog η.hw i s (.absturz, spur) next) ∨
      E.system.fertig s c ∨ (∃ b, E.system.blockiert s c b) ∨
      (∃ w spur next, Schritt E.einrichtung E.system E.katalog η.hw i s (.kontext c w, spur) next) := by
  obtain ⟨i, after, slot⟩ := fair.kerne.2 kern physical t
  obtain ⟨s, load, rel⟩ := h.zustand i
  have shared := rel.1
  change { s with lokal := (η.zeit.zustand i).lokal } = η.zeit.zustand i at shared
  have dispatched : ((η.zeit.zustand i).kerne kern).laeuft = some c := by
    rw [← shared]
    exact (dispatch i after s load).1
  have running : (η.zeit.zustand i).status c = .laeuft := by
    rw [← shared]
    exact (dispatch i after s load).2
  refine ⟨i, after, ?_⟩
  rcases fortschritt_im_lauf run fertig regeln komponierbar i c running ⟨kern, dispatched⟩ with
    crash | done | blocked | enabled | withheld
  · exact Or.inl crash
  · exact Or.inr (Or.inl done)
  · exact Or.inr (Or.inr (Or.inl blocked))
  · exact Or.inr (Or.inr (Or.inr enabled))
  · exact (withheld.2 kern dispatched (h.hardware.symm ▸ slot)).elim

end Gabbro.Core.Maschine.I
