module

public import Core.Verfeinerung.Speicherordnung

@[expose] public section

namespace Gabbro.Core.Maschine.I

open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

/-- Relate logical completion and every typed blocking reason of the same
    context, in addition to the protocol status and outcome. -/
def FortsetzungsBezug (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F)
    (s i : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  ∀ c, s.status c = i.status c ∧ (E.system.fertig s c ↔ E.system.fertig i c) ∧
    (∀ b, E.system.blockiert s c b ↔ E.system.blockiert i c b)

/-- The local checks required for the whole-run simulation, including concrete
    authority on all admitted prefixes, whether or not their steps are visible. -/
structure SimPflichten (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F) : Prop where
  abgleich : AbgleichPflichten E
  autoritaet : ∀ h ρ, Maschine.Laeufe E h ρ → ∀ t, BerechtigungAmTakt ρ t
  fortsetzung : ∀ s i, Zustandsbezug E s i → FortsetzungsBezug E s i

/-- Whole-run state and step simulation at the M4 interface, using the
    unit's local state relation and checked stutter lengths. The same choices
    and ordered effects are replayed, and concrete authority is checked on
    private steps too. The shared SC order extension is chosen once for the
    run, with a separate order for each crash epoch. -/
def Sim (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F)
    (ρ : Maschine.Lauf E) (η : Lauf E) : Prop :=
  ∃ ordnung, Laufabgleich ρ η ∧ StotterSchranke η ∧
    ZustandAm E η ⟨0, Or.inl rfl⟩ = start E ρ.start ∧
    (∀ a b : Maschine.Schnitt E ρ, a.val ≤ b.val →
      (Zeitlauf.schnittBild ρ.zeit η.zeit a).val ≤ (Zeitlauf.schnittBild ρ.zeit η.zeit b).val) ∧
    Function.Surjective (Zeitlauf.schnittBild ρ.zeit η.zeit) ∧
    (∀ t, BerechtigungAmTakt ρ t) ∧
    (∀ t s, ρ.zeit.zustand t = some s → FortsetzungsBezug E s (η.zeit.zustand t)) ∧
    (∀ t s, ρ.zeit.zustand t = some s → SpeicherWahlGleich s.graph (η.zeit.zustand t).graph) ∧
    SCOrdnung ordnung ∧
    (∀ t s, ρ.zeit.zustand t = some s →
      SCOrdnung.Erfasst ordnung s ∧ SCOrdnung.Erfasst ordnung (η.zeit.zustand t)) ∧
    (ρ.zeit.Endlich ↔ η.zeit.Endlich)

variable {h : Umgebung} {ρ : Maschine.Lauf E} {η : Lauf E}

/-- An interval that exceeds the unit's checked length refutes simulation. -/
theorem nicht_sim_bei_stotterueberlauf {c : Kontext} {f : F} {a n : Nat}
    (intervall : Stotterintervall η c f a n)
    (ueberlauf : E.stotterLaenge f < zaehle (fun t => decide (η.belegt t = some c)) a n) :
    ¬ Sim E ρ η := by
  rintro ⟨_, _, bound, _⟩
  exact (Nat.not_lt_of_ge (bound c f a n intervall)) ueberlauf

theorem Laufabgleich.sim (matched : Laufabgleich ρ η) (valid : Laeufe E η)
    (bound : StotterSchranke η) (authority : ∀ t, BerechtigungAmTakt ρ t)
    (continuation : ∀ s i, Zustandsbezug E s i → FortsetzungsBezug E s i) :
    Sim E ρ η := by
  obtain ⟨ordnung, exactOrder, idealOrder⟩ := sc_ordnung_im_lauf valid
  refine ⟨ordnung, matched, bound, matched.anfang valid, ?_, matched.schnitt_deckt, authority,
    ?_, ?_, exactOrder, ?_, matched.endlich valid⟩
  · intro a b ab
    exact η.zeit.letzterSchnitt_monoton ab
  · intro t s loaded
    obtain ⟨z, state, rel⟩ := matched.zustand t
    exact (Option.some.inj (state.symm.trans loaded)) ▸ continuation z _ rel
  · intro t s loaded
    obtain ⟨z, state, order⟩ := matched.speicherwahl t
    exact (Option.some.inj (state.symm.trans loaded)) ▸ order
  · intro t s loaded
    obtain ⟨z, atCut, related⟩ := matched.zustand t
    have eq := Option.some.inj (atCut.symm.trans loaded)
    subst s
    refine ⟨?_, idealOrder t⟩
    have shared := related.1
    change { z with lokal := (η.zeit.zustand t).lokal } = η.zeit.zustand t at shared
    have order := idealOrder t
    rw [← shared] at order
    exact order

theorem sim_im_lauf (pflicht : SimPflichten E) (run : Maschine.Laeufe E h ρ) :
    ∃ η : Lauf E, Laeufe E η ∧ Sim E ρ η := by
  obtain ⟨η, valid, matched, _⟩ := laufabgleich pflicht.abgleich run
  exact ⟨η, valid, matched.sim valid (pflicht.abgleich.schranke h ρ η run matched)
    (pflicht.autoritaet h ρ run) pflicht.fortsetzung⟩

end Gabbro.Core.Maschine.I
