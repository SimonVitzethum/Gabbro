module

public import Core.Verfeinerung.Folgen

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
structure SimPflichten (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F)
    (lokal : LokalerBezug Lok) (laenge : F → Nat) : Prop where
  abgleich : AbgleichPflichten E lokal laenge
  autoritaet : ∀ h ρ, Maschine.Laeufe E h ρ → ∀ t, BerechtigungAmTakt ρ t
  fortsetzung : ∀ s i, Zustandsbezug lokal s i → FortsetzungsBezug E s i

/-- Whole-run state and step simulation at the M4 interface. The same actual
    choices and ordered effects are replayed. Private work is bounded for
    each context and checked for authority on the concrete side. -/
def Sim (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F)
    (ρ : Maschine.Lauf E) (η : Lauf E) : Prop :=
  ∃ lokal laenge, Laufabgleich ρ η lokal ∧ StotterSchranke laenge η ∧
    ZustandAm E η ⟨0, Or.inl rfl⟩ = start E ρ.start ∧
    (∀ a b : Maschine.Schnitt E ρ, a.val ≤ b.val →
      (Zeitlauf.schnittBild ρ.zeit η.zeit a).val ≤ (Zeitlauf.schnittBild ρ.zeit η.zeit b).val) ∧
    Function.Surjective (Zeitlauf.schnittBild ρ.zeit η.zeit) ∧
    (∀ t, BerechtigungAmTakt ρ t) ∧
    (∀ t s, ρ.zeit.zustand t = some s → FortsetzungsBezug E s (η.zeit.zustand t)) ∧
    (∀ t s, ρ.zeit.zustand t = some s → SpeicherWahlGleich s.graph (η.zeit.zustand t).graph) ∧
    (ρ.zeit.Endlich ↔ η.zeit.Endlich)

variable {lokal : LokalerBezug Lok} {laenge : F → Nat}
variable {h : Umgebung} {ρ : Maschine.Lauf E} {η : Lauf E}

theorem Laufabgleich.sim (matched : Laufabgleich ρ η lokal) (valid : Laeufe E η)
    (bound : StotterSchranke laenge η) (authority : ∀ t, BerechtigungAmTakt ρ t)
    (continuation : ∀ s i, Zustandsbezug lokal s i → FortsetzungsBezug E s i) :
    Sim E ρ η := by
  refine ⟨lokal, laenge, matched, bound, matched.anfang valid, ?_, matched.schnitt_deckt, authority,
    ?_, ?_, matched.endlich valid⟩
  · intro a b ab
    exact η.zeit.letzterSchnitt_monoton ab
  · intro t s loaded
    obtain ⟨z, state, rel⟩ := matched.zustand t
    exact (Option.some.inj (state.symm.trans loaded)) ▸ continuation z _ rel
  · intro t s loaded
    obtain ⟨z, state, order⟩ := matched.speicherwahl t
    exact (Option.some.inj (state.symm.trans loaded)) ▸ order

theorem sim_im_lauf (pflicht : SimPflichten E lokal laenge) (run : Maschine.Laeufe E h ρ) :
    ∃ η : Lauf E, Laeufe E η ∧ Sim E ρ η := by
  obtain ⟨η, valid, matched⟩ := laufabgleich pflicht.abgleich run
  exact ⟨η, valid, matched.sim valid (pflicht.abgleich.schranke h ρ η run matched)
    (pflicht.autoritaet h ρ run) pflicht.fortsetzung⟩

end Gabbro.Core.Maschine.I
