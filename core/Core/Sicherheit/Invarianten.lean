module

public import Core.Sicherheit.Einheit

@[expose] public section

namespace Gabbro.Core.Sicherheit

open Maschine Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]

/-- An invariant holds at a cut outside its declared writers. -/
def InvariantenAmSchnitt (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (s : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  (∀ l, (s.sperren l).besitzer = none → E.maschine.einrichtung.invariant s l) ∧
  ∀ i d, E.invarianten[i]? = some d → (∀ c, s.status c = .laeuft → ¬ s.buchung.schreibt c i) → d.gilt s

/-- A hand-off is both an acquisition and a release. Waiting and ticketing without
    a change of owner are neither. -/
def InvariantenBeimWechsel (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (vor nach : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  ∀ l, (vor.sperren l).Wechsel (nach.sperren l) →
    E.maschine.einrichtung.invariant nach l ∧
      ∀ d ∈ E.invarianten, d.sperre = some l → d.gilt nach

/-- A crash retires the previous locks. -/
def InvariantenErhalten (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (_H : Umgebung) (ρ : Lauf E) : Prop :=
  (∀ (t : Maschine.Schnitt E.maschine ρ) s, ρ.zeit.zustand t.val = some s → InvariantenAmSchnitt E s) ∧
  ∀ t vor spur nach, Uebergang E ρ t vor spur nach → ¬ Absturz spur → InvariantenBeimWechsel E vor nach

end Gabbro.Core.Sicherheit
