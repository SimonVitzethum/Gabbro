module

public import Core.Verfeinerung.Abnahme.Effekte
public import Core.Verfeinerung.Formpflichten

@[expose] public section

namespace Gabbro.Core.Maschine.I

open Gabbro.Core.Katalog

inductive FlushPhase where
  | senden (ziele : List Kern)
  | handler (kern : Kern)
  | bestaetigen (kern : Kern)
  | freigeben

/-- Each key identifies one revocation, including its generation and epoch.
    The prefix may end after any phase. A release needs evidence for every
    target, and a reset cannot turn pre-crash evidence into a valid release. -/
structure FlushProtokoll {Id : Type} (spur : Nat → Option (Id × FlushPhase))
    (absturz : Nat → Prop) : Prop where
  eindeutig : ∀ id phase t u, spur t = some (id, phase) → spur u = some (id, phase) → t = u
  eineSendung : ∀ id xs ys t u, spur t = some (id, .senden xs) →
    spur u = some (id, .senden ys) → t = u
  sendung : ∀ id k t, spur t = some (id, .handler k) →
    ∃ s ziele, s < t ∧ spur s = some (id, .senden ziele) ∧ k ∈ ziele ∧
      ∀ u, s ≤ u → u < t → ¬ absturz u
  bestaetigung : ∀ id k t, spur t = some (id, .bestaetigen k) →
    ∃ h, h < t ∧ spur h = some (id, .handler k) ∧
      ∀ u, h ≤ u → u < t → ¬ absturz u
  freigabe : ∀ id t, spur t = some (id, .freigeben) →
    ∃ s ziele, s < t ∧ spur s = some (id, .senden ziele) ∧
      (∀ u, s ≤ u → u < t → ¬ absturz u) ∧
      ∀ k, k ∈ ziele → ∃ h a, s < h ∧ h < a ∧ a < t ∧
        spur h = some (id, .handler k) ∧ spur a = some (id, .bestaetigen k)

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

abbrev FlushSicht (Ort Wert Wahl Id : Type) :=
  EffektSicht Ort Wert Wahl (Id × FlushPhase)

/-- A multi-phase flush family supplies one step obligation per staged
    machine rule and proves the protocol from every actual ideal run. The
    decoder must be tied to those rules by the form's semantics proof. -/
def FlushSimAussage (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F)
    (phase : F → Prop) {Id : Type} (sicht : FlushSicht Ort Wert Wahl Id) : Prop :=
  (∀ f, phase f → RegelSimulation E f) ∧
    ∀ (η : Lauf E), Laeufe E η →
      FlushProtokoll (fun t => sicht.lesen (η.zeit.spur t))
        (fun t => η.zeit.spur t = some (.absturz, absturzSpur))

private theorem absturzGleich
    {konkret ideal : Option (SchrittWahl Wahl × SchrittSpur Ort Wert)}
    (matched : SpurAbgleich konkret ideal) :
    (konkret = some (.absturz, absturzSpur)) ↔ (ideal = some (.absturz, absturzSpur)) := by
  cases matched with
  | pause => exact Iff.rfl
  | privat c w => exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | schritt event => exact Iff.rfl

theorem FlushSimAussage.konkret {phase : F → Prop} {Id : Type}
    {sicht : FlushSicht Ort Wert Wahl Id} (pflicht : FlushSimAussage E phase sicht)
    {ρ : Maschine.Lauf E} {η : Lauf E} (valid : Laeufe E η) (matched : Laufabgleich ρ η) :
    FlushProtokoll (fun t => sicht.lesen (ρ.zeit.spur t))
      (fun t => ρ.zeit.spur t = some (.absturz, absturzSpur)) := by
  have phases : (fun t => sicht.lesen (ρ.zeit.spur t)) =
      (fun t => sicht.lesen (η.zeit.spur t)) :=
    funext fun t => matched.effekte sicht t
  have crash : (fun t => ρ.zeit.spur t = some (.absturz, absturzSpur)) =
      (fun t => η.zeit.spur t = some (.absturz, absturzSpur)) := by
    exact funext fun t => propext (absturzGleich (matched.spur t))
  rw [phases, crash]
  exact pflicht.2 η valid

end Gabbro.Core.Maschine.I
