module

public import Core.Verfeinerung.Simulation

@[expose] public section

namespace Gabbro.Core.Maschine

open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

/-- The catalogue part of the concrete prefix in execution order. -/
def Katalogspur (ρ : Lauf E) (k : Schnitt E ρ) : List Ereignis :=
  Zeitlauf.praefix (fun t => (ρ.zeit.spur t).elim [] (fun event => event.2.aussen)) k.val

/-- A context reports only a value or reason exit. Catalogue results come from
    the ordered outside trace, independently of context termination. -/
def ErgebnisseAmSchnitt (ρ : Lauf E) (k : Schnitt E ρ) :
    (Kontext → Option (Ergebnis Wert Grund)) × List (Ergebnis Wert Grund) :=
  let ende := fun c => (ρ.zeit.zustand k.val).elim none fun z =>
    match z.status c with
    | .ruht | .laeuft => none
    | .beendet e => some (Ergebnis.ende e)
  (ende, (Katalogspur ρ k).map Ergebnis.katalog)

/-- The guarantees carried by the M4 machine at a concrete cut. Every access
    in its prefix was authorised when it occurred. The RC11 graph and
    consumption counters are valid, and outcomes come from the typed machine
    status or catalogue events recorded in that prefix. -/
def ZielFX (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F)
    (h : Umgebung) (ρ : Lauf E) (k : Schnitt E ρ) : Prop :=
  Laeufe E h ρ ∧
  ∃ z, ρ.zeit.zustand k.val = some z ∧ z.SpeicherGut ∧ z.Verbrauch ∧
    (∀ t, t < k.val → BerechtigungAmTakt ρ t) ∧
    (∀ c result, (ErgebnisseAmSchnitt ρ k).1 c = some result ↔
      ∃ e, z.status c = .beendet e ∧ result = .ende e) ∧
    (∀ result, result ∈ (ErgebnisseAmSchnitt ρ k).2 ↔
      ∃ e, e ∈ Katalogspur ρ k ∧ result = .katalog e)

theorem I.SimPflichten.zielFX
    (pflicht : I.SimPflichten E) {h : Umgebung} {ρ : Maschine.Lauf E}
    (run : Maschine.Laeufe E h ρ) (k : Maschine.Schnitt E ρ) : ZielFX E h ρ k := by
  obtain ⟨z, loaded, memory, answers⟩ := pflicht.abgleich.sicherheit_am_schnitt run k
  refine ⟨run, z, loaded, memory, answers, fun t _ => pflicht.autoritaet h ρ run t, ?_, ?_⟩
  · intro c result
    unfold ErgebnisseAmSchnitt
    simp only [loaded, Option.elim]
    cases status : z.status c with
    | ruht | laeuft =>
      constructor
      · intro h
        cases h
      · rintro ⟨e, h, _⟩
        cases h
    | beendet e =>
      constructor
      · intro h
        exact ⟨e, rfl, (Option.some.inj h).symm⟩
      · rintro ⟨_, h, rfl⟩
        cases h
        rfl
  · intro result
    change result ∈ (Katalogspur ρ k).map Ergebnis.katalog ↔ _
    constructor
    · intro h
      obtain ⟨e, member, eq⟩ := List.mem_map.mp h
      exact ⟨e, member, eq.symm⟩
    · rintro ⟨e, member, eq⟩
      exact List.mem_map.mpr ⟨e, member, eq.symm⟩

end Gabbro.Core.Maschine
