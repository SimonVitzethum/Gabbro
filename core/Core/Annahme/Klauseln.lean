/-
  File:      core/Core/Annahme/Klauseln.lean
  Subject:   The written clauses of acceptance (PERFECT-MODEL §3.2, step M5).

  `KlauselnWahr E` says the user's written clauses — requires, ensures, invariants — hold on
  every `I` run. It is stated over `I.Laeufe` only: requires at the ideal start, the invariant
  at every cut, ensures at every finished cut. The clause table is DATA DETERMINED BY THE
  UNIT: `Akzeptiert` uses the canonical value `kanonischeKlauseln E`, never a supplied
  instance. Elaboration stores the clauses in source order and acceptance conjoins the
  predicates at their designated ideal cuts.
-/
module

public import Core.Maschine.Start

@[expose] public section

namespace Gabbro.Core.Annahme

open Gabbro.Core.Maschine

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type}

/-- **The written clauses of a unit**: requires on `I` starts, ensures on finished `I` cuts,
    invariants on every `I` cut. Predicates over `I` states, never over definedness of `I` or
    anything about the implementation. The M6 constructors supply per-program tables in this
    shape when the syntax enters. -/
class KlauselTabelle (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) : Type where
  voraus : Zustand L Ort Wert Raum Lok Grund → Prop
  sicher : Zustand L Ort Wert Raum Lok Grund → Prop
  invariant : Zustand L Ort Wert Raum Lok Grund → Prop

/-- The canonical clause table conjoins the predicates written by the source. -/
def kanonischeKlauseln (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) :
    KlauselTabelle E :=
  let t := E.quelltabellen.klauseln
  ⟨fun s => ∀ p ∈ t.voraus, p s, fun s => ∀ p ∈ t.sicher, p s,
    fun s => ∀ p ∈ t.invariant, p s⟩

/-- **`KlauselnWahr E`: every written clause holds on every `I` run** — requires at the ideal
    start, the invariant at every cut, ensures at every finished cut; over the canonical
    tables determined by the unit, with no instance arguments. -/
def KlauselnWahr [DecidableEq L] (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) :
    Prop :=
  ∀ ρ : I.Lauf E, I.Laeufe E ρ →
    (kanonischeKlauseln E).voraus (I.start E ρ.start).2 ∧
    (∀ t : I.Schnitt E ρ, (kanonischeKlauseln E).invariant (ρ.zeit.zustand t.val)) ∧
    (∀ t : I.Schnitt E ρ, (∀ c, E.system.fertig (ρ.zeit.zustand t.val) c) →
      (kanonischeKlauseln E).sicher (ρ.zeit.zustand t.val))

end Gabbro.Core.Annahme
