/-
  File:      core/Core/Annahme/Klauseln.lean
  Subject:   The written clauses of acceptance (PERFECT-MODEL §3.2, step M5).

  `KlauselnWahr E` says the user's written clauses — requires, ensures, invariants — hold on
  every `I` run. It is stated over `I.Laeufe` only: requires at the ideal start, the invariant
  at every cut, ensures at every finished cut. The clause table is supplied per program; the M6
  constructors and B11 fill it.
-/
module

public import Core.Maschine.Start

@[expose] public section

namespace Gabbro.Core.Annahme

open Gabbro.Core.Maschine

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type}

/-- **The written clauses of a unit**: requires on `I` starts, ensures on finished `I` cuts,
    invariants on every `I` cut. Predicates over `I` states, never over definedness of `I` or
    anything about the implementation. -/
class KlauselTabelle (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) : Type where
  voraus : Zustand L Ort Wert Raum Lok Grund → Prop
  sicher : Zustand L Ort Wert Raum Lok Grund → Prop
  invariant : Zustand L Ort Wert Raum Lok Grund → Prop

/-- **`KlauselnWahr E`: every written clause holds on every `I` run** — requires at the ideal
    start, the invariant at every cut, ensures at every finished cut. -/
def KlauselnWahr [DecidableEq L] (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    [K : KlauselTabelle E] : Prop :=
  ∀ ρ : I.Lauf E, I.Laeufe E ρ →
    K.voraus (I.start E ρ.start).2 ∧
    (∀ t : I.Schnitt E ρ, K.invariant (ρ.zeit.zustand t.val)) ∧
    (∀ t : I.Schnitt E ρ, (∀ c, E.system.fertig (ρ.zeit.zustand t.val) c) →
      K.sicher (ρ.zeit.zustand t.val))

end Gabbro.Core.Annahme
