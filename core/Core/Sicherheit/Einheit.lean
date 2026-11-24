module

public import Core.Maschine.Start

@[expose] public section

namespace Gabbro.Core.Sicherheit

open Maschine Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type}

/-- One declaration in the unit, identified by its index in the declaration table.
    The same writer scope applies to type, module, loop and lock invariants. -/
structure Invariante (L S : Type) where
  sperre : Option L
  gilt : S → Prop

/-- The declaration table belongs to the unit whose rules and loader produce the run.
    M6 elaboration supplies this table as part of unit construction. -/
structure Einheit (L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type) where
  maschine : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form
  invarianten : List (Invariante L (Zustand L Ort Wert Raum Lok Grund))

variable [DecidableEq L]
variable (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)

abbrev Lauf := Maschine.Lauf E.maschine

/-- A recorded transition with both its concrete states, projecting the recorded choice away. -/
def Uebergang (ρ : Lauf E) (t : Nat) (vor : Zustand L Ort Wert Raum Lok Grund)
    (spur : SchrittSpur Ort Wert) (nach : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  ρ.zeit.zustand t = some vor ∧ (∃ w, ρ.zeit.spur t = some (w, spur)) ∧
    ρ.zeit.zustand (t + 1) = some nach

/-- A crash retires the old volatile epoch and is not a program release. -/
def Absturz (spur : SchrittSpur Ort Wert) : Prop :=
  Katalog.Ereignis.persistenz .crash ∈ spur.aussen

/-- Journal suffix of one transition. The crash ends the volatile journal after its
    earlier entries have already been checked at their own transitions. -/
def NeueWirkungen (vor nach : Zustand L Ort Wert Raum Lok Grund)
    (spur : SchrittSpur Ort Wert) (neu : List Wirkung) : Prop :=
  (Absturz spur ∧ nach.buchung.wirkungen = [] ∧ neu = []) ∨
    (¬ Absturz spur ∧ nach.buchung.wirkungen = vor.buchung.wirkungen ++ neu)

end Gabbro.Core.Sicherheit
