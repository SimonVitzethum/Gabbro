module

public import Core.Verfeinerung.Maschine

@[expose] public section

namespace Gabbro.Core.Maschine.I

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

/-- An interpretation of actual trace labels which ignores silent context
    transitions. It can recognise protocol events or object linearisation
    points. Merely changing a private frame cannot emit such an event. -/
structure EffektSicht (Ort Wert Wahl Ereignis : Type) where
  lesen : Option (SchrittWahl Wahl × SchrittSpur Ort Wert) → Option Ereignis
  leer : lesen none = none
  privat : ∀ c w, lesen (some (.kontext c w, ⟨[], []⟩)) = lesen none

theorem SpurAbgleich.effekte {Ev : Type} (sicht : EffektSicht Ort Wert Wahl Ev)
    {konkret ideal : Option (SchrittWahl Wahl × SchrittSpur Ort Wert)}
    (matched : SpurAbgleich konkret ideal) : sicht.lesen konkret = sicht.lesen ideal := by
  cases matched with
  | pause => rfl
  | privat c w => exact sicht.privat c w
  | schritt event => rfl

theorem Laufabgleich.effekte {ρ : Maschine.Lauf E} {η : Lauf E}
    (matched : Laufabgleich ρ η) {Ev : Type} (sicht : EffektSicht Ort Wert Wahl Ev) (t : Nat) :
    sicht.lesen (ρ.zeit.spur t) = sicht.lesen (η.zeit.spur t) :=
  (matched.spur t).effekte sicht

end Gabbro.Core.Maschine.I
