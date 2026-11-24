module

public import Core.Aussen.Geraet
public import Core.Aussen.Provenienz
public import Core.Maschine.Griff
public import Core.Maschine.Kontext

@[expose] public section

namespace Gabbro.Core.Sicherheit

open Maschine Katalog

inductive Speicherrecht where
  | lesen
  | schreiben
  | freigeben

/-- An executed address operand consists of a capability and an offset into its allocation. -/
structure Adresse where
  griff : Griff
  offset : Nat

/-- A commit observed in the implementation independently of its legality. Historical
    provenance can explain the chosen operation, but cannot authorise it. -/
structure AussenCommit where
  kontext : Kontext
  frage : Frage
  herkunft : Aussen.Provenienz

inductive Wirkung where
  | freigabe (c : Kontext) (g : Griff)
  | aussen (e : AussenCommit)

/-- Implementation observations supplied by the forms. Locations are indexed by a capability's
    object and an offset, access operands by the concrete event index of the current graph epoch.
    The effects ledger keeps the emitted releases and unmediated commits in execution order. -/
structure Buchung (Ort : Type) where
  umfang : Nat → List Ort
  haelt : Kontext → Griff → Speicherrecht → Prop
  adresse : Nat → Option Adresse
  schreibt : Kontext → Nat → Prop
  aussengriff : Kontext → Handle → Recht → Prop
  geraet : Objekt → Option (Kontext × Aussen.Vollmacht)
  wirkungen : List Wirkung

def Buchung.leer : Buchung Ort where
  umfang := fun _object => []
  haelt := fun _actor _handle _right => False
  adresse := fun _event => none
  schreibt := fun _actor _invariant => False
  aussengriff := fun _actor _handle _right => False
  geraet := fun _device => none
  wirkungen := []

end Gabbro.Core.Sicherheit
