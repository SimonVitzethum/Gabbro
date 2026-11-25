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

/-- Shared allocation extents and context holdings, together with the observations supplied by
    concrete forms. Locations are indexed by a capability's object and offset. Concrete access
    operands are indexed by event in the current graph epoch. The effects ledger keeps emitted
    releases and unmediated commits in execution order. -/
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

/-- **The holdings after a hand-over** (MK-07): `von` hands over the handles `gs` to `an`. Every right `von` held
    on one of them passes to `an` and `von` holds none of them any more; nobody else's holdings and no other
    handle's holders change. Authority moves, it is never copied. -/
def Buchung.uebergeben (b : Buchung Ort) (von an : Kontext) (gs : List Griff) :
    Kontext → Griff → Speicherrecht → Prop :=
  fun d g r =>
    if g ∈ gs then
      (if d = an then b.haelt von g r ∨ b.haelt an g r else if d = von then False else b.haelt d g r)
    else b.haelt d g r

/-- **The holdings after a join** (MK-07): the ended thread `kind` hands back everything it still held to the
    joiner `an`; it holds nothing afterwards, and nobody else's holdings change. -/
def Buchung.zurueckgegeben (b : Buchung Ort) (kind an : Kontext) : Kontext → Griff → Speicherrecht → Prop :=
  fun d g r => if d = an then b.haelt an g r ∨ b.haelt kind g r else if d = kind then False else b.haelt d g r

/-- **Exclusive authority has one holder**: no handle is held with the right to write or to release by two
    contexts. A hand-over and a take-back keep it (`uebergeben_eindeutig`, `zurueckgegeben_eindeutig`). -/
def Buchung.Eindeutig (b : Buchung Ort) : Prop :=
  ∀ d d' g r, (r = Speicherrecht.schreiben ∨ r = Speicherrecht.freigeben) →
    b.haelt d g r → b.haelt d' g r → d = d'

end Gabbro.Core.Sicherheit
