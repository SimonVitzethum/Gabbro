module

public import Core.Verfeinerung.Abnahme.Effekte
public import Core.Verfeinerung.Formpflichten

@[expose] public section

namespace Gabbro.Core.Maschine.I

/-- At most one operation commits per tick. A one-step operation may also
    invoke and return at that tick. An operation key names a single
    invocation, including context and invocation instance. -/
structure LockFreeTakt (Id Arg Ergebnis : Type) where
  aufruf : Option (Id × Arg)
  punkt : Option (Id × Arg × Ergebnis)
  antwort : Option (Id × Ergebnis)

variable {Id Arg Ergebnis S : Type}

/-- History bookkeeping at the concrete cuts. A pending invocation may have
    committed or may be omitted from the sequential history. A completed
    invocation must have committed with its actual argument and result. -/
structure LockFreeTakte (spur : Nat → Option (LockFreeTakt Id Arg Ergebnis)) : Prop where
  aufrufEinmal : ∀ id x y t u, (spur t).bind LockFreeTakt.aufruf = some (id, x) →
    (spur u).bind LockFreeTakt.aufruf = some (id, y) → t = u
  punktEinmal : ∀ id x y r s t u, (spur t).bind LockFreeTakt.punkt = some (id, x, r) →
    (spur u).bind LockFreeTakt.punkt = some (id, y, s) → t = u
  antwortEinmal : ∀ id r s t u, (spur t).bind LockFreeTakt.antwort = some (id, r) →
    (spur u).bind LockFreeTakt.antwort = some (id, s) → t = u
  aufgerufen : ∀ id x r t, (spur t).bind LockFreeTakt.punkt = some (id, x, r) →
    ∃ u, u ≤ t ∧ (spur u).bind LockFreeTakt.aufruf = some (id, x)
  abgeschlossen : ∀ id r t, (spur t).bind LockFreeTakt.antwort = some (id, r) →
    ∃ x u, u ≤ t ∧ (spur u).bind LockFreeTakt.punkt = some (id, x, r)

/-- One sequential execution of the declared abstract object. The fixed
    tick-indexed execution also serves every finite prefix. -/
def LockFreeSequenziell (spur : Nat → Option (LockFreeTakt Id Arg Ergebnis))
    (start : S) (spezifikation : S → Arg → Ergebnis → S → Prop) : Prop :=
  ∃ zustand : Nat → S, zustand 0 = start ∧
    ∀ t, match (spur t).bind LockFreeTakt.punkt with
      | none => zustand (t + 1) = zustand t
      | some (_, x, r) => spezifikation (zustand t) x r (zustand (t + 1))

structure LockFreeLinearisiert (spur : Nat → Option (LockFreeTakt Id Arg Ergebnis))
    (start : S) (spezifikation : S → Arg → Ergebnis → S → Prop) : Prop where
  takte : LockFreeTakte spur
  sequenziell : LockFreeSequenziell spur start spezifikation
  echtzeit : ∀ id jd x y r s a b p q,
    (spur a).bind LockFreeTakt.antwort = some (id, r) →
    (spur b).bind LockFreeTakt.aufruf = some (jd, y) → a < b →
    (spur p).bind LockFreeTakt.punkt = some (id, x, r) →
    (spur q).bind LockFreeTakt.punkt = some (jd, y, s) → p < q

theorem LockFreeTakte.linearisiert {spur : Nat → Option (LockFreeTakt Id Arg Ergebnis)}
    {start : S} {spezifikation : S → Arg → Ergebnis → S → Prop}
    (takte : LockFreeTakte spur) (sequenziell : LockFreeSequenziell spur start spezifikation) :
    LockFreeLinearisiert spur start spezifikation := by
  refine ⟨takte, sequenziell, ?_⟩
  intro id jd x y r s a b p q antwort aufruf vorher punkt next
  obtain ⟨z, u, bis, commit⟩ := takte.abgeschlossen id r a antwort
  obtain ⟨v, ab, invoke⟩ := takte.aufgerufen jd y s q next
  have first := takte.punktEinmal id x z r r p u punkt commit
  have second := takte.aufrufEinmal jd y y b v aufruf invoke
  exact (first ▸ bis).trans_lt (vorher.trans_le (second ▸ ab))

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

/-- A lock-free form family proves the step obligations and extracts operation
    instances and abstract updates from the actual ideal run. The operation
    decoder and the abstract spec are supplied by the form's declaration. -/
def LockFreeSimAussage (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F)
    (operation : F → Prop) (sicht : EffektSicht Ort Wert Wahl (LockFreeTakt Id Arg Ergebnis))
    (start : S) (spezifikation : S → Arg → Ergebnis → S → Prop) : Prop :=
  (∀ f, operation f → RegelSimulation E f) ∧
    ∀ (η : Lauf E), Laeufe E η →
      LockFreeTakte (fun t => sicht.lesen (η.zeit.spur t)) ∧
      LockFreeSequenziell (fun t => sicht.lesen (η.zeit.spur t)) start spezifikation

theorem LockFreeSimAussage.konkret {operation : F → Prop}
    {sicht : EffektSicht Ort Wert Wahl (LockFreeTakt Id Arg Ergebnis)}
    {start : S} {spezifikation : S → Arg → Ergebnis → S → Prop}
    (pflicht : LockFreeSimAussage E operation sicht start spezifikation)
    {ρ : Maschine.Lauf E} {η : Lauf E} (valid : Laeufe E η) (matched : Laufabgleich ρ η) :
    LockFreeLinearisiert (fun t => sicht.lesen (ρ.zeit.spur t)) start spezifikation := by
  have same : (fun t => sicht.lesen (ρ.zeit.spur t)) = (fun t => sicht.lesen (η.zeit.spur t)) :=
    funext (matched.effekte sicht)
  rw [same]
  obtain ⟨takte, sequenziell⟩ := pflicht.2 η valid
  exact takte.linearisiert sequenziell

end Gabbro.Core.Maschine.I
