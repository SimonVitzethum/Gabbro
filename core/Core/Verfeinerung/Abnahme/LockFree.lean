module

public import Core.Verfeinerung.Abnahme.Effekte
public import Core.Verfeinerung.Formpflichten
public import Core.Verfeinerung.Erfuellbar

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
  omega

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]

/-- A lock-free family declares its operation decoder and its abstract object as data of the
    unit wrapper. The decoder names invocations, commits and responses in the ideal run; the
    abstraction function, its start value and its specification fix the abstract history.
    Membership selects the rule duties the family owes. -/
structure LockFreeEinheit (L Ort Wert Raum Lok Grund Bedingung Wahl F : Type) [DecidableEq L] where
  einheit : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F
  Id : Type
  Arg : Type
  Ergebnis : Type
  S : Type
  mitglied : F → Prop
  sicht : EffektSicht Ort Wert Wahl (LockFreeTakt Id Arg Ergebnis)
  abs : Maschine.Zustand L Ort Wert Raum Lok Grund → S
  start : S
  spezifikation : S → Arg → Ergebnis → S → Prop

/-- Abstraction faithfulness at every ideal tick. A commit point must satisfy the declared
    specification between the abstraction before and after the tick; at every other tick,
    including private work and pauses, the abstraction is preserved. -/
def LockFreeAbsTreue (U : LockFreeEinheit L Ort Wert Raum Lok Grund Bedingung Wahl F)
    (η : Lauf U.einheit) : Prop :=
  U.abs (η.zeit.zustand 0) = U.start ∧
    ∀ t, match (U.sicht.lesen (η.zeit.spur t)).bind LockFreeTakt.punkt with
      | none => U.abs (η.zeit.zustand (t + 1)) = U.abs (η.zeit.zustand t)
      | some (_, x, r) => U.spezifikation (U.abs (η.zeit.zustand t)) x r
          (U.abs (η.zeit.zustand (t + 1)))

/-- The declared abstraction correspondence is a sequential history of the ideal run. At a
    silent tick the ideal state is unchanged (`Zeitlauf.wartet`), in line with the maximal-run
    condition of `Laeufe`; the abstraction is carried by `abs` in both cases. -/
theorem absTreue_gibt_sequenziell (U : LockFreeEinheit L Ort Wert Raum Lok Grund Bedingung Wahl F)
    (η : Lauf U.einheit) (treue : LockFreeAbsTreue U η) :
    LockFreeSequenziell (fun t => U.sicht.lesen (η.zeit.spur t)) U.start U.spezifikation := by
  refine ⟨fun t => U.abs (η.zeit.zustand t), treue.1, ?_⟩
  intro t
  cases eintrag : (U.sicht.lesen (η.zeit.spur t)).bind LockFreeTakt.punkt with
  | none =>
      have duty := treue.2 t
      simpa only using duty
  | some _ =>
      have duty := treue.2 t
      simpa only using duty

/-- A lock-free family discharges the simulation duties of its member rules and declares, on
    every ideal run of its unit, a well-formed operation history together with a faithful
    abstraction. Linearisability is derived in `konkret`, not declared here. -/
def LockFreeFamilienAussage (U : LockFreeEinheit L Ort Wert Raum Lok Grund Bedingung Wahl F) : Prop :=
  (∀ f, U.mitglied f → RegelSimulation U.einheit f) ∧
    ∀ (η : Lauf U.einheit), Laeufe U.einheit η →
      LockFreeTakte (fun t => U.sicht.lesen (η.zeit.spur t)) ∧ LockFreeAbsTreue U η

theorem LockFreeFamilienAussage.konkret
    (U : LockFreeEinheit L Ort Wert Raum Lok Grund Bedingung Wahl F)
    (pflicht : LockFreeFamilienAussage U)
    {ρ : Maschine.Lauf U.einheit} {η : Lauf U.einheit} (valid : Laeufe U.einheit η)
    (matched : Laufabgleich ρ η) :
    LockFreeLinearisiert (fun t => U.sicht.lesen (ρ.zeit.spur t)) U.start U.spezifikation := by
  have same : (fun t => U.sicht.lesen (ρ.zeit.spur t)) =
      (fun t => U.sicht.lesen (η.zeit.spur t)) :=
    funext (matched.effekte U.sicht)
  rw [same]
  obtain ⟨takte, treue⟩ := pflicht.2 η valid
  exact takte.linearisiert (absTreue_gibt_sequenziell U η treue)

/-- The family duty is satisfiable: with no member rules, a decoder that emits nothing and a
    constant abstraction, every unit admits the empty operation history and the trivial spec. -/
theorem LockFreeFamilienAussage.erfuellbar
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F) :
    ∃ U : LockFreeEinheit L Ort Wert Raum Lok Grund Bedingung Wahl F,
      LockFreeFamilienAussage U := by
  let U : LockFreeEinheit L Ort Wert Raum Lok Grund Bedingung Wahl F :=
    ⟨E, PUnit, PUnit, PUnit, PUnit, fun _ => False,
      ⟨fun _ => none, rfl, fun _ _ => rfl⟩, fun _ => PUnit.unit, PUnit.unit,
      fun _ _ _ _ => True⟩
  refine ⟨U, ?_⟩
  constructor
  · intro f nichtLeer
    cases nichtLeer
  · intro η lauf
    constructor
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro id x y t u ht hu
        change none = some (id, x) at ht
        cases ht
      · intro id x y r s t u ht hu
        change none = some (id, x, r) at ht
        cases ht
      · intro id r s t u ht hu
        change none = some (id, r) at ht
        cases ht
      · intro id x r t ht
        change none = some (id, x, r) at ht
        cases ht
      · intro id r t ht
        change none = some (id, r) at ht
        cases ht
    · dsimp only [LockFreeAbsTreue, U]
      constructor
      · rfl
      · intro t
        rfl

/-- The family duty is refutable: declaring an abstract start that differs from the abstraction
    of the unit's initial state breaks the faithfulness duty on every ideal run. The unit and run
    come from `fortschritt_erfuellbar`. -/
theorem LockFreeFamilienAussage.nichtTrivial :
    ∃ U : LockFreeEinheit Unit Unit Unit Unit Bool Unit Unit Unit Unit,
      ¬ LockFreeFamilienAussage U := by
  obtain ⟨E, _, _, _, η, _, _, valid, _⟩ := fortschritt_erfuellbar
  let U : LockFreeEinheit Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
    ⟨E, PUnit, PUnit, PUnit, Bool, fun _ => False,
      ⟨fun _ => none, rfl, fun _ _ => rfl⟩, fun _ => false, true, fun _ _ _ _ => True⟩
  refine ⟨U, ?_⟩
  intro aussage
  have validU : Laeufe U.einheit η := by simpa only [U] using valid
  obtain ⟨_, treue⟩ := aussage.2 η validU
  dsimp only [LockFreeAbsTreue, U] at treue
  obtain ⟨initial, _⟩ := treue
  cases initial

end Gabbro.Core.Maschine.I
