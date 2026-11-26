/-
  File:      core/Core/Annahme/DomaeneBeweise/Bruecke.lean
  Subject:   OPEN 1 of MK-17: the rule-to-run bridge. The checker-side isolation duty of every
             head form (`DomaenenLokal` in `Core/Annahme/Lokal.lean`, the `RegelLokal` pattern)
             implies run isolation by inversion over `ImplSchritt`, and hence the isolation
             conclusion under the added checker row.

             The per-form duty `RegelIsolation` lives with the checker row in `Lokal.lean`. It is not
             a consequence of the other acceptance conjuncts: without the row the core statement
             is false (the refutation with the hosted unit and a channel-free plan, removed with
             the row in place).
-/
module

public import Core.Annahme.Domaene

@[expose] public section

namespace Gabbro.Core.Annahme

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type}

/-- **The rule-to-run bridge** (MK-17d): if the checker decides the isolation duty of
    every head form under the unit's own table, every recorded context cut of an admitted
    run respects that table. The cut is inverted
    once: `Takt.schritt` gives a `Lauffolge`, whose single constructor contains the machine
    `ImplSchritt`; its context constructor contains the rule of the form at the head, and the
    row supplies the duty for exactly that head form. -/
theorem regelIsolation_laufisolation [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (reihe : DomaenenLokal E) : LaufIsolation E (tabellePlan E.domaenen) := by
  intro h ρ lauf t w spur hspur c wahl hwahl
  have recorded := ρ.zeit.takt t
  rw [hspur] at recorded
  generalize vorEq : ρ.zeit.zustand t = vor at recorded
  generalize nachEq : ρ.zeit.zustand (t + 1) = nach at recorded
  cases recorded with
  | wartet label _ _ => cases label
  | schritt label step =>
    cases label
    cases step with
    | schritt impl =>
      subst hwahl
      cases impl with
      | kontext _ _ regel aus =>
        obtain ⟨i, hkopf, hp⟩ := regel
        exact reihe.2 _ _ _ hkopf t c _ _ _ wahl _ spur hp aus

/-- The isolation conclusion holds once the checker accepts the unit: acceptance carries
    the row over the unit's own table, and the bridge turns it into run isolation. -/
theorem isolation_aus_regel [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (hakk : Akzeptiert E) : LaufIsolation E (tabellePlan E.domaenen) :=
  regelIsolation_laufisolation E (akzeptiert_domaenen hakk)

/-- **The core statement over elaborated units**: acceptance carries the checker row over
    the elaborated unit's own table, and the bridge turns the row into run isolation. -/
theorem isolation_elaboriert (P : Katalog.Plattform) : IsolationAussage P := by
  intro t hakk
  exact isolation_aus_regel _ hakk

end Gabbro.Core.Annahme
