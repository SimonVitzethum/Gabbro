/-
  File:      core/Core/Annahme/DomaeneBeweise/Bruecke.lean
  Subject:   OPEN 1 of MK-17: the rule-to-run bridge. A checker-side isolation duty of every
             form (`RegelIsolation`, the `RegelLokal` pattern) implies run isolation by inversion
             over `ImplSchritt`, and hence the isolation conclusion under the added duty premise.

             `RegelIsolation` did not exist in the merged model. It is introduced here as the
             per-form duty at the machine boundary: a form's implementation step, once carried
             out through `FuehrtSchrittAus`, must yield a domain-respecting spur. It is not a
             consequence of `Akzeptiert`; the companion module `Gegenbeispiel` proves that the
             core statement without this premise is false.
-/
module

public import Core.Annahme.Domaene

@[expose] public section

namespace Gabbro.Core.Annahme

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type}

/-- **The checker-side isolation duty of one form** (the `RegelLokal` pattern, lifted to the
    recorded step as for `Beobachtung.RegelNIPflicht`): every implementation step of the form
    that the machine carries out through `FuehrtSchrittAus` produces a spur the acting context's
    domain respects. The duty is per form, generic over units, and carries no per-program data. -/
def RegelIsolation [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (plan : DomaenenPlan) (i : ι) : Prop :=
  ∀ (t : Nat) (c : Kontext) (s u s' : Zustand L Ort Wert Raum Lok Grund)
    (w : Wahl) (p : SchrittPlan L Ort Wert Bedingung) (spur : SchrittSpur Ort Wert),
    (E.system.regel i).impl c s w [p] u →
    FuehrtSchrittAus E.einrichtung t c s u p spur s' →
    SpurRespektiert E plan c spur

/-- **The rule-to-run bridge**: if the checker decides the isolation duty of every form, every
    recorded context cut of an admitted run respects the domains. The cut is inverted once:
    `Takt.schritt` gives a `Lauffolge`, whose single constructor contains the machine
    `ImplSchritt`; its context constructor contains the rule of the form at the head. -/
theorem regelIsolation_laufisolation [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (plan : DomaenenPlan)
    (regeln : ∀ i, RegelIsolation E plan i) : LaufIsolation E plan := by
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
        obtain ⟨i, _, hp⟩ := regel
        exact regeln i t c _ _ _ wahl _ spur hp aus

/-- The isolation conclusion holds once the per-form duty is added to the premise bundle; the
    other three premises are carried through unused, exactly as in `IsolationAussage`. -/
theorem isolation_aus_regel [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (plan : DomaenenPlan)
    (_ : plan.wohlgeformt) (_ : Akzeptiert E) (_ : DomaenenKohaerenz E plan)
    (regeln : ∀ i, RegelIsolation E plan i) : LaufIsolation E plan :=
  regelIsolation_laufisolation E plan regeln

end Gabbro.Core.Annahme
