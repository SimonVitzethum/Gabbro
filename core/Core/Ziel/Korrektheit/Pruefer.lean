/-
  File:      core/Core/Ziel/Korrektheit/Pruefer.lean
  Subject:   CHECKER CORRECTNESS (PERFECT-MODEL §3.2 and §7), stated as pinned propositions.

  `Akzeptiert E := Lokal E ∧ KlauselnWahr E ∧ WaechterHalten E` is the perfect checker; as a whole it is
  undecidable (`Beobachtung/Unentscheidbar`, `RiceAussage`). The deployed checker decides a fragment of it and is
  tied to it by two statements: soundness (`pruefe = true → Akzeptiert`) and completeness on a named decidable
  fragment (`Fragment → Akzeptiert → pruefe = true`). Soundness alone holds for a checker that refuses everything,
  so completeness and the non-triviality statements below are part of the same package. Meaning change (MK-17):
  the isolation row of `Lokal` constrains the recorded implementation steps, so acceptance reaches them.

  The checker is a TOTAL BOOLEAN function over source units (`Pruefer`), never a `Prop` with a `Decidable`
  instance: `∃ f : _ → Bool, ∀ p, f p = true ↔ Akzeptiert p` is provable classically and says nothing about
  computability. Computability is carried by the DEFINITION of the concrete checker: its Lean body is an ordinary
  `Bool` function, and the guards of `Core/Waechter/` will refuse a `Classical.choice` in its axiom closure when the
  concrete checker enters (see the report). Each of the three conjuncts of `Akzeptiert` has its own component, so
  the soundness and completeness of the three parts are independent tasks.

  Nothing here is proved except the two compositions (`pruefer_korrekt_aus_teilen`,
  `pruefer_vollstaendig_aus_teilen`): the statements of the parts compose to the statements of the whole.
-/
module

public import Core.Ast.Semantik.Elaborierung
public import Core.Annahme.Annahme
public import Core.Beobachtung.Unentscheidbar.Rice

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core

/-- The unit a source tree denotes on a platform: the elaborated unit (`elab_korrekt`). Every statement of
`Core/Ziel/Korrektheit/` about "a program" is a statement about `einheitVon P t` for a source unit `t`. -/
def einheitVon (P : Katalog.Plattform) (t : Ast.Unit) : Ast.Semantik.Einheit :=
  Ast.Semantik.elaborieren P (category := Ast.Category.unit) t

/-- A computable checker: one total Boolean decision per conjunct of `Akzeptiert`, and one total Boolean
membership test per conjunct for the decidable fragment on which that decision is complete. -/
structure Pruefer where
  pruefeLokal : Katalog.Plattform → Ast.Unit → Bool
  pruefeKlauseln : Katalog.Plattform → Ast.Unit → Bool
  pruefeWaechter : Katalog.Plattform → Ast.Unit → Bool
  fragmentLokal : Katalog.Plattform → Ast.Unit → Bool
  fragmentKlauseln : Katalog.Plattform → Ast.Unit → Bool
  fragmentWaechter : Katalog.Plattform → Ast.Unit → Bool

/-- The checker's verdict on a unit: the three components agree. -/
def Pruefer.pruefe (C : Pruefer) (P : Katalog.Plattform) (t : Ast.Unit) : Bool :=
  C.pruefeLokal P t && C.pruefeKlauseln P t && C.pruefeWaechter P t

/-- The decidable fragment of the checker: every component's fragment holds. -/
def Pruefer.fragment (C : Pruefer) (P : Katalog.Plattform) (t : Ast.Unit) : Bool :=
  C.fragmentLokal P t && C.fragmentKlauseln P t && C.fragmentWaechter P t

/-- SOUNDNESS of the local component: acceptance by the checker gives `Lokal` (types, ownership, lock ranks,
units, provenance of outside answers, guards or `else` paths, waits, stack and length bounds, row selection,
labelled flow). Feeds: `Annahme.Lokal` and its conjuncts (`RegelLokal`, `AussenLokal`, `FlussLokal`,
`SchrankenLokal`), per-instruction `Befehl.lokal`. Proof sketch: a syntactic pass over the tree whose every case
is the generic per-instruction lemma. Open: the pass itself (Designer for the pass, Prover for the lemma). -/
def PrueferLokalKorrektAussage (C : Pruefer) : Prop :=
  ∀ P t, C.pruefeLokal P t = true → Annahme.Lokal (einheitVon P t)

/-- COMPLETENESS of the local component on its fragment: every unit of the fragment that satisfies `Lokal` is
accepted by the component. The fragment is the set of units on which the local rules are structural. -/
def PrueferLokalVollstaendigAussage (C : Pruefer) : Prop :=
  ∀ P t, C.fragmentLokal P t = true → Annahme.Lokal (einheitVon P t) → C.pruefeLokal P t = true

/-- SOUNDNESS of the clause component: acceptance by the checker gives `KlauselnWahr` — every written clause
holds over every `I` run — for clauses in the decidable fragment (finite-state or bounded forms). Feeds:
`Annahme.KlauselnWahr`, `kanonischeKlauseln`, `I.Laeufe`. Proof sketch: the checker decides the clause over a
finite abstraction and the abstraction is sound (`Ideal` rules are deterministic). Open: the decision procedure
and the abstraction lemma (Designer: fragment; Prover: lemma). -/
def PrueferKlauselnKorrektAussage (C : Pruefer) : Prop :=
  ∀ P t, C.pruefeKlauseln P t = true → Annahme.KlauselnWahr (einheitVon P t)

/-- COMPLETENESS of the clause component on its fragment. -/
def PrueferKlauselnVollstaendigAussage (C : Pruefer) : Prop :=
  ∀ P t, C.fragmentKlauseln P t = true → Annahme.KlauselnWahr (einheitVon P t) →
    C.pruefeKlauseln P t = true

/-- SOUNDNESS of the guard component: acceptance by the checker gives `WaechterHalten` — every guard of a
partial operation holds in every reachable `I` state, and no reachable cut has a closed waiting set. Feeds:
`Annahme.WaechterHalten`, `waechterBedarf`, `SperrHalterHalten`, `deadlockfrei_aus_waechter`. -/
def PrueferWaechterKorrektAussage (C : Pruefer) : Prop :=
  ∀ P t, C.pruefeWaechter P t = true → Annahme.WaechterHalten (einheitVon P t)

/-- COMPLETENESS of the guard component on its fragment. -/
def PrueferWaechterVollstaendigAussage (C : Pruefer) : Prop :=
  ∀ P t, C.fragmentWaechter P t = true → Annahme.WaechterHalten (einheitVon P t) →
    C.pruefeWaechter P t = true

/-- `pruefer_korrekt` of PERFECT-MODEL §3.2: the checker accepts only accepted units. -/
def PrueferKorrektAussage (C : Pruefer) : Prop :=
  ∀ P t, C.pruefe P t = true → Annahme.Akzeptiert (einheitVon P t)

/-- `pruefer_vollstaendig` of PERFECT-MODEL §3.2: on its named decidable fragment the checker accepts every
accepted unit. -/
def PrueferVollstaendigAussage (C : Pruefer) : Prop :=
  ∀ P t, C.fragment P t = true → Annahme.Akzeptiert (einheitVon P t) → C.pruefe P t = true

/-- Soundness of the three components gives soundness of the checker. -/
theorem pruefer_korrekt_aus_teilen (C : Pruefer) (lokal : PrueferLokalKorrektAussage C)
    (klauseln : PrueferKlauselnKorrektAussage C) (waechter : PrueferWaechterKorrektAussage C) :
    PrueferKorrektAussage C := by
  intro P t h
  simp only [Pruefer.pruefe, Bool.and_eq_true] at h
  exact ⟨lokal P t h.1.1, klauseln P t h.1.2, waechter P t h.2⟩

/-- Completeness of the three components gives completeness of the checker on the joint fragment. -/
theorem pruefer_vollstaendig_aus_teilen (C : Pruefer) (lokal : PrueferLokalVollstaendigAussage C)
    (klauseln : PrueferKlauselnVollstaendigAussage C) (waechter : PrueferWaechterVollstaendigAussage C) :
    PrueferVollstaendigAussage C := by
  intro P t hf hA
  obtain ⟨hl, hk, hw⟩ := hA
  simp only [Pruefer.fragment, Bool.and_eq_true] at hf
  simp only [Pruefer.pruefe, Bool.and_eq_true]
  exact ⟨⟨lokal P t hf.1.1 hl, klauseln P t hf.1.2 hk⟩, waechter P t hf.2 hw⟩

/-- The checker is not trivial in either direction: it accepts some unit (it is not a refuse-everything
checker, for which soundness is empty) and it refuses some unit of its own fragment that is not accepted (it is
not an accept-everything checker; with soundness this is a unit the model itself refuses). Feeds:
`Annahme.akzeptiert_erfuellbar`, `geschlossen_nicht_akzeptiert`, `stale_nicht_akzeptiert`, the examples of
`Annahme/Hosted`. -/
def PrueferNichtTrivialAussage (C : Pruefer) : Prop :=
    (∃ P t, C.pruefe P t = true)
  ∧ (∃ P t, C.fragment P t = true ∧ C.pruefe P t = false ∧ ¬ Annahme.Akzeptiert (einheitVon P t))

/-- The checked remainder: outside its fragment no checker is complete. This is the undecidability of
`Akzeptiert` as a whole, stated through the existing Rice transfer: every extensional, non-trivial property of
simulated programs — functional correctness among them — is undecidable (`RiceAussage`), so everything outside
the fragment is the user's program logic (GabbroProve) and not a checker defect. Feeds:
`Beobachtung.Unentscheidbar.RiceAussage`, `substrat_rice`, `HalteUnentscheidbarAussage`. -/
def PrueferRestUnentscheidbarAussage : Prop :=
  Beobachtung.Unentscheidbar.RiceAussage

end Gabbro.Core.Ziel.Korrektheit
