/-
  File:      core/Core/Ziel/Korrektheit/Beweise/BegleitPruefer.lean
  Subject:   COMPANION LEMMAS for the pinned statements of `Core/Ziel/Korrektheit/Pruefer.lean`
             (checker correctness): for every `…Aussage` an `X.erfuellbar` (a checker satisfying
             the statement, with the decision premises realised) and an `X.nichtTrivial`
             (a non-accepted object or a degenerate checker violates the statement). No pinned
             statement is changed. The soundness companions use `staleEinheit`; the completeness
             companions use `akzeptiert_erfuellbar`. The checker that decides each conjunct by
             a classical `if` makes the soundness and completeness statements true non-vacuously
             without a `decide` proof on a large proposition.
-/
module

public import Core.Ziel.Korrektheit.Pruefer
public import Core.Annahme.Annahme
public import Core.Beobachtung.Unentscheidbar.Modell

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Classical

/-- The checker whose three verdicts are the classical decisions of the three conjuncts of
    `Akzeptiert`, and whose fragment is total. Every soundness and completeness statement below
    holds for this checker with a real decision. -/
noncomputable def prueferEntscheidet : Pruefer where
  pruefeLokal := fun P t => if Annahme.Lokal (einheitVon P t) then true else false
  pruefeKlauseln := fun P t => if Annahme.KlauselnWahr (einheitVon P t) then true else false
  pruefeWaechter := fun P t => if Annahme.WaechterHalten (einheitVon P t) then true else false
  fragmentLokal := fun _ _ => true
  fragmentKlauseln := fun _ _ => true
  fragmentWaechter := fun _ _ => true

/-- The checker that accepts every unit and whose fragment is total. It is the degenerate case in
    which soundness is vacuous and completeness fails. -/
def prueferNimmtAlles : Pruefer where
  pruefeLokal := fun _ _ => true
  pruefeKlauseln := fun _ _ => true
  pruefeWaechter := fun _ _ => true
  fragmentLokal := fun _ _ => true
  fragmentKlauseln := fun _ _ => true
  fragmentWaechter := fun _ _ => true

/-- Acceptance is not universal: the stale-handle unit is refused. Feeds: `staleEinheit`,
    `stale_nicht_akzeptiert`. -/
theorem akzeptiertNichtTrivial :
    ∃ E : Maschine.Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit,
      ¬ Annahme.Akzeptiert E :=
  ⟨Annahme.staleEinheit, Annahme.stale_nicht_akzeptiert⟩

/-- The local component is refused for the same unit: its outside-validity conjunct fails. Feeds:
    `staleEinheit`, `stale_nicht_aussen_gueltig`. -/
theorem lokalNichtTrivial :
    ∃ E : Maschine.Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit, ¬ Annahme.Lokal E := by
  refine ⟨Annahme.staleEinheit, ?_⟩
  intro hLocal
  exact Annahme.stale_nicht_aussen_gueltig hLocal.2.2.1.2

/-! ### Soundness components -/

theorem PrueferLokalKorrektAussage.erfuellbar :
    ∃ C : Pruefer, PrueferLokalKorrektAussage C := by
  refine ⟨prueferEntscheidet, ?_⟩
  intro P t accepted
  change (if Annahme.Lokal (einheitVon P t) then true else false) = true at accepted
  split at accepted
  · assumption
  · cases accepted

theorem PrueferLokalKorrektAussage.nichtTrivial :
    ∃ E : Maschine.Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit, ¬ Annahme.Lokal E :=
  lokalNichtTrivial

theorem PrueferKlauselnKorrektAussage.erfuellbar :
    ∃ C : Pruefer, PrueferKlauselnKorrektAussage C := by
  refine ⟨prueferEntscheidet, ?_⟩
  intro P t accepted
  change (if Annahme.KlauselnWahr (einheitVon P t) then true else false) = true at accepted
  split at accepted
  · assumption
  · cases accepted

theorem PrueferKlauselnKorrektAussage.nichtTrivial :
    ∃ E : Maschine.Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit,
      ¬ Annahme.Akzeptiert E :=
  akzeptiertNichtTrivial

theorem PrueferWaechterKorrektAussage.erfuellbar :
    ∃ C : Pruefer, PrueferWaechterKorrektAussage C := by
  refine ⟨prueferEntscheidet, ?_⟩
  intro P t accepted
  change (if Annahme.WaechterHalten (einheitVon P t) then true else false) = true at accepted
  split at accepted
  · assumption
  · cases accepted

theorem PrueferWaechterKorrektAussage.nichtTrivial :
    ∃ E : Maschine.Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit,
      ¬ Annahme.Akzeptiert E :=
  akzeptiertNichtTrivial

theorem PrueferKorrektAussage.erfuellbar : ∃ C : Pruefer, PrueferKorrektAussage C := by
  refine ⟨prueferEntscheidet, ?_⟩
  apply pruefer_korrekt_aus_teilen
  · intro P t accepted
    change (if Annahme.Lokal (einheitVon P t) then true else false) = true at accepted
    split at accepted
    · assumption
    · cases accepted
  · intro P t accepted
    change (if Annahme.KlauselnWahr (einheitVon P t) then true else false) = true at accepted
    split at accepted
    · assumption
    · cases accepted
  · intro P t accepted
    change (if Annahme.WaechterHalten (einheitVon P t) then true else false) = true at accepted
    split at accepted
    · assumption
    · cases accepted

theorem PrueferKorrektAussage.nichtTrivial :
    ∃ E : Maschine.Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit,
      ¬ Annahme.Akzeptiert E :=
  akzeptiertNichtTrivial

/-! ### Completeness components -/

theorem PrueferLokalVollstaendigAussage.erfuellbar :
    ∃ C : Pruefer, PrueferLokalVollstaendigAussage C := by
  refine ⟨prueferEntscheidet, ?_⟩
  intro P t _ hLocal
  change (if Annahme.Lokal (einheitVon P t) then true else false) = true
  split
  · rfl
  · rename_i notLocal
    exact (notLocal hLocal).elim

theorem PrueferLokalVollstaendigAussage.nichtTrivial :
    ∃ E : Maschine.Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit,
      Annahme.Akzeptiert E :=
  Annahme.akzeptiert_erfuellbar

theorem PrueferKlauselnVollstaendigAussage.erfuellbar :
    ∃ C : Pruefer, PrueferKlauselnVollstaendigAussage C := by
  refine ⟨prueferEntscheidet, ?_⟩
  intro P t _ clauses
  change (if Annahme.KlauselnWahr (einheitVon P t) then true else false) = true
  split
  · rfl
  · rename_i notClauses
    exact (notClauses clauses).elim

theorem PrueferKlauselnVollstaendigAussage.nichtTrivial :
    ∃ E : Maschine.Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit,
      Annahme.Akzeptiert E :=
  Annahme.akzeptiert_erfuellbar

theorem PrueferWaechterVollstaendigAussage.erfuellbar :
    ∃ C : Pruefer, PrueferWaechterVollstaendigAussage C := by
  refine ⟨prueferEntscheidet, ?_⟩
  intro P t _ guards
  change (if Annahme.WaechterHalten (einheitVon P t) then true else false) = true
  split
  · rfl
  · rename_i notGuards
    exact (notGuards guards).elim

theorem PrueferWaechterVollstaendigAussage.nichtTrivial :
    ∃ E : Maschine.Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit,
      Annahme.Akzeptiert E :=
  Annahme.akzeptiert_erfuellbar

theorem PrueferVollstaendigAussage.erfuellbar : ∃ C : Pruefer, PrueferVollstaendigAussage C := by
  refine ⟨prueferEntscheidet, ?_⟩
  apply pruefer_vollstaendig_aus_teilen
  · intro P t _ hLocal
    change (if Annahme.Lokal (einheitVon P t) then true else false) = true
    split
    · rfl
    · rename_i notLocal
      exact (notLocal hLocal).elim
  · intro P t _ clauses
    change (if Annahme.KlauselnWahr (einheitVon P t) then true else false) = true
    split
    · rfl
    · rename_i notClauses
      exact (notClauses clauses).elim
  · intro P t _ guards
    change (if Annahme.WaechterHalten (einheitVon P t) then true else false) = true
    split
    · rfl
    · rename_i notGuards
      exact (notGuards guards).elim

theorem PrueferVollstaendigAussage.nichtTrivial :
    ∃ E : Maschine.Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit,
      Annahme.Akzeptiert E :=
  Annahme.akzeptiert_erfuellbar

/-! ### Non-triviality of the checker itself -/

/-- Partial companion: a checker accepts the empty unit, so the first half of
    `PrueferNichtTrivialAussage` is realisable. The second half needs a well-formed source unit
    whose elaboration is not accepted; no such unit exists in the current catalogue of forms, so
    that half is reported as an open witness rather than claimed. -/
theorem PrueferNichtTrivialAussage.erfuellbar :
    ∃ C : Pruefer, ∃ P t, C.pruefe P t = true := by
  refine ⟨prueferNimmtAlles, Katalog.Plattform.x86_64, ⟨[], Ast.UnitBody.done⟩, ?_⟩
  rfl

theorem PrueferNichtTrivialAussage.nichtTrivial :
    ∃ C : Pruefer, ¬ PrueferNichtTrivialAussage C := by
  refine ⟨prueferNimmtAlles, ?_⟩
  rintro ⟨_, ⟨_, _, _, refused, _⟩⟩
  change true = false at refused
  cases refused

/-! ### The undecidable remainder -/

theorem PrueferRestUnentscheidbarAussage.erfuellbar :
    PrueferRestUnentscheidbarAussage := by
  intro s Q extensible nontrivial
  exact Beobachtung.Unentscheidbar.substrat_rice s Q extensible nontrivial

/-- Rice's premise is load-bearing: for every substrate the constant-true property is
    extensional but neither empty nor full on the simulation image fails. -/
theorem PrueferRestUnentscheidbarAussage.nichtTrivial :
    ∀ (s : Beobachtung.Unentscheidbar.SimulationsSubstrat),
      ∃ Q : List Ast.Semantik.Befehl → Prop,
        ¬ ((∃ c, Q (s.programm c)) ∧ (∃ c, ¬ Q (s.programm c))) := by
  intro s
  refine ⟨fun _ => True, ?_⟩
  rintro ⟨_, ⟨c, notTrue⟩⟩
  exact notTrue True.intro

end Gabbro.Core.Ziel.Korrektheit
