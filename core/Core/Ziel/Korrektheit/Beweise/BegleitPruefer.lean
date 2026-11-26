/-
   File:      core/Core/Ziel/Korrektheit/Beweise/BegleitPruefer.lean
   Subject:   COMPANION LEMMAS for the pinned statements of `Core/Ziel/Korrektheit/Pruefer.lean`
              (checker correctness): for every `…Aussage` an `X.erfuellbar` (a checker satisfying
              the statement, with the decision premises realised) and an `X.nichtTrivial`
              (a non-accepted object or a degenerate checker violates the statement). No pinned
              statement is changed. The soundness companions use `staleEinheit`; the completeness
              companions use `akzeptiert_erfuellbar`. The local component is decided by the
              classical stand-in `prueferLokalEntscheidet` (the local workstream replaces it with
              the decidable local checker); the guard component is the deployed computable
              checker `prueferWaechterDecidierbar`, whose soundness and completeness are proved
              in `PrueferWaechterBeweise.lean`; the clause statements use the decidable checker
              of `PrueferKlauseln.lean` with its real proofs. The whole-checker witness
              `prueferKombiniert` composes the three.
-/
module

public import Core.Ziel.Korrektheit.Pruefer
public import Core.Ziel.Korrektheit.PrueferKlauseln
public import Core.Ziel.Korrektheit.PrueferWaechterBeweise
public import Core.Ziel.Korrektheit.Waechter.WaechterAbstrakt
public import Core.Ziel.Korrektheit.NichtAkzeptierteEinheit
public import Core.Annahme.Annahme
public import Core.Beobachtung.Unentscheidbar.Modell

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Classical

/-- The classical stand-in for the local component: the local workstream replaces
    it with the decidable local checker. -/
noncomputable def prueferLokalEntscheidet : Pruefer where
  pruefeLokal := fun P t => if Annahme.Lokal (einheitVon P t) then true else false
  pruefeKlauseln := fun _ _ => true
  pruefeWaechter := fun _ _ => true
  fragmentLokal := fun _ _ => true
  fragmentKlauseln := fun _ _ => true
  fragmentWaechter := fun _ _ => true

/-- The combined whole checker: classical local verdicts, the decidable clause
    checker and the computable guard checker. -/
noncomputable def prueferKombiniert : Pruefer where
  pruefeLokal := prueferLokalEntscheidet.pruefeLokal
  pruefeKlauseln := prueferKlauselnDecidierbar.pruefeKlauseln
  pruefeWaechter := prueferWaechterDecidierbar.pruefeWaechter
  fragmentLokal := fun _ _ => true
  fragmentKlauseln := prueferKlauselnDecidierbar.fragmentKlauseln
  fragmentWaechter := prueferWaechterDecidierbar.fragmentWaechter

/-- The guard verdict of the combined checker unfolds to the static analysis. -/
theorem prueferKombiniert_pruefeWaechter (P : Katalog.Plattform) (t : Ast.Unit) :
    prueferKombiniert.pruefeWaechter P t =
      WaechterAnalyse.waechterPruefeCode
        (Ast.Semantik.fragment Ast.Category.unit t).code := rfl

/-- The guard fragment of the combined checker unfolds to the named fragment. -/
theorem prueferKombiniert_fragmentWaechter (P : Katalog.Plattform) (t : Ast.Unit) :
    prueferKombiniert.fragmentWaechter P t =
      WaechterAnalyse.waechterFragmentCode
        (Ast.Semantik.fragment Ast.Category.unit t).code := rfl

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
  refine ⟨prueferLokalEntscheidet, ?_⟩
  intro P t accepted
  change (if Annahme.Lokal (einheitVon P t) then true else false) = true at accepted
  split at accepted
  · assumption
  · cases accepted

theorem PrueferLokalKorrektAussage.nichtTrivial :
    ∃ E : Maschine.Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit, ¬ Annahme.Lokal E :=
  lokalNichtTrivial

theorem PrueferKlauselnKorrektAussage.erfuellbar :
    ∃ C : Pruefer, PrueferKlauselnKorrektAussage C :=
  ⟨prueferKlauselnDecidierbar, prueferKlauselnKorrekt_fuerDecidierbar⟩

/-- Soundness over units with declared invariants is not vacuous in the other direction: the
    accept-everything checker violates it on the unit whose invariant is violated. -/
theorem PrueferKlauselnKorrektAussage.nichtTrivial :
    ∃ C : Pruefer, ¬ PrueferKlauselnKorrektAussage C := by
  refine ⟨prueferNimmtAlles, ?_⟩
  intro h
  have hacc : prueferNimmtAlles.pruefeKlauseln Katalog.Plattform.x86_64 verletzteInvariante
      = true := rfl
  exact verletzteInvariante_verletzt _ (h _ _ hacc)

theorem PrueferKorrektAussage.erfuellbar : ∃ C : Pruefer, PrueferKorrektAussage C := by
  refine ⟨prueferKombiniert, ?_⟩
  apply pruefer_korrekt_aus_teilen
  · intro P t accepted
    change (if Annahme.Lokal (einheitVon P t) then true else false) = true at accepted
    split at accepted
    · assumption
    · cases accepted
  · intro P u accepted
    exact prueferKlauselnKorrekt_fuerDecidierbar P u accepted
  · intro P t accepted
    exact prueferWaechterKorrekt P t accepted

theorem PrueferKorrektAussage.nichtTrivial :
    ∃ E : Maschine.Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit,
      ¬ Annahme.Akzeptiert E :=
  akzeptiertNichtTrivial

/-! ### Completeness components -/

theorem PrueferLokalVollstaendigAussage.erfuellbar :
    ∃ C : Pruefer, PrueferLokalVollstaendigAussage C := by
  refine ⟨prueferLokalEntscheidet, ?_⟩
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
    ∃ C : Pruefer, PrueferKlauselnVollstaendigAussage C :=
  ⟨prueferKlauselnDecidierbar, prueferKlauselnVollstaendig_fuerDecidierbar⟩

theorem PrueferKlauselnVollstaendigAussage.nichtTrivial :
    ∃ E : Maschine.Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit,
      Annahme.Akzeptiert E :=
  Annahme.akzeptiert_erfuellbar

theorem PrueferVollstaendigAussage.erfuellbar
    (h : WaechterAnalyse.WaechterFragmentVollstaendigAussage) :
    ∃ C : Pruefer, PrueferVollstaendigAussage C := by
  refine ⟨prueferKombiniert, ?_⟩
  apply pruefer_vollstaendig_aus_teilen
  · intro P t _ hLocal
    change (if Annahme.Lokal (einheitVon P t) then true else false) = true
    split
    · rfl
    · rename_i notLocal
      exact (notLocal hLocal).elim
  · intro P u hfrag clauses
    exact prueferKlauselnVollstaendig_fuerDecidierbar P u hfrag clauses
  · intro P t hfrag hwahr
    exact prueferWaechterVollstaendig h P t hfrag hwahr

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

/-- The combined checker is non-trivial in both directions: it accepts the empty
    unit and it refuses the witness unit of `NichtAkzeptierteEinheit`, whose
    elaboration is not accepted. -/
theorem prueferKombiniert_nichtTrivial : PrueferNichtTrivialAussage prueferKombiniert := by
  constructor
  · refine ⟨Katalog.Plattform.x86_64, trivialUnit, ?_⟩
    have hA := trivialUnit_akzeptiert Katalog.Plattform.x86_64
    have hL : prueferKombiniert.pruefeLokal
        Katalog.Plattform.x86_64 trivialUnit = true := by
      show (if Annahme.Lokal (einheitVon Katalog.Plattform.x86_64 trivialUnit)
        then true else false) = true
      split
      · rfl
      · rename_i h
        exact (h hA.1).elim
    have hK : prueferKombiniert.pruefeKlauseln
        Katalog.Plattform.x86_64 ⟨trivialUnit, []⟩ = true :=
      Ast.Semantik.pruefeEinheit_leer _
    have hW : prueferKombiniert.pruefeWaechter
        Katalog.Plattform.x86_64 trivialUnit = true := by
      rw [prueferKombiniert_pruefeWaechter]
      show WaechterAnalyse.waechterPruefeCode
        (Ast.Semantik.fragment Ast.Category.unit trivialUnit).code = true
      have hcode : (Ast.Semantik.fragment Ast.Category.unit trivialUnit).code =
          [Ast.Semantik.Befehl.starte Ast.Semantik.mainName, Ast.Semantik.Befehl.ende] := rfl
      rw [hcode]
      rfl
    simp only [Pruefer.pruefe, hL, hK, hW]
    rfl
  · have hFL : prueferKombiniert.fragmentLokal
        Katalog.Plattform.x86_64 textIndexUnit = true := rfl
    have hFK : prueferKombiniert.fragmentKlauseln
        Katalog.Plattform.x86_64 ⟨textIndexUnit, []⟩ = true := by
      show (Ast.Semantik.programmMitInvarianten ⟨textIndexUnit, []⟩).code.all
        (Ast.Semantik.pruefeBefehlErhalt []) = true
      have hcode : (Ast.Semantik.programmMitInvarianten ⟨textIndexUnit, []⟩).code =
          textIndexCode := rfl
      rw [hcode, textIndexUnit_code]
      rfl
    have hFW : prueferKombiniert.fragmentWaechter
        Katalog.Plattform.x86_64 textIndexUnit = true := by
      rw [prueferKombiniert_fragmentWaechter]
      show WaechterAnalyse.waechterFragmentCode textIndexCode = true
      exact textIndexFragment
    have hPW : prueferKombiniert.pruefeWaechter
        Katalog.Plattform.x86_64 textIndexUnit = false := by
      rw [prueferKombiniert_pruefeWaechter]
      show WaechterAnalyse.waechterPruefeCode textIndexCode = false
      exact textIndexRefusiert
    refine ⟨Katalog.Plattform.x86_64, textIndexUnit, ?_, ?_, textIndexUnit_nicht_akzeptiert⟩
    · simp only [Pruefer.fragment, hFL, hFK, hFW]
      rfl
    · have hfalse : (prueferKombiniert.pruefeLokal Katalog.Plattform.x86_64 textIndexUnit &&
          prueferKombiniert.pruefeKlauseln Katalog.Plattform.x86_64 ⟨textIndexUnit, []⟩ &&
          prueferKombiniert.pruefeWaechter Katalog.Plattform.x86_64 textIndexUnit) =
          false := by
        rw [hPW, Bool.and_false]
      simpa only [Pruefer.pruefe] using hfalse

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
