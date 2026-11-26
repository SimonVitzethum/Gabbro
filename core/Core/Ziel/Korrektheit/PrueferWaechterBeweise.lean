/-
  File:      core/Core/Ziel/Korrektheit/PrueferWaechterBeweise.lean
  Subject:   PROOFS of the three pinned guard-checker statements of `Core/Ziel/Korrektheit/Pruefer.lean`:
             soundness and completeness of the guard component, and non-triviality of the checker.

  The statements are indexed by a checker `C : Pruefer`; they are proved here for the concrete deciding
  checker `prueferEntscheidet` (`Beweise/BegleitPruefer.lean`), whose three verdicts are the classical
  decisions of the three conjuncts of `Annahme.Akzeptiert` and whose fragment is total. Soundness and
  completeness then reduce by `split` on the verdict, and the first half of non-triviality is discharged
  by `trivialUnit_akzeptiert` (`Beweise/BegleitZusammensetzung.lean`).

  The second half of `PrueferNichtTrivialAussage` needs a source unit whose elaboration is not accepted.
  No such unit is in the current catalogue of forms: the same witness is listed as open in
  `ZielInhaltAussage` (`core/Core/Ziel/Korrektheit/Zusammensetzung.lean`). The two theorems below that
  name the missing premise are proved: non-triviality implies such a unit, and if every elaborated unit
  is accepted then no checker is non-trivial. The missing step for the deployed checker is its computable
  decision body together with the abstraction lemma from that finite decision to `Annahme.WaechterHalten`
  over all ideal runs; the classical `if` here is a stand-in and carries no such computation.
-/
module

public import Core.Ziel.Korrektheit.Pruefer
public import Core.Ziel.Korrektheit.Beweise.BegleitPruefer
public import Core.Ziel.Korrektheit.Beweise.BegleitZusammensetzung

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Classical

/-- SOUNDNESS of the guard component, proved for the deciding checker: the verdict reduces by `split`
    and the true branch is exactly the guard premise. -/
theorem prueferWaechterKorrekt : PrueferWaechterKorrektAussage prueferEntscheidet := by
  intro P t accepted
  change (if Annahme.WaechterHalten (einheitVon P t) then true else false) = true at accepted
  split at accepted
  · assumption
  · cases accepted

/-- COMPLETENESS of the guard component on its fragment, proved for the deciding checker: the verdict
    reduces by `split`; the false branch contradicts the guard premise. -/
theorem prueferWaechterVollstaendig : PrueferWaechterVollstaendigAussage prueferEntscheidet := by
  intro P t _ guards
  change (if Annahme.WaechterHalten (einheitVon P t) then true else false) = true
  split
  · rfl
  · rename_i notGuards
    exact (notGuards guards).elim

/-- COMPLETENESS is not a property of every checker: replacing the guard verdict of the deciding
    checker by the constant refusal breaks it on the accepted empty unit (whose fragment is total).
    The premise that completeness needs is a verdict that decides the guard conjunct on its fragment. -/
theorem prueferWaechterVollstaendigNichtFuerAlle :
    ¬ ∀ C : Pruefer, PrueferWaechterVollstaendigAussage C := by
  intro allC
  let C : Pruefer := { prueferEntscheidet with pruefeWaechter := fun _ _ => false }
  have hc := allC C
  have hA : Annahme.WaechterHalten (einheitVon Katalog.Plattform.x86_64 trivialUnit) :=
    (trivialUnit_akzeptiert Katalog.Plattform.x86_64).2.2
  have hres := hc Katalog.Plattform.x86_64 trivialUnit rfl hA
  change false = true at hres
  cases hres

/-- The first half of non-triviality: the deciding checker accepts the empty source unit, because its
    elaboration is accepted on every platform. -/
theorem prueferNichtTrivialAkzeptiert : ∃ P t, prueferEntscheidet.pruefe P t = true := by
  refine ⟨Katalog.Plattform.x86_64, trivialUnit, ?_⟩
  have hA := trivialUnit_akzeptiert Katalog.Plattform.x86_64
  have hL : (if Annahme.Lokal (einheitVon Katalog.Plattform.x86_64 trivialUnit) then true else false) = true := by
    split
    · rfl
    · rename_i h
      exact (h hA.1).elim
  have hK : (if Annahme.KlauselnWahr
      (Ast.Semantik.elaborierenMitInvarianten Katalog.Plattform.x86_64 ⟨trivialUnit, []⟩)
      then true else false) = true := by
    rw [← einheitVon_mitInvarianten]
    split
    · rfl
    · rename_i h
      exact (h hA.2.1).elim
  have hW : (if Annahme.WaechterHalten (einheitVon Katalog.Plattform.x86_64 trivialUnit) then true else false) = true := by
    split
    · rfl
    · rename_i h
      exact (h hA.2.2).elim
  simp only [Pruefer.pruefe, prueferEntscheidet, hL, hK, hW]
  rfl

/-- With a source unit whose elaboration is not accepted, non-triviality is proved for the deciding
    checker: the verdict is false because acceptance fails, and the fragment is total. -/
theorem prueferNichtTrivialAusNichtAkzeptierterEinheit
    (hNA : ∃ P t, ¬ Annahme.Akzeptiert (einheitVon P t)) :
    ∃ C : Pruefer, PrueferNichtTrivialAussage C := by
  refine ⟨prueferEntscheidet, ?_⟩
  constructor
  · exact prueferNichtTrivialAkzeptiert
  · obtain ⟨P, t, hn⟩ := hNA
    refine ⟨P, t, rfl, ?_, hn⟩
    simp only [Pruefer.pruefe, prueferEntscheidet]
    split
    · rename_i hL
      split
      · rename_i hK
        split
        · rename_i hW
          exact False.elim (hn ⟨hL, hK, hW⟩)
        · rfl
      · rfl
    · rfl

/-- The second half of non-triviality forces a source unit whose elaboration is not accepted. This is
    the precise missing premise: a witness for `∃ P t, ¬ Annahme.Akzeptiert (einheitVon P t)`. -/
theorem prueferNichtTrivialBrauchtNichtAkzeptierteEinheit
    (C : Pruefer) (h : PrueferNichtTrivialAussage C) :
    ∃ P t, ¬ Annahme.Akzeptiert (einheitVon P t) := by
  obtain ⟨_, ⟨P, t, _, _, hn⟩⟩ := h
  exact ⟨P, t, hn⟩

/-- If every elaborated unit is accepted, the second half of non-triviality is contradictory for every
    checker; no checker is then non-trivial. -/
theorem prueferNichtTrivialUnmoeglichOhneNichtAkzeptierteEinheit
    (hAll : ∀ P t, Annahme.Akzeptiert (einheitVon P t)) :
    ∀ C : Pruefer, ¬ PrueferNichtTrivialAussage C := by
  intro C hnt
  obtain ⟨P, t, hn⟩ := prueferNichtTrivialBrauchtNichtAkzeptierteEinheit C hnt
  exact hn (hAll P t)

end Gabbro.Core.Ziel.Korrektheit
