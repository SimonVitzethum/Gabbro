/-
  File:      core/Core/Ziel/Korrektheit/PrueferWaechterBeweise.lean
  Subject:   PROOFS of the two pinned guard-checker statements of `Core/Ziel/Korrektheit/Pruefer.lean`:
             soundness and completeness of the deployed computable guard checker
             `prueferWaechterDecidierbar`, and non-triviality of the deployed checker.

  Soundness is the abstraction lemma `waechterAbstrakt` (`Waechter/WaechterAbstrakt.lean`):
  the static analysis implies `Annahme.WaechterHalten` over all ideal runs.
  Completeness rests on the pinned fragment statement
  `WaechterFragmentVollstaendigAussage`, handed to provers. Non-triviality uses the
  accepted empty unit (`BegleitZusammensetzung`) for the first half; the second
  half needs a source unit whose elaboration is not accepted, which
  `NichtAkzeptierteEinheit.lean` supplies. The classical placeholder
  `prueferEntscheidet` is deleted: every statement here speaks about the real checker.
-/
module

public import Core.Ziel.Korrektheit.Pruefer
public import Core.Ziel.Korrektheit.Waechter.WaechterAbstrakt
public import Core.Ziel.Korrektheit.Beweise.BegleitZusammensetzung

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core

/-- The guard verdict of the deployed checker unfolds to the static analysis. -/
theorem pruefeWaechter_decidierbar (P : Katalog.Plattform) (t : Ast.Unit) :
    prueferWaechterDecidierbar.pruefeWaechter P t =
      WaechterAnalyse.waechterPruefeCode
        (Ast.Semantik.fragment Ast.Category.unit t).code := rfl

/-- The fragment verdict of the deployed checker unfolds to the named fragment. -/
theorem fragmentWaechter_decidierbar (P : Katalog.Plattform) (t : Ast.Unit) :
    prueferWaechterDecidierbar.fragmentWaechter P t =
      WaechterAnalyse.waechterFragmentCode
        (Ast.Semantik.fragment Ast.Category.unit t).code := rfl

/-- SOUNDNESS of the deployed guard checker, from the abstraction lemma. -/
theorem prueferWaechterKorrekt : PrueferWaechterKorrektAussage := by
  intro P t accepted
  rw [pruefeWaechter_decidierbar] at accepted
  exact WaechterAnalyse.waechterAbstrakt (Ast.Semantik.fragment Ast.Category.unit t) P accepted

/-- COMPLETENESS of the deployed guard checker on its fragment, from the pinned
    fragment statement. -/
theorem prueferWaechterVollstaendig
    (h : WaechterAnalyse.WaechterFragmentVollstaendigAussage) :
    PrueferWaechterVollstaendigAussage := by
  intro P t hfrag hwahr
  rw [fragmentWaechter_decidierbar] at hfrag
  rw [pruefeWaechter_decidierbar]
  exact h (Ast.Semantik.fragment Ast.Category.unit t) P hfrag hwahr

/-- The pinned soundness statement holds: it is realised by the deployed checker. -/
theorem PrueferWaechterKorrektAussage.erfuellbar : PrueferWaechterKorrektAussage :=
  prueferWaechterKorrekt

/-- COMPLETENESS is not a property of every checker: replacing the guard verdict of
    the deployed checker by the constant refusal breaks it on the accepted empty unit
    (whose fragment holds). The premise that completeness needs is a verdict that
    decides the guard conjunct on its fragment. -/
theorem prueferWaechterVollstaendigNichtFuerAlle :
    ∃ C : Pruefer, ¬ (∀ P t, C.fragmentWaechter P t = true →
      Annahme.WaechterHalten (einheitVon P t) → C.pruefeWaechter P t = true) := by
  refine ⟨{ prueferWaechterDecidierbar with pruefeWaechter := fun _ _ => false }, ?_⟩
  intro hall
  have hfrag : prueferWaechterDecidierbar.fragmentWaechter
      Katalog.Plattform.x86_64 trivialUnit = true := by
    rw [fragmentWaechter_decidierbar]
    show WaechterAnalyse.waechterFragmentCode
      (Ast.Semantik.fragment Ast.Category.unit trivialUnit).code = true
    have hcode : (Ast.Semantik.fragment Ast.Category.unit trivialUnit).code =
        [Ast.Semantik.Befehl.starte Ast.Semantik.mainName, Ast.Semantik.Befehl.ende] := rfl
    rw [hcode]
    decide
  have hA : Annahme.WaechterHalten (einheitVon Katalog.Plattform.x86_64 trivialUnit) :=
    (trivialUnit_akzeptiert Katalog.Plattform.x86_64).2.2
  have hres := hall Katalog.Plattform.x86_64 trivialUnit hfrag hA
  exact Bool.false_ne_true hres

/-- The deployed checker accepts the accepted empty unit. -/
theorem prueferWaechterDecidierbar_akzeptiertTrivial :
    prueferWaechterDecidierbar.pruefeWaechter Katalog.Plattform.x86_64 trivialUnit = true := by
  rw [pruefeWaechter_decidierbar]
  show WaechterAnalyse.waechterPruefeCode
    (Ast.Semantik.fragment Ast.Category.unit trivialUnit).code = true
  have hcode : (Ast.Semantik.fragment Ast.Category.unit trivialUnit).code =
      [Ast.Semantik.Befehl.starte Ast.Semantik.mainName, Ast.Semantik.Befehl.ende] := rfl
  rw [hcode]
  decide

/-- The first half of non-triviality: the deployed checker accepts the empty source
    unit, because its elaboration is accepted on every platform. -/
theorem prueferNichtTrivialAkzeptiert :
    ∃ P t, prueferWaechterDecidierbar.pruefe P t = true := by
  refine ⟨Katalog.Plattform.x86_64, trivialUnit, ?_⟩
  have hL : prueferWaechterDecidierbar.pruefeLokal
      Katalog.Plattform.x86_64 trivialUnit = true := rfl
  have hK : prueferWaechterDecidierbar.pruefeKlauseln
      Katalog.Plattform.x86_64 ⟨trivialUnit, []⟩ = true := rfl
  have hW := prueferWaechterDecidierbar_akzeptiertTrivial
  simp only [Pruefer.pruefe, hL, hK, hW]
  rfl

/-- The second half of non-triviality forces a source unit whose elaboration is not
    accepted. This is the precise missing premise: a witness for
    `∃ P t, ¬ Annahme.Akzeptiert (einheitVon P t)`. -/
theorem prueferNichtTrivialBrauchtNichtAkzeptierteEinheit
    (C : Pruefer) (h : PrueferNichtTrivialAussage C) :
    ∃ P t, ¬ Annahme.Akzeptiert (einheitVon P t) := by
  obtain ⟨_, ⟨P, t, _, _, hn⟩⟩ := h
  exact ⟨P, t, hn⟩

/-- If every elaborated unit is accepted, the second half of non-triviality is
    contradictory for every checker; no checker is then non-trivial. -/
theorem prueferNichtTrivialUnmoeglichOhneNichtAkzeptierteEinheit
    (hAll : ∀ P t, Annahme.Akzeptiert (einheitVon P t)) :
    ∀ C : Pruefer, ¬ PrueferNichtTrivialAussage C := by
  intro C hnt
  obtain ⟨P, t, hn⟩ := prueferNichtTrivialBrauchtNichtAkzeptierteEinheit C hnt
  exact hn (hAll P t)

end Gabbro.Core.Ziel.Korrektheit
