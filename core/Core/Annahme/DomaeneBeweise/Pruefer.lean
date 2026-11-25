/-
  File:      core/Core/Annahme/DomaeneBeweise/Pruefer.lean
  Subject:   OPEN 3 of MK-17: correctness and completeness of the static checker line
              `pruefeDomaenen` against `DomaenenKohaerenz` / `Akzeptiert`, formulated as
              `pruefeDomaenen p = true ↔ p.wohlgeformt ∧ DomaenenKohaerenz E p`.

              The claimed equivalence is REFUTED: the line decides only the finite declaration
              (domain count and channel bounds), never the total assignment functions of the
              plan. Completeness holds only because `wohlgeformt` is by definition the line's
              own verdict; if that premise is dropped, completeness fails too.

              No pinned statement in `Domaene.lean` is changed. This file owns its own small
              pinned root `DomaenenPrueferAussage`, deliberately not under `DomaenenAussage`.
-/
module

public import Core.Annahme.Domaene

@[expose] public section

namespace Gabbro.Core.Annahme

open Gabbro.Core.Maschine

/-- CORRECTNESS of the checker line against coherence: for an accepted unit, every plan the line
    accepts is well-formed and coherent. This is the forward leg of the claimed equivalence. -/
def DomaenenPrueferKorrektAussage : Prop :=
  ∀ {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type} [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) (plan : DomaenenPlan),
    Akzeptiert E → pruefeDomaenen plan = true →
      plan.wohlgeformt ∧ DomaenenKohaerenz E plan

/-- COMPLETENESS of the checker line against coherence: for an accepted unit, every well-formed
    and coherent plan passes the line. This is the backward leg of the claimed equivalence. -/
def DomaenenPrueferVollstaendigAussage : Prop :=
  ∀ {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type} [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) (plan : DomaenenPlan),
    Akzeptiert E → plan.wohlgeformt ∧ DomaenenKohaerenz E plan →
      pruefeDomaenen plan = true

/-- The claimed equivalence: over an accepted unit, the line accepts exactly the well-formed and
    coherent plans. -/
def DomaenenPrueferAequivalenzAussage : Prop :=
  ∀ {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type} [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) (plan : DomaenenPlan),
    Akzeptiert E →
      (pruefeDomaenen plan = true ↔ plan.wohlgeformt ∧ DomaenenKohaerenz E plan)

/-- The small pinned root of the checker-line analysis. It is NOT a conjunct of `DomaenenAussage`:
    the two roots are pinned independently. -/
def DomaenenPrueferAussage : Prop :=
  DomaenenPrueferKorrektAussage ∧ DomaenenPrueferVollstaendigAussage ∧
    DomaenenPrueferAequivalenzAussage

/-! ### What the line actually decides -/

/-- The line decides exactly the finite declaration: a positive domain count and in-scope
    channels. The three assignment functions are not inspected. -/
theorem pruefeDomaenen_entscheidetFinit (plan : DomaenenPlan) :
    (pruefeDomaenen plan = true) ↔
      (0 < plan.domaenen ∧
        plan.kanaele.all
          (fun k => decide (k.1 < plan.domaenen) && decide (k.2 < plan.domaenen)) = true) := by
  simp only [pruefeDomaenen, Bool.and_eq_true, decide_eq_true_eq]

/-! ### Counterexample: accepted line, accepted unit, incoherent plan -/

/-- One declared domain and no channels, but every context assigned to domain `7`. -/
def prueferGegenbeispielPlan : DomaenenPlan where
  domaenen := 1
  kontextDomaene := fun _ => 7
  objektDomaene := fun _ => 0
  geraetDomaene := fun _ => 0
  kanaele := []

/-- The line accepts the counterexample plan. -/
theorem prueferGegenbeispiel_wohlgeformt :
    pruefeDomaenen prueferGegenbeispielPlan = true := rfl

/-- The counterexample plan is not coherent with the trivial unit: a context is assigned outside
    the single declared domain. -/
theorem prueferGegenbeispiel_nichtKohaerent :
    ¬ DomaenenKohaerenz trivialeEinheit prueferGegenbeispielPlan := by
  intro h
  have hbad : (7 : Nat) < 1 := h.1 (.faden 0)
  have hnein : ¬ (7 : Nat) < 1 := by decide
  exact hnein hbad

/-! ### Counterexample: coherent plan, refused line -/

/-- All assignments in range, but a channel leaving the single declared domain. -/
def kanalGegenbeispielPlan : DomaenenPlan where
  domaenen := 1
  kontextDomaene := fun _ => 0
  objektDomaene := fun _ => 0
  geraetDomaene := fun _ => 0
  kanaele := [(0, 7)]

/-- The coherent plan passes coherence with the trivial unit. -/
theorem kanalGegenbeispiel_kohaerent :
    DomaenenKohaerenz trivialeEinheit kanalGegenbeispielPlan := by
  refine ⟨fun _ => Nat.zero_lt_one, fun _ => Nat.zero_lt_one, fun _ => Nat.zero_lt_one⟩

/-- The line refuses the coherent plan: its channel endpoint is out of scope. -/
theorem kanalGegenbeispiel_nichtWohlgeformt :
    pruefeDomaenen kanalGegenbeispielPlan = false := rfl

/-- Coherence alone does not imply acceptance: the missing premise of completeness is
    `plan.wohlgeformt`, i.e. the line's own verdict. -/
theorem prueferVollstaendigOhneWohlgeformt_nicht :
    ¬ (∀ {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type} [DecidableEq L]
        (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) (plan : DomaenenPlan),
        Akzeptiert E → DomaenenKohaerenz E plan → pruefeDomaenen plan = true) := by
  intro h
  have hres := h trivialeEinheit kanalGegenbeispielPlan akzeptiert_trivial
    kanalGegenbeispiel_kohaerent
  rw [kanalGegenbeispiel_nichtWohlgeformt] at hres
  cases hres

/-! ### Verdicts -/

/-- Completeness holds, but only because `wohlgeformt` is by definition the line's verdict. The
    premises are jointly satisfiable by the trivial unit and the single-domain plan. -/
theorem prueferVollstaendig : DomaenenPrueferVollstaendigAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl ι decL E plan akzeptiert h
  exact h.1

/-- The completeness premises can hold together: no vacuous obligation. -/
theorem prueferVollstaendig_erfuellbar :
    ∃ (E : Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit) (plan : DomaenenPlan),
      Akzeptiert E ∧ plan.wohlgeformt ∧ DomaenenKohaerenz E plan :=
  ⟨trivialeEinheit, eineDomaene, akzeptiert_trivial, eineDomaene_wohlgeformt,
    eineDomaene_kohaerent⟩

/-- Correctness fails even over an accepted unit: the line never checks the assignment
    functions. -/
theorem prueferKorrekt_nicht : ¬ DomaenenPrueferKorrektAussage := by
  intro h
  have hres := h trivialeEinheit prueferGegenbeispielPlan akzeptiert_trivial
    prueferGegenbeispiel_wohlgeformt
  exact prueferGegenbeispiel_nichtKohaerent hres.2

/-- The claimed equivalence fails for the same plan. -/
theorem prueferAequivalenz_nicht : ¬ DomaenenPrueferAequivalenzAussage := by
  intro h
  have hiff := h trivialeEinheit prueferGegenbeispielPlan akzeptiert_trivial
  exact prueferGegenbeispiel_nichtKohaerent
    (hiff.mp prueferGegenbeispiel_wohlgeformt).2

/-- The pinned root is refuted: its correctness and equivalence conjuncts are false. -/
theorem prueferAussage_nicht : ¬ DomaenenPrueferAussage := by
  intro h
  exact prueferKorrekt_nicht h.1

end Gabbro.Core.Annahme
