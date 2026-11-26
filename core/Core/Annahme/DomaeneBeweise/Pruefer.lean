/-
  File:      core/Core/Annahme/DomaeneBeweise/Pruefer.lean
  Subject:   MK-17 (designer decision 2026-11-26): the domain checker DECIDES coherence.

               The earlier analysis in this file refuted
               `DomaenenPrueferKorrektAussage` for the function-based `DomaenenPlan`:
               `pruefeDomaenen` inspected only the finite declaration, never the total
               assignment functions, so an incoherent plan was accepted. The counterexamples
               below still record that failure; they are not statements about the new line.

               The strengthened plan is the finite `Maschine.DomaenenTabelle` (mk17d, bound
               to the `DomaenenLokal` isolation row through `tabellePlan`). Its checker
               `pruefeDomaenenTab` additionally decides every coherence condition of
               `tabKohaerent`, and `DomaenenTabelle.wohlgeformt` is an independent structural
               condition on the finite declaration, not the line's own verdict. Over that plan
               correctness, completeness and equivalence all hold, with no `Akzeptiert` premise
               and no free enumeration hypothesis: lookup is total with default domain `0`, so
               the finite table already covers every context and device. The checker verdict
               yields `DomaenenKohaerenz` on the embedded plan through `tabellePlan_kohaerent`.
               The condition that still ranges over infinitely many assignments is a proved
               user obligation in `DomaeneBeweise/Unentscheidbar.lean`.

               This file owns its own pinned root `DomaenenPrueferAussage`, deliberately not
               under `DomaenenAussage`.
-/
module

public import Core.Annahme.Domaene
public import Core.Annahme.DomaeneBeweise.Tabellen

@[expose] public section

namespace Gabbro.Core.Annahme

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type}

/-! ### The strengthened checker statements -/

/-- CORRECTNESS of the checker over the finite-table plan: acceptance implies the independent
    structural condition and every coherence condition, with no `Akzeptiert` premise. -/
def DomaenenPrueferKorrektAussage : Prop :=
  ∀ tab : DomaenenTabelle,
    pruefeDomaenenTab tab = true → tab.wohlgeformt ∧ tabKohaerent tab

/-- COMPLETENESS of the checker over the finite-table plan: the independent structural condition
    together with coherence implies acceptance. `wohlgeformt` is not the line's verdict, so this
    leg carries real content rather than unfolding a definition. -/
def DomaenenPrueferVollstaendigAussage : Prop :=
  ∀ tab : DomaenenTabelle,
    tab.wohlgeformt ∧ tabKohaerent tab → pruefeDomaenenTab tab = true

/-- The equivalence: the line accepts exactly the well-formed coherent finite tables. -/
def DomaenenPrueferAequivalenzAussage : Prop :=
  ∀ tab : DomaenenTabelle,
    (pruefeDomaenenTab tab = true ↔ tab.wohlgeformt ∧ tabKohaerent tab)

/-- The small pinned root of the checker-line analysis. It is NOT a conjunct of `DomaenenAussage`:
    the two roots are pinned independently. -/
def DomaenenPrueferAussage : Prop :=
  DomaenenPrueferKorrektAussage ∧ DomaenenPrueferVollstaendigAussage ∧
    DomaenenPrueferAequivalenzAussage

/-! ### Proofs -/

/-- Correctness: the line's finite conjunction gives coherence, whose declaration conjuncts are
    exactly the independent structural condition. -/
theorem prueferTabellenKorrekt : DomaenenPrueferKorrektAussage := by
  intro tab h
  have hk := tabellenKorrekt tab h
  exact ⟨⟨hk.1, hk.2.2.2.2⟩, hk⟩

/-- Completeness: coherence alone already gives the line; the structural premise is recorded but
    not consumed, since it is a conjunct of coherence. -/
theorem prueferTabellenVollstaendig : DomaenenPrueferVollstaendigAussage := by
  intro tab h
  exact tabellenVollstaendig tab h.2

/-- Equivalence from the two legs. -/
theorem prueferTabellenAequivalenz : DomaenenPrueferAequivalenzAussage := by
  intro tab
  exact ⟨prueferTabellenKorrekt tab, prueferTabellenVollstaendig tab⟩

/-- The strengthened checker root holds. -/
theorem pruefer_aussage : DomaenenPrueferAussage :=
  ⟨prueferTabellenKorrekt, prueferTabellenVollstaendig, prueferTabellenAequivalenz⟩

/-- The checker decides the run-level coherence of the embedded plan: acceptance of the unit's
    finite table implies `DomaenenKohaerenz` of the plan the isolation row uses. -/
theorem pruefeDomaenenTab_kohaerenz [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) (tab : DomaenenTabelle)
    (h : pruefeDomaenenTab tab = true) :
    DomaenenKohaerenz E (tabellePlan tab) := by
  exact tabellePlan_kohaerent E tab (tabellenKorrekt tab h)

/-- Satisfiability of the strengthened checker: the single-domain table is accepted, structurally
    well-formed and coherent, and the premises of all three legs hold jointly. -/
theorem prueferTabellen_erfuellbar :
    ∃ tab : DomaenenTabelle,
      pruefeDomaenenTab tab = true ∧ tab.wohlgeformt ∧ tabKohaerent tab := by
  refine ⟨eineTabelle, eineTabelle_akzeptiert, ?_, eineTabelle_kohaerent⟩
  exact ⟨eineTabelle_kohaerent.1, eineTabelle_kohaerent.2.2.2.2⟩

/-- Non-triviality of the strengthened checker: the empty-domain table is refused, while the
    single-domain table is accepted with both premises satisfied. -/
theorem prueferTabellen_nichtTrivial :
    (∃ tab : DomaenenTabelle, pruefeDomaenenTab tab = false) ∧
      (∃ tab : DomaenenTabelle,
        pruefeDomaenenTab tab = true ∧ tab.wohlgeformt ∧ tabKohaerent tab) := by
  refine ⟨⟨leereTabelle, leereTabelle_verweigert⟩, ?_⟩
  exact prueferTabellen_erfuellbar

/-! ### What the old function-based line decided (the finding, kept as a record) -/

/-- The old line decided exactly the finite declaration: a positive domain count and in-scope
    channels. The three assignment functions were not inspected. -/
theorem pruefeDomaenen_entscheidetFinit (plan : DomaenenPlan) :
    (pruefeDomaenen plan = true) ↔
      (0 < plan.domaenen ∧
        plan.kanaele.all
          (fun k => decide (k.1 < plan.domaenen) && decide (k.2 < plan.domaenen)) = true) := by
  simp only [pruefeDomaenen, Bool.and_eq_true, decide_eq_true_eq]

/-- One declared domain and no channels, but every context assigned to domain `7`. -/
def prueferGegenbeispielPlan : DomaenenPlan where
  domaenen := 1
  kontextDomaene := fun _ => 7
  objektDomaene := fun _ => 0
  geraetDomaene := fun _ => 0
  kanaele := []

/-- The old line accepts the counterexample plan. -/
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

/-- The old line refuses the coherent plan: its channel endpoint is out of scope. -/
theorem kanalGegenbeispiel_nichtWohlgeformt :
    pruefeDomaenen kanalGegenbeispielPlan = false := rfl

/-- Coherence of a function-based plan alone never implied acceptance of the old line: the missing
    premise was the line's own verdict. This is precisely the vacuity removed by the table design. -/
theorem prueferVollstaendigOhneWohlgeformt_nicht :
    ¬ (∀ {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type} [DecidableEq L]
        (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) (plan : DomaenenPlan),
        Akzeptiert E → DomaenenKohaerenz E plan → pruefeDomaenen plan = true) := by
  intro h
  have hres := h trivialeEinheit kanalGegenbeispielPlan akzeptiert_trivial
    kanalGegenbeispiel_kohaerent
  rw [kanalGegenbeispiel_nichtWohlgeformt] at hres
  cases hres

end Gabbro.Core.Annahme
