module

public import Grammatik.Logik.Invarianten.Modell.Decision
public import Grammatik.Logik.Invarianten.Modell.Witness

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Modell.DecisionWitness

open Frag Elim Elim.Korrekt

def rangeInvariant : Expr Frag.Witness.declaration [] [] .bool :=
  .le (.glob false (Frag.Witness.globalAccess false)) (.lit 10)

def rangeFormula : LProp (Observation Frag.Witness.declaration) :=
  .le (.var (.glob false)) (.konst 10)

theorem range_translated_zeuge :
    uebersetzeB (Frag.Witness.declaration.traeger ()) rangeInvariant = .ok rangeFormula := by rfl

/-- This is valid because of the declared 0..10 type, not over all integers. -/
theorem range_true_computed_zeuge :
    decideInvariant (Frag.Witness.declaration.traeger ()) rangeInvariant = .ok true := by
  apply (decideInvariant_true_iff Frag.Witness.initial (Frag.Witness.declaration.traeger ())
    rangeInvariant rangeFormula range_translated_zeuge).mpr
  intro world
  apply (uebersetzeB_sound (Frag.Witness.declaration.traeger ()) rangeInvariant rangeFormula
    range_translated_zeuge world).mpr
  have bounds := observationBounds_assignment rangeFormula.keys world
    (uebersetzeB_supported (Frag.Witness.declaration.traeger ()) rangeInvariant rangeFormula
      range_translated_zeuge)
  change ((0 : Int) ≤ assignment world (.glob false) ∧
    assignment world (.glob false) ≤ 10) ∧ True at bounds
  exact bounds.1.2

theorem range_true_sound_zeuge (world : World Frag.Witness.declaration) :
    eval world rangeInvariant world .nil = true :=
  decideInvariant_sound (Frag.Witness.declaration.traeger ()) rangeInvariant none
    range_true_computed_zeuge world

/-- Regression: evaluating this open formula at zero would incorrectly accept
    it as a universal invariant. The composed entry point answers FALSE. -/
def zeroInvariant : Expr Frag.Witness.declaration [] [] .bool :=
  .eq (.glob false (Frag.Witness.globalAccess false)) (.lit 0)

def zeroFormula : LProp (Observation Frag.Witness.declaration) :=
  .eq (.var (.glob false)) (.konst 0)

theorem zero_translated_zeuge :
    uebersetzeB (Frag.Witness.declaration.traeger ()) zeroInvariant = .ok zeroFormula := by rfl

theorem zero_false_computed_zeuge :
    decideInvariant (Frag.Witness.declaration.traeger ()) zeroInvariant = .ok false := by
  apply (decideInvariant_false_iff Frag.Witness.initial (Frag.Witness.declaration.traeger ())
    zeroInvariant zeroFormula zero_translated_zeuge).mpr
  refine ⟨Frag.Witness.initial, ?_⟩
  change wahr? (eval Frag.Witness.initial zeroInvariant Frag.Witness.initial .nil) = false
  apply Bool.eq_false_iff.mpr
  intro evaluated
  have impossible := (uebersetzeB_sound (Frag.Witness.declaration.traeger ()) zeroInvariant
    zeroFormula zero_translated_zeuge Frag.Witness.initial).mp evaluated
  change (3 : Int) = 0 at impossible
  omega

theorem zero_concrete_counterexample_zeuge :
    ∃ world : World Frag.Witness.declaration,
      invariantCounterexample Frag.Witness.initial (Frag.Witness.declaration.traeger ())
        zeroInvariant = some world ∧ eval world zeroInvariant world .nil = false :=
  decideInvariant_complete Frag.Witness.initial (Frag.Witness.declaration.traeger ())
    zeroInvariant none zero_false_computed_zeuge

theorem short_false_computed_zeuge :
    decideInvariant (Frag.Witness.declaration.traeger ()) Witness.shortInvariant = .ok false := by
  apply (decideInvariant_false_iff Frag.Witness.initial (Frag.Witness.declaration.traeger ())
    Witness.shortInvariant Witness.shortFormula Witness.short_translated_zeuge).mpr
  refine ⟨Frag.Witness.invalidLengthWorld, ?_⟩
  change wahr? (eval Frag.Witness.invalidLengthWorld Witness.shortInvariant
    Frag.Witness.invalidLengthWorld .nil) = false
  apply Bool.eq_false_iff.mpr
  intro evaluated
  have impossible := (uebersetzeB_sound (Frag.Witness.declaration.traeger ())
    Witness.shortInvariant Witness.shortFormula Witness.short_translated_zeuge
    Frag.Witness.invalidLengthWorld).mp evaluated
  change (9 : Int) ≤ 3 at impossible
  omega

/-- The model entry point returns a refuting typed state, without fixing the
    extractor's choice among the admissible counterexample values 4..10. -/
theorem short_counterexample_exists_zeuge :
    ∃ world : World Frag.Witness.declaration,
      invariantCounterexample Frag.Witness.initial (Frag.Witness.declaration.traeger ())
        Witness.shortInvariant = some world ∧
      eval world Witness.shortInvariant world .nil = false :=
  decideInvariant_complete Frag.Witness.initial (Frag.Witness.declaration.traeger ())
    Witness.shortInvariant none short_false_computed_zeuge

theorem short_counterexample_sound_zeuge (world : World Frag.Witness.declaration)
    (success : invariantCounterexample Frag.Witness.initial (Frag.Witness.declaration.traeger ())
      Witness.shortInvariant = some world) :
    eval world Witness.shortInvariant world .nil = false :=
  invariantCounterexample_sound Frag.Witness.initial (Frag.Witness.declaration.traeger ())
    Witness.shortInvariant world success

theorem repeated_keys_computed_zeuge :
    Frag.Witness.boundedFormula.keys = [.glob false, .glob true] := by
  have different :
      ((Observation.glob true : Observation Frag.Witness.declaration) == .glob false) =
        false := by decide
  have same :
      ((Observation.glob false : Observation Frag.Witness.declaration) == .glob false) =
        true := by decide
  simp [Frag.Witness.boundedFormula, LProp.keys, LProp.freeVariables, LTerm.variables,
    List.eraseDups_cons, different, same]

def shadowedFormula : LProp Nat :=
  .all 0 (.and (.eq (.var 0) (.var 0)) (.eq (.var 1) (.konst 0)))

theorem free_keys_shadowing_zeuge : shadowedFormula.keys = [1] := by decide

theorem free_keys_support_zeuge : closedUnderB shadowedFormula.keys shadowedFormula = true :=
  shadowedFormula.keys_supported

theorem closure_closed_zeuge :
    closedUnderB [] (closedInvariant Frag.Witness.boundedFormula) = true :=
  closedInvariant_closed Frag.Witness.boundedFormula

theorem generated_ranges_hold_zeuge (world : World Frag.Witness.declaration) :
    (observationBounds Frag.Witness.boundedFormula.keys).denote (assignment world) :=
  observationBounds_assignment _ world (uebersetzeB_supported
    (Frag.Witness.declaration.traeger ()) Frag.Witness.boundedLength
    Frag.Witness.boundedFormula Frag.Witness.boundedLength_translated_zeuge)

theorem default_budget_total_zeuge :
    decideInvariant (Frag.Witness.declaration.traeger ()) rangeInvariant =
      .ok (decideB (closedInvariant rangeFormula)) :=
  decideInvariant_total (Frag.Witness.declaration.traeger ()) rangeInvariant rangeFormula
    range_translated_zeuge

theorem model_validity_iff_zeuge :
    decideInvariant (Frag.Witness.declaration.traeger ()) rangeInvariant = .ok true ↔
      ∀ world : World Frag.Witness.declaration, eval world rangeInvariant world .nil = true :=
  decideInvariant_true_iff Frag.Witness.initial (Frag.Witness.declaration.traeger ())
    rangeInvariant rangeFormula range_translated_zeuge

theorem model_counterexample_iff_zeuge :
    decideInvariant (Frag.Witness.declaration.traeger ()) Witness.shortInvariant = .ok false ↔
      ∃ world : World Frag.Witness.declaration, eval world Witness.shortInvariant world .nil = false :=
  decideInvariant_false_iff Frag.Witness.initial (Frag.Witness.declaration.traeger ())
    Witness.shortInvariant Witness.shortFormula Witness.short_translated_zeuge

theorem sufficient_explicit_budget_zeuge (fuel : Nat)
    (enough : Budget (closedInvariant rangeFormula) ≤ fuel) :
    decideInvariant (Frag.Witness.declaration.traeger ()) rangeInvariant (some fuel) =
      .ok (decideB (closedInvariant rangeFormula)) :=
  decideInvariant_at_budget (Frag.Witness.declaration.traeger ()) rangeInvariant rangeFormula
    range_translated_zeuge (some fuel) enough

theorem insufficient_budget_refused_zeuge (fuel : Nat)
    (overrun : fuel < Budget (closedInvariant rangeFormula)) :
    decideInvariant (Frag.Witness.declaration.traeger ()) rangeInvariant (some fuel) =
      .error (.decision (.budgetExceeded 0 (Budget (closedInvariant rangeFormula)) fuel)) :=
  decideInvariant_over_budget (Frag.Witness.declaration.traeger ()) rangeInvariant rangeFormula
    range_translated_zeuge fuel overrun

theorem nonlinear_still_refused_zeuge :
    decideInvariant (Frag.Witness.declaration.traeger ()) Frag.Witness.product =
      .error (.translation (.within "left" .nonlinear)) := by
  simp only [decideInvariant, Frag.Witness.product_refused_zeuge]

end Gabbro.Grammatik.Invarianten.Modell.DecisionWitness
