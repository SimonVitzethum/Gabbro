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

/-- This is valid because of the declared 0..10 type, not over all integers. -/
theorem range_true_computed_zeuge :
    decideInvariant (Frag.Witness.declaration.traeger ()) rangeInvariant = .ok true := by
  apply (decideInvariant_true_iff Frag.Witness.initial (Frag.Witness.declaration.traeger ())
    rangeInvariant rangeFormula (by rfl)).mpr
  intro world
  change decide ((world.globs false).n ≤ 10) = true
  simpa only [decide_eq_true_eq] using (world.globs false).le_hi

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

theorem zero_false_computed_zeuge :
    decideInvariant (Frag.Witness.declaration.traeger ()) zeroInvariant = .ok false := by
  apply (decideInvariant_false_iff Frag.Witness.initial (Frag.Witness.declaration.traeger ())
    zeroInvariant zeroFormula (by rfl)).mpr
  refine ⟨Frag.Witness.initial, ?_⟩
  show wahr? (eval Frag.Witness.initial zeroInvariant Frag.Witness.initial .nil) = false
  rfl

theorem zero_concrete_counterexample_zeuge :
    ∃ world : World Frag.Witness.declaration,
      invariantCounterexample Frag.Witness.initial (Frag.Witness.declaration.traeger ())
        zeroInvariant = some world ∧ eval world zeroInvariant world .nil = false :=
  decideInvariant_complete Frag.Witness.initial (Frag.Witness.declaration.traeger ())
    zeroInvariant none zero_false_computed_zeuge

theorem short_false_computed_zeuge :
    decideInvariant (Frag.Witness.declaration.traeger ()) Witness.shortInvariant = .ok false := by
  apply (decideInvariant_false_iff Frag.Witness.initial (Frag.Witness.declaration.traeger ())
    Witness.shortInvariant Witness.shortFormula (by rfl)).mpr
  refine ⟨Frag.Witness.invalidLengthWorld, ?_⟩
  show wahr? (eval Frag.Witness.invalidLengthWorld Witness.shortInvariant
    Frag.Witness.invalidLengthWorld .nil) = false
  rfl

theorem short_counterexample_computed_zeuge :
    (invariantCounterexample Frag.Witness.initial (Frag.Witness.declaration.traeger ())
      Witness.shortInvariant).map (fun world => assignment world (.glob false)) = some 4 := by
  have translated : uebersetzeB (Frag.Witness.declaration.traeger ()) Witness.shortInvariant =
      .ok Witness.shortFormula := by rfl
  simpa only [invariantCounterexample, translated] using Witness.state_counterexample_computed_zeuge

theorem short_counterexample_sound_zeuge (world : World Frag.Witness.declaration)
    (success : invariantCounterexample Frag.Witness.initial (Frag.Witness.declaration.traeger ())
      Witness.shortInvariant = some world) :
    eval world Witness.shortInvariant world .nil = false :=
  invariantCounterexample_sound Frag.Witness.initial (Frag.Witness.declaration.traeger ())
    Witness.shortInvariant world success

theorem repeated_keys_computed_zeuge :
    Frag.Witness.boundedFormula.keys = [.glob false, .glob true] := by decide

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
    Frag.Witness.boundedFormula rfl)

theorem default_budget_total_zeuge :
    decideInvariant (Frag.Witness.declaration.traeger ()) rangeInvariant =
      .ok (decideB (closedInvariant rangeFormula)) :=
  decideInvariant_total (Frag.Witness.declaration.traeger ()) rangeInvariant rangeFormula rfl

theorem model_validity_iff_zeuge :
    decideInvariant (Frag.Witness.declaration.traeger ()) rangeInvariant = .ok true ↔
      ∀ world : World Frag.Witness.declaration, eval world rangeInvariant world .nil = true :=
  decideInvariant_true_iff Frag.Witness.initial (Frag.Witness.declaration.traeger ())
    rangeInvariant rangeFormula rfl

theorem model_counterexample_iff_zeuge :
    decideInvariant (Frag.Witness.declaration.traeger ()) Witness.shortInvariant = .ok false ↔
      ∃ world : World Frag.Witness.declaration, eval world Witness.shortInvariant world .nil = false :=
  decideInvariant_false_iff Frag.Witness.initial (Frag.Witness.declaration.traeger ())
    Witness.shortInvariant Witness.shortFormula rfl

theorem sufficient_explicit_budget_zeuge (fuel : Nat)
    (enough : Budget (closedInvariant rangeFormula) ≤ fuel) :
    decideInvariant (Frag.Witness.declaration.traeger ()) rangeInvariant (some fuel) =
      .ok (decideB (closedInvariant rangeFormula)) :=
  decideInvariant_at_budget (Frag.Witness.declaration.traeger ()) rangeInvariant rangeFormula
    rfl (some fuel) enough

theorem insufficient_budget_refused_zeuge (fuel : Nat)
    (overrun : fuel < Budget (closedInvariant rangeFormula)) :
    decideInvariant (Frag.Witness.declaration.traeger ()) rangeInvariant (some fuel) =
      .error (.decision (.budgetExceeded 0 (Budget (closedInvariant rangeFormula)) fuel)) :=
  decideInvariant_over_budget (Frag.Witness.declaration.traeger ()) rangeInvariant rangeFormula
    rfl fuel overrun

theorem nonlinear_still_refused_zeuge :
    decideInvariant (Frag.Witness.declaration.traeger ()) Frag.Witness.product =
      .error (.translation (.within "left" .nonlinear)) := by rfl

end Gabbro.Grammatik.Invarianten.Modell.DecisionWitness
