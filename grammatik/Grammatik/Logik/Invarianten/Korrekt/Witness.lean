module

public import Grammatik.Logik.Invarianten.Korrekt.Decision

public section

namespace Gabbro.Grammatik.Invarianten.Elim.Korrekt.Witness

open Frag

/-- A lower boundary and a nontrivial divisor must both survive elimination. -/
def evenAbove : LProp Nat :=
  .ex 0 (.and (.lt (.konst 3) (.var 0)) (.dvd 2 (.var 0)))

/-- Normalization's extra image constraint rules out this rational solution. -/
def oddEquation : LProp Nat := .ex 0 (.eq (.scale 2 (.var 0)) (.konst 3))

theorem evenAbove_computed_zeuge : decideB evenAbove = true := by
  apply (decideB_true_iff evenAbove (by rfl) (fun _ => 0)).mpr
  refine ⟨4, ?_, ?_⟩
  · change (3 : Int) < 4
    decide
  · change (2 : Int) ∣ 4
    exact ⟨2, rfl⟩

theorem oddEquation_computed_zeuge : decideB oddEquation = false := by
  apply (decideB_false_iff oddEquation (by rfl) (fun _ => 0)).mpr
  rintro ⟨value, equation⟩
  change 2 * value = 3 at equation
  omega

theorem decideB_sound_zeuge (values : Assignment Nat) : evenAbove.denote values :=
  decideB_sound evenAbove (by decide) evenAbove_computed_zeuge values

theorem decideB_complete_zeuge (values : Assignment Nat) : ¬ oddEquation.denote values :=
  decideB_complete oddEquation (by decide) oddEquation_computed_zeuge values

theorem decideB_of_valid_zeuge (values : Assignment Nat) : decideB evenAbove = true :=
  decideB_of_valid evenAbove (by decide) values (decideB_sound_zeuge values)

theorem decideB_false_iff_zeuge (values : Assignment Nat) :
    decideB oddEquation = false ↔ ¬ oddEquation.denote values :=
  decideB_false_iff oddEquation (by decide) values

theorem decideWithBudget_at_Budget_zeuge (values : Assignment Nat) :
    (decideWithBudget evenAbove (Budget evenAbove) = .ok true ↔ evenAbove.denote values) ∧
    (decideWithBudget evenAbove (Budget evenAbove) = .ok false ↔ ¬ evenAbove.denote values) :=
  decideWithBudget_at_Budget evenAbove (by decide) values

end Gabbro.Grammatik.Invarianten.Elim.Korrekt.Witness
