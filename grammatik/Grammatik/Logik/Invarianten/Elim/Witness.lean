module

public import Grammatik.Logik.Invarianten.Korrekt.Linear
public import Grammatik.Logik.Invarianten.Korrekt.Budget

public section

namespace Gabbro.Grammatik.Invarianten.Elim.Witness

open Frag

def ordered : LProp Nat :=
  .all 0 (.imp (.le (.var 0) (.konst 5)) (.lt (.var 0) (.konst 6)))

theorem ordered_true_zeuge : decideB ordered = true := by decide

def oddEquation : LProp Nat := .ex 0 (.eq (.scale 2 (.var 0)) (.konst 3))

theorem oddEquation_false_zeuge : decideB oddEquation = false := by decide

/-- A genuine alternating prefix; the witness depends on the outer variable. -/
def successor : LProp Nat :=
  .all 0 (.ex 1 (.eq (.var 1) (.add (.var 0) (.konst 1))))

theorem successor_true_zeuge : decideB successor = true := by decide

def impossible : LProp Nat :=
  .ex 0 (.ex 1 (.and (.lt (.var 0) (.var 1)) (.le (.var 1) (.var 0))))

theorem impossible_false_zeuge : decideB impossible = false := by decide

/-- The only satisfying residue is represented by the infinity projection. -/
def unboundedBelow : LProp Nat :=
  .ex 0 (.and (.lt (.var 0) (.konst (-5))) (.dvd 2 (.var 0)))

theorem infinity_true_zeuge : decideB unboundedBelow = true := by decide

def emptyInterval : LProp Nat :=
  .ex 0 (.and (.lt (.konst 0) (.var 0)) (.lt (.var 0) (.konst 1)))

theorem emptyInterval_false_zeuge : decideB emptyInterval = false := by decide

def shadowed : LProp Nat :=
  .all 0 (.and (.ex 0 (.eq (.var 0) (.konst 2))) (.eq (.var 0) (.var 0)))

theorem shadowed_true_zeuge : decideB shadowed = true := by decide

def negativeDivisor : LProp Nat := .ex 0 (.dvd (-2) (.scale 2 (.var 0)))

theorem negativeDivisor_true_zeuge : decideB negativeDivisor = true := by decide

theorem zeroDivisor_true_zeuge : decideB (.dvd 0 (.konst 0) : LProp Nat) = true := by decide

theorem zeroDivisor_false_zeuge : decideB (.dvd 0 (.konst 1) : LProp Nat) = false := by decide

theorem budget_refused_zeuge :
    decideWithBudget (.tru : LProp Nat) 0 = .error (.budgetExceeded 0 1 0) := by rfl

theorem open_refused_zeuge :
    decideWithBudget (.eq (.var 0) (.konst 0) : LProp Nat) 100 = .error .freeVariables := by rfl

theorem budget_sufficient_zeuge (fuel : Nat) (enough : Budget oddEquation ≤ fuel) :
    decideWithBudget oddEquation fuel = .ok (decideB oddEquation) :=
  Korrekt.budget_sufficient oddEquation fuel (by decide) enough

theorem compile_success_zeuge :
    ∃ result spent, (compile successor).run { limit := none } =
      .ok (result,
        { limit := none
          spent := spent }) := Korrekt.compile_success successor

theorem substitution_zeuge (values : Assignment Nat) :
    (substTerm 0 (.add (.var 1) (.konst 1)) (.scale 2 (.var 0))).denote values =
      (LTerm.scale 2 (.var 0)).denote
        (values.bind 0 ((LTerm.add (.var 1) (.konst 1)).denote values)) :=
  Korrekt.substTerm_denote 0 (.add (.var 1) (.konst 1)) (.scale 2 (.var 0)) values

end Gabbro.Grammatik.Invarianten.Elim.Witness
