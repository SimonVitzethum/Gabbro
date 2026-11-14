module

public import Grammatik.Logik.Invarianten.Korrekt.Compile

public section

namespace Gabbro.Grammatik.Invarianten.Elim.Korrekt

open Frag

theorem term_closed_congr [DecidableEq α] (bound : List α) (term : LTerm α)
    (values other : Assignment α) (closed : termClosedB bound term = true)
    (agree : ∀ name ∈ bound, values name = other name) :
    term.denote values = term.denote other := by
  induction term with
  | var name =>
      apply agree name
      simpa [termClosedB] using closed
  | konst value => rfl
  | add left right ihLeft ihRight =>
      simp only [termClosedB, Bool.and_eq_true] at closed
      simp only [LTerm.denote, ihLeft closed.1, ihRight closed.2]
  | sub left right ihLeft ihRight =>
      simp only [termClosedB, Bool.and_eq_true] at closed
      simp only [LTerm.denote, ihLeft closed.1, ihRight closed.2]
  | scale coefficient term ih =>
      simp only [LTerm.denote, ih closed]

/-- Closedness respects nested quantifiers which bind an already-used name. -/
theorem closed_congr [DecidableEq α] (bound : List α) (formula : LProp α)
    (values other : Assignment α) (closed : closedUnderB bound formula = true)
    (agree : ∀ name ∈ bound, values name = other name) :
    formula.denote values ↔ formula.denote other := by
  induction formula generalizing bound values other with
  | tru => rfl
  | fls => rfl
  | le left right | lt left right | eq left right =>
      simp only [closedUnderB, Bool.and_eq_true] at closed
      simp only [LProp.denote, term_closed_congr bound left values other closed.1 agree,
        term_closed_congr bound right values other closed.2 agree]
  | dvd divisor term =>
      simp only [LProp.denote, term_closed_congr bound term values other closed agree]
  | not body ih => exact not_congr (ih bound values other closed agree)
  | and left right ihLeft ihRight | or left right ihLeft ihRight | imp left right ihLeft ihRight =>
      simp only [closedUnderB, Bool.and_eq_true] at closed
      simp only [LProp.denote, ihLeft bound values other closed.1 agree,
        ihRight bound values other closed.2 agree]
  | ex name body ih =>
      apply exists_congr
      intro x
      apply ih (name :: bound) (values.bind name x) (other.bind name x) closed
      intro otherName member
      by_cases h : otherName = name
      · simp [Assignment.bind, h]
      · have hm : otherName ∈ bound := (List.mem_cons.mp member).resolve_left h
        simp [Assignment.bind, h, agree otherName hm]
  | all name body ih =>
      apply forall_congr'
      intro x
      apply ih (name :: bound) (values.bind name x) (other.bind name x) closed
      intro otherName member
      by_cases h : otherName = name
      · simp [Assignment.bind, h]
      · have hm : otherName ∈ bound := (List.mem_cons.mp member).resolve_left h
        simp [Assignment.bind, h, agree otherName hm]

/-- No semantic precondition is imposed on formulas beyond syntactic closedness. -/
theorem decideB_true_iff [DecidableEq α] (formula : LProp α)
    (closed : closedUnderB [] formula = true) (values : Assignment α) :
    decideB formula = true ↔ formula.denote values := by
  unfold decideB
  rw [qf_eval, elimination_denote]
  exact closed_congr [] formula (fun _ => 0) values closed (by simp)

/-- P15: a true result proves the closed formula under every assignment. -/
theorem decideB_sound [DecidableEq α] (formula : LProp α)
    (closed : closedUnderB [] formula = true) (accepted : decideB formula = true)
    (values : Assignment α) : formula.denote values :=
  (decideB_true_iff formula closed values).mp accepted

/-- P16: false is a proof of falsehood, never an inconclusive QE result. -/
theorem decideB_complete [DecidableEq α] (formula : LProp α)
    (closed : closedUnderB [] formula = true) (rejected : decideB formula = false)
    (values : Assignment α) : ¬ formula.denote values := by
  intro holds
  have accepted := (decideB_true_iff formula closed values).mpr holds
  rw [rejected] at accepted
  contradiction

theorem decideB_false_iff [DecidableEq α] (formula : LProp α)
    (closed : closedUnderB [] formula = true) (values : Assignment α) :
    decideB formula = false ↔ ¬ formula.denote values := by
  constructor
  · exact fun rejected => decideB_complete formula closed rejected values
  · intro invalid
    cases h : decideB formula with
    | false => rfl
    | true => exact False.elim (invalid (decideB_sound formula closed h values))

/-- Completeness in the conventional validity-to-acceptance direction as well. -/
theorem decideB_of_valid [DecidableEq α] (formula : LProp α)
    (closed : closedUnderB [] formula = true) (values : Assignment α)
    (valid : formula.denote values) : decideB formula = true :=
  (decideB_true_iff formula closed values).mpr valid

/-- At the exact engineering budget, both logical answers have their full meaning. -/
theorem decideWithBudget_at_Budget [DecidableEq α] (formula : LProp α)
    (closed : closedUnderB [] formula = true) (values : Assignment α) :
    (decideWithBudget formula (Budget formula) = .ok true ↔ formula.denote values) ∧
    (decideWithBudget formula (Budget formula) = .ok false ↔ ¬ formula.denote values) := by
  have computed := budget_sufficient formula (Budget formula) closed (by omega)
  constructor
  · rw [computed]
    simpa only [Except.ok.injEq] using decideB_true_iff formula closed values
  · rw [computed]
    simpa only [Except.ok.injEq] using decideB_false_iff formula closed values

end Gabbro.Grammatik.Invarianten.Elim.Korrekt
