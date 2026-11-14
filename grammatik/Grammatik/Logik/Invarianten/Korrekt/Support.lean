module

public import Grammatik.Logik.Invarianten.Frag.Support
public import Grammatik.Logik.Invarianten.Elim.Linear

public section

namespace Gabbro.Grammatik.Invarianten.Frag

theorem termClosedB_iff [DecidableEq α] (bound : List α) (term : LTerm α) :
    Elim.termClosedB bound term = true ↔ ∀ key ∈ term.variables, key ∈ bound := by
  induction term with
  | var name => simp [Elim.termClosedB, LTerm.variables]
  | konst value => simp [Elim.termClosedB, LTerm.variables]
  | add left right ihLeft ihRight | sub left right ihLeft ihRight =>
      simp only [Elim.termClosedB, Bool.and_eq_true, LTerm.variables,
        List.forall_mem_append, ihLeft, ihRight]
  | scale coefficient term ih => exact ih

theorem closedUnderB_iff [DecidableEq α] (bound : List α) (formula : LProp α) :
    Elim.closedUnderB bound formula = true ↔ ∀ key ∈ formula.freeVariables, key ∈ bound := by
  induction formula generalizing bound with
  | tru => simp [Elim.closedUnderB, LProp.freeVariables]
  | fls => simp [Elim.closedUnderB, LProp.freeVariables]
  | le left right | lt left right | eq left right =>
      simp only [Elim.closedUnderB, Bool.and_eq_true, LProp.freeVariables,
        List.forall_mem_append, termClosedB_iff]
  | dvd divisor term => exact termClosedB_iff bound term
  | not body ih => exact ih bound
  | and left right ihLeft ihRight | or left right ihLeft ihRight
  | imp left right ihLeft ihRight =>
      simp only [Elim.closedUnderB, Bool.and_eq_true, LProp.freeVariables,
        List.forall_mem_append, ihLeft, ihRight]
  | ex name body ih | all name body ih =>
      rw [Elim.closedUnderB, ih]
      change (∀ key ∈ body.freeVariables, key ∈ name :: bound) ↔
        ∀ key ∈ body.freeVariables.filter (fun key => decide (key ≠ name)), key ∈ bound
      constructor
      · intro covered key member
        obtain ⟨present, different⟩ := List.mem_filter.mp member
        exact (List.mem_cons.mp (covered key present)).resolve_left (of_decide_eq_true different)
      · intro covered key member
        by_cases same : key = name
        · exact List.mem_cons.mpr (Or.inl same)
        · exact List.mem_cons.mpr (Or.inr
            (covered key (List.mem_filter.mpr ⟨member, by simp [same]⟩)))

theorem LProp.keys_supported [DecidableEq α] (formula : LProp α) :
    Elim.closedUnderB formula.keys formula = true :=
  (closedUnderB_iff formula.keys formula).mpr
    (fun key member => (formula.mem_keys key).mpr member)

end Gabbro.Grammatik.Invarianten.Frag
