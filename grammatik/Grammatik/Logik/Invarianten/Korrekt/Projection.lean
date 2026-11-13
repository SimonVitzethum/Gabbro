module

public import Grammatik.Logik.Invarianten.Korrekt.Boundary

public section

namespace Gabbro.Grammatik.Invarianten.Elim.Korrekt

open Frag

theorem anyOf_denote (formulas : List (QF α)) (values : Assignment α) :
    (anyOf formulas).denote values ↔ ∃ body ∈ formulas, body.denote values := by
  induction formulas with
  | nil => simp [anyOf, QF.denote]
  | cons head tail ih =>
      simp only [anyOf, List.foldr_cons, disj_denote]
      change (head.denote values ∨ (anyOf tail).denote values) ↔ _
      rw [ih]
      simp only [List.mem_cons]
      constructor
      · rintro (h | ⟨body, member, h⟩)
        · exact ⟨head, Or.inl rfl, h⟩
        · exact ⟨body, Or.inr member, h⟩
      · rintro ⟨body, rfl | member, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨body, member, h⟩

theorem anyOf_map_denote (items : List β) (formulas : β → QF α) (values : Assignment α) :
    (anyOf (items.map formulas)).denote values ↔
      ∃ item ∈ items, (formulas item).denote values := by
  rw [anyOf_denote]
  simp only [List.mem_map]
  constructor
  · rintro ⟨body, ⟨item, member, rfl⟩, h⟩
    exact ⟨item, member, h⟩
  · rintro ⟨item, member, h⟩
    exact ⟨formulas item, ⟨item, member, rfl⟩, h⟩

/-- The actual finite syntax emitted by `project` realizes Cooper's disjunction.
    Both directions refer to the implementation, with no supplied step certificate. -/
theorem project_denote [DecidableEq α] (name : α) (body : QF α)
    (unit : UnitCoefficients name body) (values : Assignment α) :
    (project name
      { multiple := 1
        body := body
        modulus := period name body
        boundaries := lowerBounds name body
        infinity := minusInfinity name body }).denote values ↔
      ∃ x : Int, body.denote (values.bind name x) := by
  rw [cooper_cases name body unit values]
  simp only [project, disj_denote, anyOf_map_denote, List.mem_range,
    subst_denote, LTerm.denote, addTerm_denote, Int.natCast_add, Int.natCast_one]

/-- One complete elimination step, including coefficient normalization and its
    image divisibility constraint. This is the sole QE fact used by the compiler. -/
theorem eliminateOne_denote [DecidableEq α] (name : α) (body : QF α)
    (values : Assignment α) :
    (eliminateOne name body).denote values ↔
      ∃ x : Int, body.denote (values.bind name x) := by
  have hp := project_denote name (normalize name body) (normalize_unit name body) values
  have hn := normalize_exists name body values
  exact hp.trans hn

end Gabbro.Grammatik.Invarianten.Elim.Korrekt
