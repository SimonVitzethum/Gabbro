module

public import Grammatik.Logik.Invarianten.Korrekt.Period
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

namespace Gabbro.Grammatik.Invarianten.Elim.Korrekt

open Frag

/-- If a downward step crosses no lower threshold, every true atom remains true.
    This one-way statement is exactly what positive NNF conjunctions/disjunctions
    require; upper bounds can only become easier when moving to the left. -/
theorem descend [DecidableEq α] (name : α) (body : QF α)
    (unit : UnitCoefficients name body) (values : Assignment α)
    (delta : Nat) (covered : period name body ∣ delta) (x : Int)
    (holds : body.denote (values.bind name x))
    (noCross : ∀ boundary ∈ lowerBounds name body,
      ¬ (x - (delta : Int) ≤ boundary.denote values ∧ boundary.denote values < x)) :
    body.denote (values.bind name (x - (delta : Int))) := by
  induction body with
  | tru => trivial
  | fls => exact holds
  | atom relation term =>
      cases relation with
      | lt =>
          simp only [QF.denote, Relation.denote, term_bind] at holds ⊢
          rcases unit with hz | hp | hn
          · simp_all
          · simp only [hp, one_mul] at holds ⊢
            omega
          · have hb : (splitVar name term).2 ∈ lowerBounds name (.atom .lt term) := by
              simp [lowerBounds, hn]
            have hc := noCross _ hb
            simp only [hn, neg_one_mul] at holds ⊢
            omega
      | dvd k =>
          exact (divisibility_periodic name term values k delta x (x - (delta : Int))
            covered ⟨1, by ring⟩).mp holds
      | ndvd k =>
          exact (not_congr (divisibility_periodic name term values k delta x (x - (delta : Int))
            covered ⟨1, by ring⟩)).mp holds
  | conj left right ihLeft ihRight =>
      have hl : period name left ∣ delta :=
        (Int.natAbs_dvd_lcm_left (period name left : Int) (period name right : Int)).trans covered
      have hr : period name right ∣ delta :=
        (Int.natAbs_dvd_lcm_right (period name left : Int) (period name right : Int)).trans covered
      exact ⟨ihLeft unit.1 hl holds.1 (fun b hb => noCross b (List.mem_append.mpr (Or.inl hb))),
        ihRight unit.2 hr holds.2 (fun b hb => noCross b (List.mem_append.mpr (Or.inr hb)))⟩
  | disj left right ihLeft ihRight =>
      have hl : period name left ∣ delta :=
        (Int.natAbs_dvd_lcm_left (period name left : Int) (period name right : Int)).trans covered
      have hr : period name right ∣ delta :=
        (Int.natAbs_dvd_lcm_right (period name left : Int) (period name right : Int)).trans covered
      rcases holds with hlBody | hrBody
      · exact Or.inl (ihLeft unit.1 hl hlBody
          (fun b hb => noCross b (List.mem_append.mpr (Or.inl hb))))
      · exact Or.inr (ihRight unit.2 hr hrBody
          (fun b hb => noCross b (List.mem_append.mpr (Or.inr hb))))

/-- A witness whose predecessor by one period is false is within one period
    above an actual boundary of this formula. -/
theorem boundary_of_blocked [DecidableEq α] (name : α) (body : QF α)
    (unit : UnitCoefficients name body) (values : Assignment α)
    (delta : Nat) (covered : period name body ∣ delta) (x : Int)
    (holds : body.denote (values.bind name x))
    (blocked : ¬ body.denote (values.bind name (x - (delta : Int)))) :
    ∃ boundary ∈ lowerBounds name body,
      x - (delta : Int) ≤ boundary.denote values ∧ boundary.denote values < x := by
  classical
  by_contra absent
  apply blocked
  apply descend name body unit values delta covered x holds
  intro boundary member crossing
  exact absent ⟨boundary, member, crossing⟩

/-- Along a residue class, either all downward steps remain witnesses or the
    least failed step leaves a witness with a false predecessor. This avoids an
    unjustified least element of an integer set unbounded below. -/
theorem witness_descent [DecidableEq α] (name : α) (body : QF α)
    (values : Assignment α) (delta : Nat) (x : Int)
    (holds : body.denote (values.bind name x)) :
    (∀ k : Nat, body.denote (values.bind name (x - (k : Int) * (delta : Int)))) ∨
      ∃ y : Int, body.denote (values.bind name y) ∧
        ¬ body.denote (values.bind name (y - (delta : Int))) := by
  classical
  by_cases allSteps : ∀ k : Nat,
      body.denote (values.bind name (x - (k : Int) * (delta : Int)))
  · exact Or.inl allSteps
  · have failure : ∃ k : Nat,
        ¬ body.denote (values.bind name (x - ((k + 1 : Nat) : Int) * (delta : Int))) := by
      by_contra absent
      apply allSteps
      intro k
      cases k with
      | zero => simpa using holds
      | succ k =>
          by_contra hk
          exact absent ⟨k, hk⟩
    let k := Nat.find failure
    have failed := Nat.find_spec failure
    have prior : body.denote (values.bind name (x - (k : Int) * (delta : Int))) := by
      cases hk : k with
      | zero => simpa [hk] using holds
      | succ n =>
          have least := Nat.find_min failure (show n < Nat.find failure by change n < k; omega)
          by_contra h
          apply least
          simpa only [hk] using h
    refine Or.inr ⟨x - (k : Int) * (delta : Int), prior, ?_⟩
    have samePoint : x - (k : Int) * (delta : Int) - (delta : Int) =
        x - ((k + 1 : Nat) : Int) * (delta : Int) := by
      push_cast
      ring
    rw [samePoint]
    exact failed

/-- The finite Cooper disjunction, stated independently of syntax construction.
    Indices j are zero-based in lists and denote the mathematical residue j+1. -/
theorem cooper_cases [DecidableEq α] (name : α) (body : QF α)
    (unit : UnitCoefficients name body) (values : Assignment α) :
    (∃ x : Int, body.denote (values.bind name x)) ↔
      (∃ j : Nat, j < period name body ∧
        (minusInfinity name body).denote (values.bind name ((j + 1 : Nat) : Int))) ∨
      (∃ boundary ∈ lowerBounds name body, ∃ j : Nat, j < period name body ∧
        body.denote (values.bind name (boundary.denote values + ((j + 1 : Nat) : Int)))) := by
  classical
  let delta := period name body
  have hp : 0 < delta := period_pos name body
  have hp' : (0 : Int) < (delta : Int) := by omega
  obtain ⟨threshold, stable⟩ := minusInfinity_eventually name body unit values
  constructor
  · rintro ⟨x, hx⟩
    rcases witness_descent name body values delta x hx with allSteps | ⟨y, hy, blocked⟩
    · obtain ⟨j, hj, congruent⟩ := residue_exists delta hp x
      let k := (max (x - threshold) 0 + 1).toNat
      have hk : (k : Int) = max (x - threshold) 0 + 1 := by
        exact Int.toNat_of_nonneg (by omega)
      have low : x - (k : Int) * (delta : Int) ≤ threshold := by
        have := le_max_left (x - threshold) 0
        rw [hk]
        have hprod := mul_nonneg (show 0 ≤ (delta : Int) - 1 by omega)
          (show 0 ≤ max (x - threshold) 0 + 1 by omega)
        nlinarith
      have atLow := (stable _ low).mp (allSteps k)
      have sameClass : (delta : Int) ∣ ((j + 1 : Nat) : Int) -
          (x - (k : Int) * (delta : Int)) := by
        convert Int.dvd_add congruent (Int.dvd_mul_left (k : Int) (delta : Int)) using 1 <;> ring
      exact Or.inl ⟨j, hj, (minusInfinity_periodic name body values delta
        (dvd_refl delta) _ _ sameClass).mpr atLow⟩
    · obtain ⟨boundary, member, lower, upper⟩ :=
        boundary_of_blocked name body unit values delta (dvd_refl delta) y hy blocked
      let j := (y - boundary.denote values - 1).toNat
      have hj : (j : Int) = y - boundary.denote values - 1 :=
        Int.toNat_of_nonneg (by omega)
      have hjlt : j < delta := by omega
      have hyEq : boundary.denote values + ((j + 1 : Nat) : Int) = y := by omega
      exact Or.inr ⟨boundary, member, j, hjlt, by simpa only [hyEq] using hy⟩
  · rintro (⟨j, hj, infinity⟩ | ⟨boundary, member, j, hj, witness⟩)
    · obtain ⟨x, low, sameClass⟩ := residue_below delta hp ((j + 1 : Nat) : Int) threshold
      have infinityAt := (minusInfinity_periodic name body values delta
        (dvd_refl delta) _ _ sameClass).mpr infinity
      exact ⟨x, (stable x low).mpr infinityAt⟩
    · exact ⟨boundary.denote values + ((j + 1 : Nat) : Int), witness⟩

end Gabbro.Grammatik.Invarianten.Elim.Korrekt
