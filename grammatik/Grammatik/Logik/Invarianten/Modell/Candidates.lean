module

public import Grammatik.Logik.Invarianten.Korrekt.Decision
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Modell

open Frag Elim Elim.Korrekt

/-- An executable stabilization threshold, evaluated after the remaining variables
    have been reconstructed. Only normalized inequalities need a threshold. -/
def infinityThreshold [DecidableEq α] (name : α) (values : Assignment α) : QF α → Int
  | .atom .lt term =>
      let parts := splitVar name term
      if parts.1 = 1 then -parts.2.denote values - 1
      else if parts.1 = -1 then parts.2.denote values else 0
  | .conj left right | .disj left right =>
      min (infinityThreshold name values left) (infinityThreshold name values right)
  | _ => 0

theorem infinityThreshold_sound [DecidableEq α] (name : α) (body : QF α)
    (unit : UnitCoefficients name body) (values : Assignment α) (x : Int)
    (low : x ≤ infinityThreshold name values body) :
    body.denote (values.bind name x) ↔
      (minusInfinity name body).denote (values.bind name x) := by
  induction body with
  | tru => rfl
  | fls => rfl
  | atom relation term =>
      cases relation with
      | lt =>
          rcases unit with hz | hp | hn
          · simp only [minusInfinity, hz, ↓reduceIte, atom_denote, QF.denote, Relation.denote]
            rw [term_bind name term values x, remainder_bind name term values x,
              hz, Int.zero_mul, Int.zero_add]
          · have bound : x ≤ -(splitVar name term).2.denote values - 1 := by
              simpa [infinityThreshold, hp] using low
            simp only [minusInfinity, hp, show (1 : Int) ≠ 0 by decide, ↓reduceIte,
              truth_denote, decide_eq_true_eq, QF.denote, Relation.denote, term_bind, hp]
            omega
          · have bound : x ≤ (splitVar name term).2.denote values := by
              simpa [infinityThreshold, hn] using low
            simp only [minusInfinity, hn, show (-1 : Int) ≠ 0 by decide, ↓reduceIte,
              truth_denote, decide_eq_true_eq, QF.denote, Relation.denote, term_bind, hn]
            omega
      | dvd k | ndvd k =>
          exact (atom_denote _ term (values.bind name x)).symm
  | conj left right ihLeft ihRight | disj left right ihLeft ihRight =>
      have hl : x ≤ infinityThreshold name values left :=
        le_trans low (min_le_left _ _)
      have hr : x ≤ infinityThreshold name values right :=
        le_trans low (min_le_right _ _)
      simp only [QF.denote, minusInfinity, conj_denote, disj_denote,
        ← ihLeft unit.1 hl, ← ihRight unit.2 hr]

/-- Move a residue representative left by a positive number of whole periods. -/
def witnessBelow (modulus : Nat) (residue threshold : Int) : Int :=
  residue - (modulus : Int) * (max (residue - threshold) 0 + 1)

theorem witnessBelow_spec (modulus : Nat) (positive : 0 < modulus)
    (residue threshold : Int) :
    witnessBelow modulus residue threshold ≤ threshold ∧
      (modulus : Int) ∣ witnessBelow modulus residue threshold - residue := by
  constructor
  · have hp : (1 : Int) ≤ (modulus : Int) := by omega
    have hm := le_max_left (residue - threshold) 0
    have hn := le_max_right (residue - threshold) 0
    have prod := mul_nonneg (show 0 ≤ (modulus : Int) - 1 by omega)
      (show 0 ≤ max (residue - threshold) 0 + 1 by omega)
    unfold witnessBelow
    nlinarith
  · refine ⟨-(max (residue - threshold) 0 + 1), ?_⟩
    unfold witnessBelow
    ring

/-- Every infinity branch has a concrete representative. Boundary candidates are
    already concrete. The order agrees with Cooper's projection and is stable. -/
def normalizedCandidates [DecidableEq α] (name : α) (plan : CooperStep α)
    (values : Assignment α) : List Int :=
  let residues := List.range plan.modulus
  let below := residues.map fun j => witnessBelow plan.modulus ((j + 1 : Nat) : Int)
    (infinityThreshold name values plan.body)
  let above := plan.boundaries.flatMap fun boundary =>
    residues.map fun j => boundary.denote values + ((j + 1 : Nat) : Int)
  below ++ above

theorem normalizedCandidates_complete [DecidableEq α] (name : α) (body : QF α)
    (values : Assignment α) (holds : (eliminateOne name body).denote values) :
    ∃ y ∈ normalizedCandidates name (prepare name body) values,
      (normalize name body).denote (values.bind name y) := by
  let normal := normalize name body
  have unit := normalize_unit name body
  have existsNormal : ∃ y : Int, normal.denote (values.bind name y) :=
    (normalize_exists name body values).mpr ((eliminateOne_denote name body values).mp holds)
  rcases (cooper_cases name normal unit values).mp existsNormal with
    ⟨j, hj, infinity⟩ | ⟨boundary, member, j, hj, valid⟩
  · let y := witnessBelow (period name normal) ((j + 1 : Nat) : Int)
      (infinityThreshold name values normal)
    have spec := witnessBelow_spec (period name normal) (period_pos name normal)
      ((j + 1 : Nat) : Int) (infinityThreshold name values normal)
    refine ⟨y, ?_, ?_⟩
    · apply List.mem_append.mpr
      apply Or.inl
      exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
    · apply (infinityThreshold_sound name normal unit values y spec.1).mpr
      exact (minusInfinity_periodic name normal values (period name normal)
        (dvd_refl _) y ((j + 1 : Nat) : Int) spec.2).mpr infinity
  · refine ⟨boundary.denote values + ((j + 1 : Nat) : Int), ?_, valid⟩
    apply List.mem_append.mpr
    apply Or.inr
    apply List.mem_flatMap.mpr
    exact ⟨boundary, member, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩⟩

/-- A trace row retains the source and the exact normalization/projection plan.
    Callers construct rows with `recordStep`; no semantic certificate is supplied. -/
structure ReconstructionStep (α : Type) where
  name : α
  source : QF α
  plan : CooperStep α

def recordStep [DecidableEq α] (name : α) (source : QF α) : ReconstructionStep α :=
  { name := name
    source := source
    plan := prepare name source }

/-- Search only the finite Cooper candidates and undo the recorded scaling. -/
def recoverOne [DecidableEq α] (row : ReconstructionStep α) (values : Assignment α) : Option Int :=
  ((normalizedCandidates row.name row.plan values).find?
    (fun y => row.plan.body.eval (values.bind row.name y))).map
      (fun y => y / (row.plan.multiple : Int))

theorem recoverOne_sound [DecidableEq α] (name : α) (body : QF α)
    (values : Assignment α) (x : Int)
    (success : recoverOne (recordStep name body) values = some x) :
    body.denote (values.bind name x) := by
  change ((normalizedCandidates name (prepare name body) values).find?
    (fun y => (normalize name body).eval (values.bind name y))).map
      (fun y => y / (coefficientLcm name body : Int)) = some x at success
  cases selected : (normalizedCandidates name (prepare name body) values).find?
      (fun y => (normalize name body).eval (values.bind name y)) with
  | none => simp only [selected, Option.map_none, reduceCtorEq] at success
  | some y =>
      have accepted : (normalize name body).eval (values.bind name y) = true :=
        List.find?_some (p := fun z => (normalize name body).eval (values.bind name z)) selected
      have valid := (qf_eval (normalize name body) (values.bind name y)).mp
        accepted
      obtain ⟨original, equation, holds⟩ := (normalize_denote name body values y).mp valid
      have nonzero : (coefficientLcm name body : Int) ≠ 0 := by
        have := coefficientLcm_pos name body
        omega
      have result : y / (coefficientLcm name body : Int) = x := by
        simpa only [selected, Option.map_some, Option.some.injEq] using success
      rw [equation, Int.mul_ediv_cancel_left _ nonzero] at result
      simpa only [result] using holds

theorem recoverOne_complete [DecidableEq α] (name : α) (body : QF α)
    (values : Assignment α) (holds : (eliminateOne name body).denote values) :
    ∃ x : Int, recoverOne (recordStep name body) values = some x := by
  obtain ⟨y, member, valid⟩ := normalizedCandidates_complete name body values holds
  have accepted := (qf_eval (normalize name body) (values.bind name y)).mpr valid
  cases selected : (normalizedCandidates name (prepare name body) values).find?
      (fun z => (normalize name body).eval (values.bind name z)) with
  | none =>
      have absent := (List.find?_eq_none.mp selected) y member
      exact False.elim (absent accepted)
  | some z =>
      refine ⟨z / (coefficientLcm name body : Int), ?_⟩
      change ((normalizedCandidates name (prepare name body) values).find?
        (fun y => (normalize name body).eval (values.bind name y))).map
          (fun y => y / (coefficientLcm name body : Int)) = _
      rw [selected]
      rfl

end Gabbro.Grammatik.Invarianten.Modell
