module

public import Grammatik.Logik.Invarianten.Modell.Candidates

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Modell

open Frag Elim Elim.Korrekt

/-- Explicit closures avoid an implicit enumeration of a variable type. Repeated
    names retain the named-shadowing semantics of the source fragment. -/
def universalClosure (names : List α) (body : LProp α) : LProp α :=
  names.foldr LProp.all body

def existentialClosure (names : List α) (body : LProp α) : LProp α :=
  names.foldr LProp.ex body

/-- Rows are stored outermost first, the reverse of elimination order. Each row
    keeps the plan used for that actual projection, including the normalized body. -/
structure EliminationTrace (α : Type) where
  result : QF α
  rows : List (ReconstructionStep α)

def eliminationTrace [DecidableEq α] : List α → QF α → EliminationTrace α
  | [], body =>
      { result := body
        rows := [] }
  | name :: names, body =>
      let inner := eliminationTrace names body
      let row := recordStep name inner.result
      { result := project name row.plan
        rows := row :: inner.rows }

/-- The final check also protects users of manually assembled traces. This is
    evaluation of quantifier-free syntax, never an oracle for quantified formulas. -/
def reconstruct [DecidableEq α] (body : QF α) :
    List (ReconstructionStep α) → Assignment α → Option (Assignment α)
  | [], values => if body.eval values then some values else none
  | row :: rows, values => do
      let value ← recoverOne row values
      reconstruct body rows (values.bind row.name value)

theorem reconstruct_sound [DecidableEq α] (body : QF α)
    (rows : List (ReconstructionStep α)) (values result : Assignment α)
    (success : reconstruct body rows values = some result) : body.denote result := by
  induction rows generalizing values with
  | nil =>
      simp only [reconstruct] at success
      split at success
      · rename_i accepted
        have valid := (qf_eval body values).mp accepted
        cases success
        exact valid
      · contradiction
  | cons row rows ih =>
      change (recoverOne row values).bind
        (fun value => reconstruct body rows (values.bind row.name value)) = some result at success
      cases selected : recoverOne row values with
      | none => simp only [selected, Option.bind_none, reduceCtorEq] at success
      | some value =>
          apply ih (values.bind row.name value)
          simpa only [selected, Option.bind_some] using success

/-- Generic replay completeness uses the original projection at every row.
    No search radius or fuel premise is needed. -/
theorem reconstruct_complete [DecidableEq α] (names : List α) (body : QF α)
    (values : Assignment α) (holds : (eliminationTrace names body).result.denote values) :
    ∃ result : Assignment α,
      reconstruct body (eliminationTrace names body).rows values = some result := by
  induction names generalizing values with
  | nil =>
      refine ⟨values, ?_⟩
      have evaluated := (qf_eval body values).mpr holds
      simp only [eliminationTrace, reconstruct, evaluated, ↓reduceIte]
  | cons name names ih =>
      have projected : (eliminateOne name (eliminationTrace names body).result).denote values :=
        holds
      obtain ⟨value, selected⟩ := recoverOne_complete name _ values projected
      have inner := recoverOne_sound name (eliminationTrace names body).result values value selected
      obtain ⟨result, replayed⟩ := ih (values.bind name value) inner
      refine ⟨result, ?_⟩
      change (recoverOne (recordStep name (eliminationTrace names body).result) values >>=
        fun x => reconstruct body (eliminationTrace names body).rows (values.bind name x)) = _
      rw [selected]
      exact replayed

theorem eliminationTrace_denote [DecidableEq α] (names : List α) (body : QF α)
    (formula : LProp α) (equivalent : ∀ values, body.denote values ↔ formula.denote values)
    (values : Assignment α) :
    (eliminationTrace names body).result.denote values ↔
      (existentialClosure names formula).denote values := by
  induction names generalizing values with
  | nil => exact equivalent values
  | cons name names ih =>
      change (eliminateOne name (eliminationTrace names body).result).denote values ↔
        ∃ value : Int, (existentialClosure names formula).denote (values.bind name value)
      rw [eliminateOne_denote]
      exact exists_congr (fun value => ih (values.bind name value))

theorem closure_negation [DecidableEq α] (names : List α) (formula : LProp α)
    (values : Assignment α) :
    (existentialClosure names (.not formula)).denote values ↔
      ¬ (universalClosure names formula).denote values := by
  classical
  induction names generalizing values with
  | nil => rfl
  | cons name names ih =>
      change (∃ value : Int,
        (existentialClosure names (.not formula)).denote (values.bind name value)) ↔
          ¬ ∀ value : Int, (universalClosure names formula).denote (values.bind name value)
      simp only [ih, not_forall]

/-- A total executable counterexample extractor. Internal quantifiers in the
    matrix are decided by P12–P16; the explicit outer variables are reconstructed
    from the retained Cooper trace. The environment of any unlisted name is zero. -/
def counterexample [DecidableEq α] (names : List α) (formula : LProp α) :
    Option (Assignment α) :=
  let body := (elimination (.not formula)).1
  let trace := eliminationTrace names body
  reconstruct body trace.rows (fun _ => 0)

/-- Replay finishes from the semantic theorem, without reducing the compiled
    matrix in the kernel. This also keeps quantified fixtures cheap. -/
theorem reconstruct_nil_of_denote [DecidableEq α] (body : QF α)
    (values : Assignment α) (holds : body.denote values) :
    reconstruct body [] values = some values := by
  have accepted := (qf_eval body values).mpr holds
  simp only [reconstruct, accepted, ↓reduceIte]

theorem counterexample_nil_of_false [DecidableEq α] (formula : LProp α)
    (invalid : ¬ formula.denote (fun _ => 0)) :
    counterexample [] formula = some (fun _ => 0) := by
  apply reconstruct_nil_of_denote
  exact (elimination_denote (.not formula) (fun _ => 0)).mpr invalid

/-- An exact one-variable replay needs only the finite candidate choice. Its
    generic soundness theorem supplies the final matrix check. -/
theorem counterexample_single_of_recovered [DecidableEq α] (name : α)
    (formula : LProp α) (value : Int)
    (selected : recoverOne (recordStep name (elimination (.not formula)).1)
      (fun _ => 0) = some value) :
    counterexample [name] formula = some (Assignment.bind (fun _ => 0) name value) := by
  change (recoverOne (recordStep name (elimination (.not formula)).1) (fun _ => 0)).bind
    (fun x => reconstruct (elimination (.not formula)).1 []
      (Assignment.bind (fun _ => 0) name x)) = _
  rw [selected, Option.bind_some]
  apply reconstruct_nil_of_denote
  exact recoverOne_sound name (elimination (.not formula)).1 (fun _ => 0) value selected

theorem counterexample_sound [DecidableEq α] (names : List α) (formula : LProp α)
    (values : Assignment α) (success : counterexample names formula = some values) :
    ¬ formula.denote values :=
  (elimination_denote (.not formula) values).mp
    (reconstruct_sound _ _ _ values success)

/-- A false universal decision always returns an assignment. Closedness is not
    needed here: both decision and reconstruction use zero for unlisted names. -/
theorem counterexample_complete [DecidableEq α] (names : List α) (formula : LProp α)
    (rejected : decideB (universalClosure names formula) = false) :
    ∃ values : Assignment α, counterexample names formula = some values := by
  have invalid : ¬ (universalClosure names formula).denote (fun _ => 0) := by
    intro valid
    have evaluated := (qf_eval (elimination (universalClosure names formula)).1
      (fun _ => 0)).mpr ((elimination_denote _ _).mpr valid)
    change decideB (universalClosure names formula) = true at evaluated
    rw [rejected] at evaluated
    contradiction
  apply reconstruct_complete names (elimination (.not formula)).1 (fun _ => 0)
  apply (eliminationTrace_denote names (elimination (.not formula)).1 (.not formula)
    (fun values => elimination_denote (.not formula) values) (fun _ => 0)).mpr
  exact (closure_negation names formula (fun _ => 0)).mpr invalid

theorem counterexample_of_exists [DecidableEq α] (names : List α) (formula : LProp α)
    (accepted : decideB (existentialClosure names (.not formula)) = true) :
    ∃ values : Assignment α, counterexample names formula = some values := by
  have valid := (elimination_denote (existentialClosure names (.not formula)) (fun _ => 0)).mp
    ((qf_eval _ _).mp accepted)
  apply reconstruct_complete names (elimination (.not formula)).1 (fun _ => 0)
  exact (eliminationTrace_denote names (elimination (.not formula)).1 (.not formula)
    (fun values => elimination_denote (.not formula) values) (fun _ => 0)).mpr valid

end Gabbro.Grammatik.Invarianten.Modell
