module

public import Grammatik.Logik.Invarianten.Frag.Symbolic.Snapshot.Counterexample
public import Grammatik.Logik.Invarianten.Modell.World

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag.Symbolic.Snapshot

open Elim Elim.Korrekt Modell

/-- Success of the finite Cooper run certifies the input formula itself. -/
theorem metered_sound [DecidableEq α] (body : LProp α) (fuel : Nat)
    (accepted : decideWithBudget body fuel = .ok true) : body.denote (fun _ => 0) := by
  unfold decideWithBudget at accepted
  split at accepted
  · cases checked : (compile body).run { limit := some fuel } with
    | error cause => simp only [checked, bind, Except.bind, reduceCtorEq] at accepted
    | ok result =>
        obtain ⟨formula, meter⟩ := result
        have evaluated : formula.eval (fun _ => 0) = true := by
          simpa only [checked, bind, Except.bind, pure, Except.pure, Except.ok.injEq] using accepted
        exact (compile_denote body _ meter formula checked _).mp ((qf_eval _ _).mp evaluated)
  · cases accepted

/-- Close the original support before simplifying. Snapshot aliases and stored
    values are substituted before the single metered Cooper stage. -/
def prepared [DecidableEq α] (original : LProp α) :=
  Reduce.normalize 8 (universalClosure original.keys original)

theorem closure_of_valid [DecidableEq α] (names : List α) (body : LProp α)
    (valid : ∀ values, body.denote values) : ∀ values, (universalClosure names body).denote values := by
  induction names with
  | nil => exact valid
  | cons name names ih => exact fun values value => ih (values.bind name value)

theorem prepared_of_valid [DecidableEq α] (original : LProp α)
    (valid : ∀ values, original.denote values) : ∀ values, (prepared original).val.denote values :=
  fun values => ((prepared original).property values).mpr (closure_of_valid original.keys original valid values)

theorem prepared_sound [DecidableEq α] (original : LProp α)
    (valid : (prepared original).val.denote (fun _ => 0)) : ∀ values, original.denote values := by
  have closed := (prepared original).property (fun _ => 0) |>.mp valid
  intro values
  apply universalClosure_specialize original.keys original values
  apply (closed_congr [] (universalClosure original.keys original) (fun _ => 0) values
    (universalClosure_closed original) (fun _ member => nomatch member)).mp closed

/-- Refusal on an exhausted work allowance is never a false-VC diagnostic.
    Simplification and evaluation carry proofs; neither enumerates integer ranges. -/
def decide [DecidableEq α] (original : LProp α) (fuel : Nat) (fallback : String) :
    Except Frag.Refusal (PLift (∀ values, original.denote values)) := do
  let _ ← rejectCounterexample true original
  let simplified := prepared original
  match Reduce.evaluate simplified.val (fun _ => 0) with
  | .yes valid => return ⟨prepared_sound original valid⟩
  | _ =>
      match checked : decideWithBudget simplified.val fuel with
      | .ok true => return ⟨prepared_sound original (metered_sound _ _ checked)⟩
      | .ok false => .error (.unsupported fallback)
      | .error reason => .error (.unsupported ("outside the decidable fragment: " ++ reason.message))

/-- A normalized true formula needs no elimination, including in proof fixtures. -/
theorem decide_of_prepared_true [DecidableEq α] (original : LProp α) (fuel : Nat) (fallback : String)
    (shape : (prepared original).val = .tru) :
    (decide original fuel fallback).toOption.isSome = true := by
  have valid := prepared_sound original (by rw [shape]; trivial)
  unfold decide
  rw [rejectCounterexample_of_valid true original (valid (fun _ => 0))]
  dsimp only [bind, Except.bind]
  obtain ⟨proof, evaluated⟩ := Reduce.evaluate_true (prepared original).val (fun _ => 0) shape
  rw [evaluated]
  rfl

end Gabbro.Grammatik.Invarianten.Frag.Symbolic.Snapshot
