module

public import Grammatik.Logik.Invarianten.VC.Formula

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag.Symbolic.Snapshot

open Elim Elim.Korrekt

/-- Reuse the already eliminated VC, but certify the proposed valuation on
    the original quantified formula. Failure to certify is not a counterexample. -/
def zeroCounterexample [DecidableEq α] (original : LProp α) (reduced : QF α)
    (correct : ∀ values, reduced.denote values ↔ original.denote values) :
    Option (PLift (¬ original.denote (fun _ => 0))) :=
  if checked : reduced.eval (fun _ => 0) = false then
    some ⟨fun valid => by
      have evaluated := (qf_eval reduced (fun _ => 0)).mpr ((correct _).mpr valid)
      rw [checked] at evaluated
      cases evaluated⟩
  else none

theorem zeroCounterexample_sound [DecidableEq α] (original : LProp α) (reduced : QF α)
    (correct : ∀ values, reduced.denote values ↔ original.denote values)
    (found : (zeroCounterexample original reduced correct).isSome = true) :
    ¬ original.denote (fun _ => 0) :=
  ((zeroCounterexample original reduced correct).get found).down

theorem zeroCounterexample_complete [DecidableEq α] (original : LProp α) (reduced : QF α)
    (correct : ∀ values, reduced.denote values ↔ original.denote values)
    (invalid : ¬ original.denote (fun _ => 0)) :
    (zeroCounterexample original reduced correct).isSome = true := by
  cases evaluated : reduced.eval (fun _ => 0) with
  | false => simp only [zeroCounterexample, evaluated, ↓reduceDIte, Option.isSome_some]
  | true => exact False.elim (invalid ((correct _).mp ((qf_eval reduced _).mp evaluated)))

def counterexampleMessage : String :=
  "false VC; certified counterexample: free observations = 0"

def refusal [DecidableEq α] (original : LProp α) (reduced : QF α)
    (correct : ∀ values, reduced.denote values ↔ original.denote values) (fallback : String) : Frag.Refusal :=
  match zeroCounterexample original reduced correct with
  | some _ => .invalid counterexampleMessage
  | none => .unsupported fallback

/-- The diagnostic certifies the original negated VC at the displayed complete
    valuation; a model of an unrelated or merely projected formula is insufficient. -/
theorem refusal_counterexample_sound [DecidableEq α] (original : LProp α) (reduced : QF α)
    (correct : ∀ values, reduced.denote values ↔ original.denote values) (fallback : String)
    (claimed : refusal original reduced correct fallback = .invalid counterexampleMessage) :
    ¬ original.denote (fun _ => 0) := by
  unfold refusal at claimed
  cases found : zeroCounterexample original reduced correct with
  | none => rw [found] at claimed; cases claimed
  | some certificate => exact certificate.down

end Gabbro.Grammatik.Invarianten.Frag.Symbolic.Snapshot
