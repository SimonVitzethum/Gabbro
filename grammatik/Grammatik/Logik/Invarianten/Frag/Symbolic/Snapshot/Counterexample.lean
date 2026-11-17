module

public import Grammatik.Logik.Invarianten.Frag.Symbolic.Reduce.Evaluate

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag.Symbolic.Snapshot

/-- Certify a proposed complete valuation on the original quantified VC.
    Inconclusive sampling is never reported as a counterexample. -/
def zeroCounterexample [DecidableEq α] (original : LProp α) :
    Option (PLift (¬ original.denote (fun _ => 0))) :=
  let simplified := Reduce.normalize 8 original
  match Reduce.evaluate simplified.val (fun _ => 0) with
  | .no invalid => some ⟨fun valid => invalid ((simplified.property _).mpr valid)⟩
  | _ => none

theorem zeroCounterexample_sound [DecidableEq α] (original : LProp α)
    (found : (zeroCounterexample original).isSome = true) :
    ¬ original.denote (fun _ => 0) :=
  ((zeroCounterexample original).get found).down

def counterexampleMessage : String :=
  "false VC; certified counterexample: free observations = 0"

/-- The only early logical rejection carries a model of the original negation. -/
def rejectCounterexample [DecidableEq α] (enabled : Bool) (original : LProp α) : Except Frag.Refusal Unit :=
  if enabled then
    match zeroCounterexample original with
    | some _ => .error (.invalid counterexampleMessage)
    | none => .ok ()
  else .ok ()

theorem rejectCounterexample_of_valid [DecidableEq α] (enabled : Bool) (original : LProp α)
    (valid : original.denote (fun _ => 0)) :
    rejectCounterexample enabled original = .ok () := by
  cases enabled with
  | false => rfl
  | true =>
      unfold rejectCounterexample
      cases found : zeroCounterexample original with
      | none => rfl
      | some certificate => exact False.elim (certificate.down valid)

/-- The displayed valuation refutes the original VC, independently of Cooper
    elimination, projection, or the outcome of any resource-limited decision. -/
theorem rejectCounterexample_sound [DecidableEq α] (original : LProp α)
    (claimed : rejectCounterexample true original = .error (.invalid counterexampleMessage)) :
    ¬ original.denote (fun _ => 0) := by
  unfold rejectCounterexample at claimed
  cases found : zeroCounterexample original with
  | none => rw [found] at claimed; cases claimed
  | some certificate => exact certificate.down

end Gabbro.Grammatik.Invarianten.Frag.Symbolic.Snapshot
