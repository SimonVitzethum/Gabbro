module

public import Grammatik.Nebenlaeufigkeit.Async.Executor.Ring

namespace Gabbro.Grammatik.Async.Executor

/-- Specification at atomic linearisation points. Claim returns the old bit
    and clears it; a failed compare-exchange on false has the same result.
    Connecting these points to canonical G/GX exchange remains a separate
    library obligation, not a new assumption about the hardware. -/
public inductive WakeStep : Bool → Bool → Bool → Prop where
  | notify (before : Bool) : WakeStep before true false
  | claim (before : Bool) : WakeStep before false before

/-- Third index records whether any claim in this finite trace received a
    notification. It asserts neither scheduling nor eventual receipt. -/
public inductive WakeRun : Bool → Bool → Bool → Prop where
  | refl (pending : Bool) : WakeRun pending pending false
  | step (first : WakeStep before middle received)
      (rest : WakeRun middle after later) : WakeRun before after (received || later)

public theorem wakeStep_retains (step : WakeStep before after received) (pending : before = true) :
    after = true ∨ received = true := by
  cases step with
  | notify => exact Or.inl rfl
  | claim => exact Or.inr pending

public theorem no_phantom_receipt (step : WakeStep false after received) : received = false := by
  cases step <;> rfl

/-- A previously posted notification either remains latched or was actually
    claimed. Queue-full scans perform no claim, so cannot consume a wake.
    Both wake-before-claim and wake-after-claim are covered by all traces. -/
public theorem wake_not_lost (run : WakeRun before after received) (pending : before = true) :
    after = true ∨ received = true := by
  revert pending
  induction run with
  | refl => intro pending; exact Or.inl pending
  | step first rest ih =>
    intro pending
    rcases wakeStep_retains first pending with remains | claimed
    · rcases ih remains with still | later
      · exact Or.inl still
      · exact Or.inr (by simp only [later, Bool.or_true])
    · exact Or.inr (by simp only [claimed, Bool.true_or])

/-- Two explicit WakeRun traces: notify/claim/claim receives at least once
    and ends clear; claim/notify receives at least once and ends latched.
    WakeRun's Boolean records any receipt, not the number of receipts. -/
public theorem notification_claim_traces_zeuge :
    WakeRun false false true ∧ WakeRun true true true := by
  constructor
  · exact .step (.notify false) (.step (.claim true) (.step (.claim false) (.refl false)))
  · exact .step (.claim true) (.step (.notify false) (.refl true))

end Gabbro.Grammatik.Async.Executor
