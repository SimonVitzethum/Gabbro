module

public import Grammatik.Nebenlaeufigkeit.Async.Verfeinerung
import Lean.Elab.Tactic.Omega

namespace Gabbro.Grammatik.Async

/-- Work left in a single finite straight-line activation, counting entry into
    an await and its child poll separately. This is not a wait/fairness bound. -/
@[expose] public def segmentWork : Direct Value Child → Nat
  | .running rest _ => 2 * rest.length + 1
  | .waiting _ rest _ _ => 2 * rest.length + 2
  | .completed _ | .cancelled => 0

public theorem internal_decreases (model : Model Value Child) (f : AsyncFn)
    {source target : Direct Value Child} {cost : Nat}
    (h : directStep model f source = (.next, target, cost)) :
    segmentWork target < segmentWork source := by
  cases source with
  | running rest frame =>
    cases rest with
    | nil =>
      cases he : model.evaluate f.result frame with
      | mk value work => simp only [directStep, he, Prod.mk.injEq, reduceCtorEq, true_and, false_and] at h
    | cons command rest =>
      cases command with
      | bind name expr bound =>
        cases he : model.evaluate expr frame with
        | mk value work =>
          simp only [directStep, he, Prod.mk.injEq, reduceCtorEq, true_and, false_and] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [segmentWork, List.length_cons]
          omega
      | await name expr boundary =>
        cases he : makeTask model frame expr with
        | mk child work =>
          simp only [directStep, he, Prod.mk.injEq, reduceCtorEq, true_and, false_and] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [segmentWork, List.length_cons]
          omega
  | waiting name rest frame child =>
    cases hp : pollTask model child with
    | mk result payload =>
      cases payload with
      | mk child' work =>
        cases result with
        | pending => simp only [directStep, hp, Prod.mk.injEq, reduceCtorEq, true_and, false_and] at h
        | ready value =>
          simp only [directStep, hp, Prod.mk.injEq, reduceCtorEq, true_and, false_and] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [segmentWork]
          omega
  | completed value => simp only [directStep, Prod.mk.injEq, reduceCtorEq, true_and, false_and] at h
  | cancelled => simp only [directStep, Prod.mk.injEq, reduceCtorEq, true_and, false_and] at h

/-- Each segment/child must discharge its OWN ordinary cost obligation. This
    follows the LogikPflicht pattern: a quantified user duty, no new assumption.
    A uniform step bound is conservative; the segment has finite many steps. -/
public structure PollCostDuty (model : Model Value Child) (f : AsyncFn)
    (states : Direct Value Child → Prop) (bound : Nat) : Prop where
  costBound : ∀ source event target cost, states source →
    directStep model f source = (event, target, cost) → cost ≤ bound
  internalClosed : ∀ source target cost, states source →
    directStep model f source = (.next, target, cost) → states target

public theorem poll_cost_bounded (model : Model Value Child) (f : AsyncFn)
    (states : Direct Value Child → Prop) (bound : Nat)
    (duty : PollCostDuty model f states bound)
    {source target : Direct Value Child} {event : Event Value} {cost : Nat}
    (initial : states source) (run : DirectPoll model f source event target cost) :
    cost ≤ (segmentWork source + 1) * bound := by
  revert initial
  induction run with
  | stop step terminal =>
    intro initial
    exact Nat.le_trans (duty.costBound _ _ _ _ initial step)
      (Nat.le_mul_of_pos_left bound (Nat.succ_pos _))
  | next step rest ih =>
    intro initial
    have restCost := ih (duty.internalClosed _ _ _ initial step)
    have decrease := internal_decreases model f step
    have remainingBound := Nat.mul_le_mul_right bound
      (Nat.succ_le_of_lt decrease)
    have firstBound := duty.costBound _ _ _ _ initial step
    have restBound := Nat.le_trans restCost remainingBound
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- Every individual poll terminates in the finite core, even if the future
    stays Pending forever. This proves no scheduler progress or wait bound. -/
public theorem direct_poll_exists (model : Model Value Child) (f : AsyncFn)
    (source : Direct Value Child) :
    ∃ event target cost, DirectPoll model f source event target cost := by
  cases hs : directStep model f source with
  | mk event payload =>
    cases payload with
    | mk target work =>
      cases event with
      | next =>
        obtain ⟨event, final, cost, run⟩ := direct_poll_exists model f target
        exact ⟨event, final, work + cost, .next hs run⟩
      | pending => exact ⟨.pending, target, work, .stop hs (by intro h; cases h)⟩
      | ready value marks =>
        exact ⟨.ready value marks, target, work, .stop hs (by intro h; cases h)⟩
      | refused => exact ⟨.refused, target, work, .stop hs (by intro h; cases h)⟩
termination_by segmentWork source
decreasing_by exact internal_decreases model f hs

end Gabbro.Grammatik.Async
