module

public import Grammatik.Nebenlaeufigkeit.Async.Verfeinerung
import Lean.Elab.Tactic.Omega

namespace Gabbro.Grammatik.Async

/-- Internal activation work, independently of changes to the world. -/
@[expose] public def segmentWork : Direct Value Child → Nat
  | .running rest _ => 2 * rest.length + 1
  | .waiting _ rest _ _ => 2 * rest.length + 2
  | .completed _ | .cancelled => 0

public theorem internal_decreases (model : Model Value Child W) (f : AsyncFn)
    {source target : Direct Value Child} {before after : W} {cost : Nat}
    (h : directStep model f source before = (.next, target, after, cost)) :
    segmentWork target < segmentWork source := by
  cases source with
  | running rest frame =>
    cases rest with
    | nil =>
      rcases he : model.evaluate f.result frame before with ⟨value, world, work⟩
      simp only [directStep, he, Prod.mk.injEq, reduceCtorEq, true_and, false_and] at h
    | cons command rest =>
      cases command with
      | bind name expr bound =>
        rcases he : model.evaluate expr frame before with ⟨value, world, work⟩
        simp only [directStep, he, Prod.mk.injEq, reduceCtorEq, true_and, false_and] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp only [segmentWork, List.length_cons]
        omega
      | await name expr boundary =>
        rcases he : makeTask model frame expr before with ⟨child, world, work⟩
        simp only [directStep, he, Prod.mk.injEq, reduceCtorEq, true_and, false_and] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp only [segmentWork, List.length_cons]
        omega
  | waiting name rest frame child =>
    rcases hp : pollTask model child before with ⟨result, child', world, work⟩
    cases result with
    | pending =>
      simp only [directStep, hp, Prod.mk.injEq, reduceCtorEq, true_and, false_and] at h
    | ready value =>
      simp only [directStep, hp, Prod.mk.injEq, reduceCtorEq, true_and, false_and] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [segmentWork]
      omega
  | completed value =>
    simp only [directStep, Prod.mk.injEq, reduceCtorEq, true_and, false_and] at h
  | cancelled =>
    simp only [directStep, Prod.mk.injEq, reduceCtorEq, true_and, false_and] at h

/-- Ordinary costs must hold for each reached state AND world. -/
public structure PollCostDuty (model : Model Value Child W) (f : AsyncFn)
    (states : Direct Value Child → W → Prop) (bound : Nat) : Prop where
  costBound : ∀ source before event target after cost, states source before →
    directStep model f source before = (event, target, after, cost) → cost ≤ bound
  internalClosed : ∀ source before target after cost, states source before →
    directStep model f source before = (.next, target, after, cost) → states target after

public theorem poll_cost_bounded (model : Model Value Child W) (f : AsyncFn)
    (states : Direct Value Child → W → Prop) (bound : Nat)
    (duty : PollCostDuty model f states bound)
    {source target : Direct Value Child} {before after : W} {event : Event Value} {cost : Nat}
    (initial : states source before) (run : DirectPoll model f source before event target after cost) :
    cost ≤ (segmentWork source + 1) * bound := by
  revert initial
  induction run with
  | stop step terminal =>
    intro initial
    exact Nat.le_trans (duty.costBound _ _ _ _ _ _ initial step)
      (Nat.le_mul_of_pos_left bound (Nat.succ_pos _))
  | next step rest ih =>
    intro initial
    have restCost := ih (duty.internalClosed _ _ _ _ _ initial step)
    have decrease := internal_decreases model f step
    have remainingBound := Nat.mul_le_mul_right bound (Nat.succ_le_of_lt decrease)
    have firstBound := duty.costBound _ _ _ _ _ _ initial step
    have restBound := Nat.le_trans restCost remainingBound
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- Each poll terminates even if subsequent polls stay Pending forever. -/
public theorem direct_poll_exists (model : Model Value Child W) (f : AsyncFn)
    (source : Direct Value Child) (world : W) :
    ∃ event target world' cost, DirectPoll model f source world event target world' cost := by
  rcases hs : directStep model f source world with ⟨event, target, world', work⟩
  cases event with
  | next =>
    obtain ⟨event, final, after, cost, run⟩ := direct_poll_exists model f target world'
    exact ⟨event, final, after, work + cost, .next hs run⟩
  | pending => exact ⟨.pending, target, world', work, .stop hs (by intro h; cases h)⟩
  | ready value marks =>
    exact ⟨.ready value marks, target, world', work, .stop hs (by intro h; cases h)⟩
  | refused => exact ⟨.refused, target, world', work, .stop hs (by intro h; cases h)⟩
termination_by segmentWork source
decreasing_by exact internal_decreases model f hs

end Gabbro.Grammatik.Async
