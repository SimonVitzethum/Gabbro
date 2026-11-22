module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.CheckedDispatch
import Grammatik.Kern.Syntax.Syntax.ProduktZucker
import Lean.Elab.Tactic.Omega

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {V : Vertrag D} {Λ : List (Res D)} {l : Bool} {Γ : Ctx}
  {types : TypeResolution} {f : AsyncFn}

/-- The remaining number of dispatches, counting a final or refused
    answer and at most two activations per remaining command. -/
@[expose] public def activationFuel (f : AsyncFn) : State (Value D) (Child D types) → Nat
  | .running tag _ => 2 * (f.body.length - tag) + 1
  | .waiting tag .. => 2 * (f.body.length - tag - 1) + 2
  | .completed .. | .cancelled => 1

public theorem activationFuel_pos (f : AsyncFn) (source : State (Value D) (Child D types)) :
    0 < activationFuel f source := by
  cases source <;> simp only [activationFuel] <;> omega

public theorem activationFuel_le (f : AsyncFn) (source : State (Value D) (Child D types)) :
    activationFuel f source ≤ 2 * f.body.length + 2 := by
  cases source <;> simp only [activationFuel] <;> omega

public theorem activationFuel_decreases (elaboration : Elaboration D V Λ types f)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn) (prices : D.Fn → Nat)
    (source target : State (Value D) (Child D types)) (before after : World D) (cost : Nat)
    (advanced : runActivation elaboration calls prices source before = .ok (.next, target, after, cost)) :
    activationFuel f target < activationFuel f source := by
  cases source with
  | cancelled => simp only [runActivation, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at advanced
  | completed => simp only [runActivation, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at advanced
  | running tag frame =>
    cases position : f.body.drop tag with
    | nil =>
      simp only [runActivation, position, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at advanced
    | cons command rest =>
      have within := congrArg List.length position
      simp only [List.length_drop, List.length_cons] at within
      cases command <;>
        simp only [runActivation, position, Except.ok.injEq, Prod.mk.injEq, true_and] at advanced <;>
        obtain ⟨rfl, _, _⟩ := advanced <;> simp only [activationFuel] <;> omega
  | waiting tag frame task =>
    cases position : f.body.drop tag with
    | nil =>
      simp only [runActivation, position, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at advanced
    | cons command rest =>
      have within := congrArg List.length position
      simp only [List.length_drop, List.length_cons] at within
      cases command with
      | bind =>
        simp only [runActivation, position, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at advanced
      | await =>
        cases polled : runTaskPoll elaboration calls prices task before with
        | error failure =>
          simp only [runActivation, position, runWaitingPoll, polled, reduceCtorEq] at advanced
        | ok result =>
          rcases result with ⟨answer, task', after', work⟩
          cases answer with
          | pending =>
            simp only [runActivation, position, runWaitingPoll, polled, waitingReply, Except.ok.injEq,
              Prod.mk.injEq, reduceCtorEq, false_and] at advanced
          | ready =>
            simp only [runActivation, position, runWaitingPoll, polled, waitingReply, Except.ok.injEq,
              Prod.mk.injEq, true_and] at advanced
            obtain ⟨rfl, _, _⟩ := advanced
            simp only [activationFuel]
            omega

/-- A source poll stops at its first external answer or G failure.
    Cost accumulates only for a successful poll. -/
@[expose] public def resolvedPoll (elaboration : Elaboration D V Λ types f)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn) (prices : D.Fn → Nat)
    (source : State (Value D) (Child D types)) (before : World D) :
    Except (Logik D ⊕ Hardware D) (Event (Value D) × State (Value D) (Child D types) × World D × Nat) :=
  match advanced : runActivation elaboration calls prices source before with
  | .error failure => .error failure
  | .ok (.next, target, after, cost) =>
    (resolvedPoll elaboration calls prices target after).map fun (event, final, world, remaining) =>
      (event, final, world, cost + remaining)
  | .ok answer => .ok answer
termination_by activationFuel f source
decreasing_by exact activationFuel_decreases elaboration calls prices source target before after cost advanced

/-- The emitted loop resets its flag for each poll and retains the ordinary
    G overflow branch. Its proof discharges that branch on represented inputs. -/
@[expose] public def checkedPoll {elaboration : Elaboration D V Λ types f}
    (table : (index : Fin (phases f).length) → PhasePlan elaboration ((phases f).get index))
    (state : Var Γ (stateType types f)) (finished : Var Γ .bool)
    (exhausted : Block D V l Γ Λ Λ) : Block D V l Γ Λ Λ :=
  .cons (.assignVar finished .fls)
    (.cons (.retry (2 * f.body.length + 2) (.var finished)
      (.cons (checkedDispatch table state finished) .nil) exhausted) .nil)

end Gabbro.Grammatik.Async.Representation
