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

private theorem singleStatement (statement : Stmt D V l Γ Λ Λ)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ) :
    execBlock oracle passes calls (.cons statement .nil) world env =
      execStmt oracle passes calls statement world env := by
  rw [execBlock]
  cases execStmt oracle passes calls statement world env <;> rfl

private theorem resolvedPoll_stop (elaboration : Elaboration D V Λ types f)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn) (prices : D.Fn → Nat)
    (source target : State (Value D) (Child D types)) (before after : World D) (cost : Nat)
    (event : Event (Value D)) (stops : activationStops event = true)
    (answered : runActivation elaboration calls prices source before = .ok (event, target, after, cost)) :
    resolvedPoll elaboration calls prices source before = .ok (event, target, after, cost) := by
  cases event with
  | next => cases stops
  | pending | ready | refused => rw [resolvedPoll, answered]

private theorem refine_addCost (inventory : Inventory D)
    (state : Var Γ (stateType types f)) (finished : Var Γ .bool) (outcome : Ausgang V l Γ) (work : Nat)
    (answer : Except (Logik D ⊕ Hardware D) (Event (Value D) × State (Value D) (Child D types) × World D × Nat))
    (refined : ActivationRefines inventory state finished outcome answer) :
    ActivationRefines inventory state finished outcome
      (answer.map fun (event, final, world, remaining) => (event, final, world, work + remaining)) := by
  cases answer with
  | error failure => cases failure <;> exact refined
  | ok result => obtain ⟨_, _, _, _⟩ := result; exact refined

private theorem retry_finished (step : World D → Env D Γ → Ausgang V true Γ)
    (exhausted : World D → Env D Γ → Ausgang V l Γ) (finished : Var Γ .bool)
    (fuel : Nat) (world : World D) (env : Env D Γ) (stops : env.get finished = true) :
    retryLauf step (fun w e => (w, e.get finished)) exhausted fuel world env = .ok world env := by
  cases fuel <;> simp only [retryLauf, stops, if_true]

/-- The real retry loop uses the source's exact results and failure causes.
    Its overflow block is unreachable for every represented starting phase
    at the emitted bound, independently of the overflow block's behavior. -/
private theorem checkedRetry_refines {elaboration : Elaboration D V Λ types f}
    (table : (index : Fin (phases f).length) → PhasePlan elaboration ((phases f).get index))
    (inventory : Inventory D) (fixed : FixedActivationInventory (f := f) inventory)
    (state : Var Γ (stateType types f)) (finished : Var Γ .bool)
    (separate : state.position ≠ finished.position)
    (oracle : Orakel D) (passes : Nat) (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (prices : D.Fn → Nat) (exhausted : World D → Env D Γ → Ausgang V l Γ)
    (fuel : Nat) (source : State (Value D) (Child D types)) (world : World D) (env : Env D Γ)
    (enough : activationFuel f source ≤ fuel) (unfinished : env.get finished = false)
    (represented : Inv f types inventory source (env.get state)) :
    ActivationRefines inventory state finished
      (retryLauf (execStmt oracle passes calls (checkedDispatch (l := true) table state finished))
        (fun w e => (w, e.get finished)) exhausted fuel world env)
      (resolvedPoll elaboration calls prices source world) := by
  induction fuel generalizing source world env with
  | zero =>
    have positive := activationFuel_pos f source
    omega
  | succ fuel ih =>
    let step := execStmt oracle passes calls (checkedDispatch (l := true) table state finished)
    have matched := checkedDispatch_refines table inventory fixed state finished separate
      oracle passes calls prices world env unfinished source represented (l := true)
    change ActivationRefines inventory state finished (step world env) _ at matched
    cases answered : runActivation elaboration calls prices source world with
    | error failure =>
      rw [answered] at matched
      rw [resolvedPoll, answered]
      cases failure with
      | inl failure =>
        change step world env = .logik failure at matched
        change retryLauf step _ exhausted (fuel + 1) world env = .logik failure
        simp only [retryLauf, unfinished, Bool.false_eq_true, if_false, matched]
      | inr failure =>
        change step world env = .hardware failure at matched
        change retryLauf step _ exhausted (fuel + 1) world env = .hardware failure
        simp only [retryLauf, unfinished, Bool.false_eq_true, if_false, matched]
    | ok answer =>
      obtain ⟨event, target, after, cost⟩ := answer
      rw [answered] at matched
      obtain ⟨updated, stepped, inv, stopFlag⟩ := matched
      change step world env = .ok after updated at stepped
      change ActivationRefines inventory state finished
        (retryLauf step _ exhausted (fuel + 1) world env) _
      simp only [retryLauf, unfinished, Bool.false_eq_true, if_false, stepped]
      cases stops : activationStops event with
      | true =>
        rw [resolvedPoll_stop elaboration calls prices source target world after cost event stops answered,
          retry_finished step exhausted finished fuel after updated (stopFlag.trans stops)]
        exact ⟨updated, rfl, inv, stopFlag⟩
      | false =>
        cases event with
        | pending | ready | refused => cases stops
        | next =>
          have decreases := activationFuel_decreases elaboration calls prices source target world after cost answered
          have remaining : activationFuel f target ≤ fuel := by omega
          have rest := ih target after updated remaining (stopFlag.trans stops) inv
          rw [resolvedPoll, answered]
          exact refine_addCost inventory state finished _ cost _ rest

public theorem checkedPoll_refines {elaboration : Elaboration D V Λ types f}
    (table : (index : Fin (phases f).length) → PhasePlan elaboration ((phases f).get index))
    (inventory : Inventory D) (fixed : FixedActivationInventory (f := f) inventory)
    (state : Var Γ (stateType types f)) (finished : Var Γ .bool)
    (separate : state.position ≠ finished.position)
    (oracle : Orakel D) (passes : Nat) (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (prices : D.Fn → Nat) (exhausted : Block D V l Γ Λ Λ)
    (source : State (Value D) (Child D types)) (world : World D) (env : Env D Γ)
    (represented : Inv f types inventory source (env.get state)) :
    ActivationRefines inventory state finished
      (execBlock oracle passes calls (checkedPoll table state finished exhausted) world env)
      (resolvedPoll elaboration calls prices source world) := by
  let reset := env.set finished (false : Wert D .bool)
  have kept : Inv f types inventory source (reset.get state) :=
    (Env.get_set_other env finished state (false : Wert D .bool) (Ne.symm separate)).symm ▸ represented
  have cleared : reset.get finished = false := Env.get_set_same env finished (false : Wert D .bool)
  change ActivationRefines inventory state finished
    (execBlock oracle passes calls (.cons
      (.retry (2 * f.body.length + 2) (.var finished) (.cons (checkedDispatch table state finished) .nil)
        exhausted) .nil) world reset) _
  rw [singleStatement, execStmt]
  simp only [singleStatement]
  exact checkedRetry_refines table inventory fixed state finished separate oracle passes calls prices
    (execBlock oracle passes calls exhausted) _ source world reset (activationFuel_le f source) cleared kept

end Gabbro.Grammatik.Async.Representation
