module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.Tasks
public import Grammatik.Nebenlaeufigkeit.Async.Segment.Model
import Lean.Elab.Tactic.Omega

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {V : Vertrag D} {Λ : List (Res D)}
  {types : TypeResolution} {f : AsyncFn}

/-- A finite future only needs declared poll functions for its own leaves. -/
@[expose] public def ResolvedFuture (elaboration : Elaboration D V Λ types f) : FutureExpr → Prop
  | .call name _ => ∃ callee, elaboration.callee name = some callee
  | .join left right => ResolvedFuture elaboration left ∧ ResolvedFuture elaboration right

/-- The actual successor task can be stored in the generated state. When
    the poll is Ready its storage is exactly the cached typed payload. -/
public inductive PollRep (D : Deklaration) (types : TypeResolution)
    (path : List Nat) (future : FutureExpr) :
    Poll (Value D) → Task (Value D) (Child D types) → Prop where
  | pending (stored : TaskRep D types path future task record) :
      PollRep D types path future Poll.pending task
  | ready (typed : valueAt D (taskResultType types path future) value = some result)
      (stored : TaskRep D types path future (.ready value) record) :
      PollRep D types path future (Poll.ready value) (.ready value)

public theorem PollRep.storage {path : List Nat} {future : FutureExpr}
    {event : Poll (Value D)} {task : Task (Value D) (Child D types)}
    (progress : PollRep D types path future event task) :
    ∃ record, TaskRep D types path future task record := by
  cases progress with
  | pending stored => exact ⟨_, stored⟩
  | ready _ stored => exact ⟨_, stored⟩

/-- A leaf polls the resolved ordinary function. Its finite answer either
    updates the child record or caches the very result returned by G. -/
public theorem leaf_poll_rep (elaboration : Elaboration D V Λ types f)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (prices : D.Fn → Nat) (normal : PollRuns elaboration calls)
    (path : List Nat) (name : String) (args : List Parser.SExpr)
    (callee : AwaitedCall D V Λ types name) (known : elaboration.callee name = some callee)
    (storage : Wert D (types.childState name)) (world : World D) :
    let step := pollTask (inducedModel elaboration calls prices normal) (.leaf (.active name storage)) world
    PollRep D types path (.call name args) step.1 step.2.1 := by
  have selected :
      pollChild elaboration calls prices normal (Child.active name storage) world =
        (let answer := normal name callee known world storage
         let (result, updated) := decodePollAnswer D types name storage
           (ergWert callee.pollResult answer.val.2)
         (result, updated, answer.val.1, prices callee.poll)) := by
    simp only [pollChild]
    split
    · rename_i absent
      rw [known] at absent
      cases absent
    · rename_i actual found
      have same : actual = callee := Option.some.inj (found.symm.trans known)
      subst actual
      rfl
  simp only [pollTask, inducedModel, selected]
  generalize ergWert callee.pollResult (normal name callee known world storage).val.2 = answer
  obtain ⟨⟨tag, bound⟩, payload⟩ := answer
  cases tag with
  | zero =>
    exact .ready (valueAt_typed D _ payload) (.callReady _ _ _ (valueAt_typed D _ payload))
  | succ tag =>
    cases tag with
    | zero => exact .pending (.callActive _ _ _ payload)
    | succ tag =>
      have small : tag + 2 < 2 := bound
      omega

/-- Join only caches a pair when both branches have returned real typed
    results. While either is Pending both successor stores are retained. -/
public theorem join_poll_rep {path : List Nat} {left right : FutureExpr}
    {lp rp : Poll (Value D)} {l r : Task (Value D) (Child D types)}
    (leftRep : PollRep D types (0 :: path) left lp l)
    (rightRep : PollRep D types (1 :: path) right rp r) :
    let result : Poll (Value D) × Task (Value D) (Child D types) :=
      match lp, rp with
      | .ready a, .ready b => (.ready (.pair a b), .ready (.pair a b))
      | _, _ => (.pending, .join l r)
    PollRep D types path (.join left right) result.1 result.2 := by
  cases leftRep with
  | pending stored =>
    obtain ⟨_, rightStored⟩ := rightRep.storage
    exact .pending (.joinActive stored rightStored)
  | @ready leftValue leftResult leftRecord leftTyped leftStored =>
    cases rightRep with
    | pending rightStored => exact .pending (.joinActive leftStored rightStored)
    | @ready rightValue rightResult rightRecord rightTyped rightStored =>
      have typed : valueAt D (taskResultType types path (.join left right))
          (.pair leftValue rightValue) = some (leftResult, rightResult, ()) := by
        simp only [taskResultType, valueAt, leftTyped, rightTyped, Option.bind_eq_bind,
          Option.bind_some, Option.pure_def] <;> rfl
      exact .ready typed (.joinReady typed)

public theorem pollTask_rep (elaboration : Elaboration D V Λ types f)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (prices : D.Fn → Nat) (normal : PollRuns elaboration calls)
    {path : List Nat} {future : FutureExpr} {task : Task (Value D) (Child D types)}
    {record : Wert D (taskStorageType types path future)}
    (represented : TaskRep D types path future task record)
    (resolved : ResolvedFuture elaboration future) (world : World D) :
    let step := pollTask (inducedModel elaboration calls prices normal) task world
    PollRep D types path future step.1 step.2.1 := by
  induction represented generalizing world with
  | callActive path name args storage =>
    obtain ⟨callee, known⟩ := resolved
    exact leaf_poll_rep elaboration calls prices normal path name args callee known storage world
  | callReady path name args typed =>
    exact .ready typed (.callReady path name args typed)
  | joinReady typed => exact .ready typed (.joinReady typed)
  | joinActive leftRep rightRep leftPoll rightPoll =>
    have leftResult := leftPoll resolved.1 world
    simp only [pollTask]
    generalize pollTask (inducedModel elaboration calls prices normal) _ world = step at leftResult ⊢
    obtain ⟨leftEvent, leftTask, middle, leftCost⟩ := step
    have rightResult := rightPoll resolved.2 middle
    generalize pollTask (inducedModel elaboration calls prices normal) _ middle = step at rightResult ⊢
    obtain ⟨rightEvent, rightTask, after, rightCost⟩ := step
    cases leftEvent <;> cases rightEvent <;> exact join_poll_rep leftResult rightResult

end Gabbro.Grammatik.Async.Representation
