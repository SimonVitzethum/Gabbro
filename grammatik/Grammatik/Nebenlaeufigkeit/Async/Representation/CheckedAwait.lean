module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.ConstructLowering
import Lean.Elab.Tactic.Omega

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {V : Vertrag D} {Λ : List (Res D)} {l : Bool} {Γ : Ctx}
  {types : TypeResolution} {f : AsyncFn}

/-- The same callee plan supplies both the constructor and the poll.
    It cannot poll a different resolved declaration after suspension. -/
@[expose] public def ConstructPlan.pollPlan {elaboration : Elaboration D V Λ types f} {tag : Nat} :
    {future : FutureExpr} → ConstructPlan elaboration tag future → PollPlan elaboration future
  | _, .call name args callee known _ => .call name args callee known
  | _, .join first second => .join (pollPlan first) (pollPlan second)

/-- Both halves of an await are pinned to one actual source command,
    its declared result slot and its resolved callees. -/
public structure CheckedAwait (elaboration : Elaboration D V Λ types f) (tag : Nat) where
  destination : String
  future : FutureExpr
  boundary : Boundary
  rest : List Command
  command : f.body.drop tag = Command.await destination future boundary :: rest
  within : tag + 1 ≤ f.body.length
  sourceType : Parser.STyp
  binding : (f.params ++ f.fields).lookup destination = some sourceType
  resultType : taskResultType types [tag] future = types.ordinary sourceType
  plan : ConstructPlan elaboration tag future

@[expose] public def checkAwaitAt (elaboration : Elaboration D V Λ types f) (tag : Nat) :
    Except String (CheckedAwait elaboration tag) := do
  match found : f.body.drop tag with
  | .await destination future boundary :: rest =>
    match binding : (f.params ++ f.fields).lookup destination with
    | none => throw "async: missing await result declaration"
    | some sourceType =>
      if typed : taskResultType types [tag] future = types.ordinary sourceType then
        let plan ← ConstructPlan.resolve elaboration tag future
        have within : tag + 1 ≤ f.body.length := by
          have length := congrArg List.length found
          simp only [List.length_drop, List.length_cons] at length
          omega
        return ⟨destination, future, boundary, rest, found, within, sourceType, binding, typed, plan⟩
      else throw "async: awaited result disagrees with its declaration"
  | _ => throw "async: position is not an await command"

@[expose] public def CheckedAwait.start {elaboration : Elaboration D V Λ types f} {tag : Nat}
    (checked : CheckedAwait elaboration tag) (saved : Var Γ (frameType types f))
    (state : Var Γ (stateType types f)) : Block D V l Γ Λ Λ :=
  beginAwaitBlock tag checked.command checked.plan saved state

@[expose] public def CheckedAwait.poll {elaboration : Elaboration D V Λ types f} {tag : Nat}
    (checked : CheckedAwait elaboration tag) (payload : Var Γ (phaseType types f (.waiting tag checked.future)))
    (state : Var Γ (stateType types f)) (finished : Var Γ .bool) : Block D V l Γ Λ Λ :=
  waitingPhaseBlock elaboration tag checked.within checked.destination checked.future checked.sourceType checked.command
    checked.resultType checked.binding checked.plan.pollPlan payload state finished

public theorem CheckedAwait.start_simulates {elaboration : Elaboration D V Λ types f} {tag : Nat}
    (checked : CheckedAwait elaboration tag) (inventory : Inventory D)
    (saved : Var Γ (frameType types f)) (state : Var Γ (stateType types f))
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ) (frame : Frame (Value D))
    (represented : FrameRep D types f (.running tag) frame (env.get saved))
    (owned : MarksRep inventory (.running tag) (.running (Child := Child D types) tag frame))
    (sameInventory : inventory.owned (.waiting tag checked.future) = inventory.owned (.running tag)) :
    let built := makeTaskBy (evaluateBound elaboration) (constructChild elaboration) frame checked.future world
    let target := State.waiting tag frame built.1
    ∃ value, execBlock oracle passes calls (checked.start (l := l) saved state) world env =
        .ok built.2.1 (env.set state value) ∧
      Inv f types inventory target value ∧ encode D types f target = some value :=
  beginAwaitBlock_simulates inventory tag checked.command checked.plan saved state oracle passes calls
    world env frame represented owned sameInventory

public theorem CheckedAwait.poll_simulates {elaboration : Elaboration D V Λ types f} {tag : Nat}
    (checked : CheckedAwait elaboration tag) (inventory : Inventory D)
    (payload : Var Γ (phaseType types f (.waiting tag checked.future)))
    (state : Var Γ (stateType types f)) (finished : Var Γ .bool)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn) (prices : D.Fn → Nat)
    (world : World D) (env : Env D Γ) (frame : Frame (Value D)) (task : Task (Value D) (Child D types))
    (represented : PhaseRep D types f (.waiting tag checked.future) (.waiting tag frame task) (env.get payload))
    (owned : MarksRep inventory (.waiting tag checked.future) (.waiting tag frame task))
    (sameInventory : inventory.owned (.running (tag + 1)) = inventory.owned (.waiting tag checked.future)) :
    let executed := execBlock oracle passes calls (checked.poll (l := l) payload state finished) world env
    match runWaitingPoll elaboration calls prices tag checked.destination frame task world with
    | .error (.inl failure) => executed = .logik failure
    | .error (.inr failure) => executed = .hardware failure
    | .ok (event, target, after, _) =>
      ∃ value, executed = .ok after
          (match event with
           | .pending => (env.set state value).set finished true
           | _ => env.set state value) ∧
        Inv f types inventory target value ∧ encode D types f target = some value :=
  waitingPhaseBlock_simulates elaboration inventory tag checked.within checked.destination checked.future checked.sourceType
    checked.command checked.resultType checked.binding checked.plan.pollPlan payload state finished oracle passes calls
    prices world env frame task represented owned sameInventory

end Gabbro.Grammatik.Async.Representation
