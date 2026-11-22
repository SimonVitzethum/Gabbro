module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.JoinLowering
public import Grammatik.Kern.Semantik.Evaluation.Aggregates.Locals
import Grammatik.Kern.Syntax.Syntax.ProduktZucker

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {V : Vertrag D} {Λ : List (Res D)} {l : Bool} {Γ : Ctx}
  {types : TypeResolution} {f : AsyncFn}

/-- Dispatch the actual stored successor of one poll. Pending preserves
    that task slot and the old frame. Ready restores the next live frame. -/
@[expose] public def awaitPollArms (types : TypeResolution) (f : AsyncFn) (tag : Nat)
    (within : tag + 1 ≤ f.body.length) (destination : String) (future : FutureExpr) (sourceType : Parser.STyp)
    {boundary : Boundary} {rest : List Command}
    (command : f.body.drop tag = Command.await destination future boundary :: rest)
    (same : taskResultType types [tag] future = types.ordinary sourceType)
    (binding : (f.params ++ f.fields).lookup destination = some sourceType)
    (task : Var Γ (taskStorageType types [tag] future)) (saved : Var Γ (frameType types f))
    (state : Var Γ (stateType types f)) (finished : Var Γ .bool) :
    Arms D V l Γ Λ Λ [some (taskActiveType types [tag] future), some (taskResultType types [tag] future)] :=
  .cons
    (.cons (.assignVar (.there state) (waitingExpr types f tag command (.var (.there saved)) (.var (.there task))))
      (.cons (.assignVar (.there finished) .tru) .nil))
    (.cons
      (.cons (.assignVar (.there state) (runningExpr types f (tag + 1) within
        (readyBindingFrame types f (.running (tag + 1)) destination sourceType same binding saved))) .nil)
      .nil)

/-- This is the actual ordinary G block for an await of a finite future. -/
@[expose] public def lowerAwaitPoll (elaboration : Elaboration D V Λ types f)
    (tag : Nat) (within : tag + 1 ≤ f.body.length) (destination : String) (future : FutureExpr) (sourceType : Parser.STyp)
    {boundary : Boundary} {rest : List Command}
    (command : f.body.drop tag = Command.await destination future boundary :: rest)
    (same : taskResultType types [tag] future = types.ordinary sourceType)
    (binding : (f.params ++ f.fields).lookup destination = some sourceType)
    (plan : PollPlan elaboration future)
    (task : Var Γ (taskStorageType types [tag] future)) (saved : Var Γ (frameType types f))
    (state : Var Γ (stateType types f)) (finished : Var Γ .bool) :
    Block D V l Γ Λ Λ :=
  .cons (plan.lower [tag] task)
    (.cons (.onTag (.var task) (awaitPollArms types f tag within destination future sourceType
      command same binding task saved state finished)) .nil)

/-- The outcome owns precisely the same resource inventory as the matched
    continuation. Arbitrarily nested join calls are handled by the plan. -/
public theorem lowerAwaitPoll_simulates (elaboration : Elaboration D V Λ types f) (inventory : Inventory D)
    (tag : Nat) (within : tag + 1 ≤ f.body.length) (destination : String) (future : FutureExpr) (sourceType : Parser.STyp)
    {boundary : Boundary} {rest : List Command}
    (command : f.body.drop tag = Command.await destination future boundary :: rest)
    (same : taskResultType types [tag] future = types.ordinary sourceType)
    (binding : (f.params ++ f.fields).lookup destination = some sourceType)
    (plan : PollPlan elaboration future)
    (slot : Var Γ (taskStorageType types [tag] future)) (saved : Var Γ (frameType types f))
    (state : Var Γ (stateType types f)) (finished : Var Γ .bool) (distinct : slot.position ≠ saved.position)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn) (prices : D.Fn → Nat)
    (world : World D) (env : Env D Γ) (frame : Frame (Value D)) (task : Task (Value D) (Child D types))
    (stored : FrameRep D types f (.waiting tag future) frame (env.get saved))
    (represented : TaskRep D types [tag] future task (env.get slot))
    (owned : MarksRep inventory (.waiting tag future) (.waiting tag frame task))
    (sameInventory : inventory.owned (.running (tag + 1)) = inventory.owned (.waiting tag future)) :
    let executed := execBlock oracle passes calls
      (lowerAwaitPoll (l := l) elaboration tag within destination future sourceType command same binding
        plan slot saved state finished) world env
    match runWaitingPoll elaboration calls prices tag destination frame task world with
    | .error (.inl failure) => executed = .logik failure
    | .error (.inr failure) => executed = .hardware failure
    | .ok (event, target, after, _) =>
      ∃ updated value, executed = .ok after
          (match event with
           | .pending => (((env.set slot updated).set state value).set finished true)
           | _ => ((env.set slot updated).set state value)) ∧
        Inv f types inventory target value ∧ encode D types f target = some value := by
  intro executed
  have lowered := plan.lower_simulates (l := l) [tag] slot oracle passes calls prices world env task represented
  have noReads (w : World D) : w.lese Λ [] = w := rfl
  cases poll : runTaskPoll elaboration calls prices task world with
  | error failure =>
    cases failure <;> simp only [poll, TaskStepRep] at lowered <;>
      simp only [runWaitingPoll, poll, executed, lowerAwaitPoll, execBlock, lowered]
  | ok answer =>
    obtain ⟨event, successor, after, price⟩ := answer
    simp only [poll, TaskStepRep] at lowered
    obtain ⟨updated, ran, representedNext⟩ := lowered
    let current := env.set slot updated
    have getSlot : current.get slot = updated := Env.get_set_same env slot updated
    have getFrame : current.get saved = env.get saved := Env.get_set_other env slot saved updated distinct
    let arms := awaitPollArms (V := V) (l := l) (Λ := Λ) types f tag within destination future sourceType command
      same binding slot saved state finished
    have ranNext : executed = execStmt oracle passes calls (.onTag (.var slot) arms) after current := by
      unfold executed
      rw [lowerAwaitPoll, execBlock, ran]
      simp only [execBlock]
      cases execStmt oracle passes calls (.onTag (.var slot) arms) after current <;> rfl
    have eventRep := runTaskPoll_rep elaboration calls prices represented plan.resolved poll
    have shape := pollRep_tag eventRep representedNext
    cases event with
    | pending =>
      obtain ⟨payload, shape⟩ := shape
      let record := waitingValue D types f tag command (env.get saved) updated
      let savedExpr : Expr D (taskActiveType types [tag] future :: Γ) Λ (stateType types f) :=
        waitingExpr types f tag command (.var (.there saved)) (.var (.there slot))
      have silent : savedExpr.orte = [] := by
        unfold savedExpr
        rw [waitingExpr_reads]
        rfl
      have value : eval after savedExpr after (.cons payload current) = record := by
        simp only [savedExpr, waitingExpr_eval, eval, Env.get, getSlot, getFrame, record]
      have writes : execStmt oracle passes calls (.onTag (.var slot) arms) after current =
          .ok after ((current.set state record).set finished true) := by
        unfold arms awaitPollArms
        erw [storedTag_active oracle passes calls slot _ _ after current payload (getSlot.trans shape)]
        simp only [execBlock, execStmt]
        erw [silent, noReads, value]
        rfl
      have marks : MarksRep inventory (.waiting tag future) (.waiting tag frame successor) := owned
      have invariant := waitingValue_inv types f inventory tag command frame successor (env.get saved) updated
        stored representedNext marks
      simp only [runWaitingPoll, poll, waitingReply]
      exact ⟨updated, record, ranNext.trans writes, invariant, inv_encoded f types inventory _ record invariant⟩
    | ready source =>
      obtain ⟨result, shape, resultTyped⟩ := shape
      let storage : Expr D (taskResultType types [tag] future :: Γ) Λ (frameType types f) :=
        readyBindingFrame types f (.running (tag + 1)) destination sourceType same binding saved
      have representedFrame : FrameRep D types f (.waiting tag future) frame (current.get saved) := by
        rw [getFrame]
        exact stored
      obtain ⟨noFrameRead, frameRep⟩ := readyBindingFrame_rep (Λ := Λ) destination sourceType same binding
        (await_retains_live tag destination future boundary rest command) saved after current result frame source resultTyped representedFrame
      let record := runningValue D types f (tag + 1) within (eval after storage after (.cons result current))
      have silent : (runningExpr types f (tag + 1) within storage).orte = [] :=
        (runningExpr_reads types f (tag + 1) within storage).trans noFrameRead
      have value := runningExpr_eval types f (tag + 1) within storage after after (.cons result current)
      have writes : execStmt oracle passes calls (.onTag (.var slot) arms) after current =
          .ok after (current.set state record) := by
        unfold arms awaitPollArms
        erw [storedTag_cached oracle passes calls slot _ _ after current result (getSlot.trans shape)]
        simp only [execBlock, execStmt]
        erw [silent, noReads, value]
        rfl
      have marks : MarksRep inventory (.running (tag + 1)) (.running (Child := Child D types) (tag + 1)
          (save frame destination source)) := by
        simpa only [MarksRep, State.marks, sameInventory, save] using owned
      have invariant := runningValue_inv types f inventory (tag + 1) within _ _ frameRep marks
      simp only [runWaitingPoll, poll, waitingReply]
      exact ⟨updated, record, ranNext.trans writes, invariant, inv_encoded f types inventory _ record invariant⟩

/-- A Waiting arm receives its frame and child only through the typed
    payload of the state tag selected by the dispatcher. -/
@[expose] public def waitingPhaseBlock (elaboration : Elaboration D V Λ types f)
    (tag : Nat) (within : tag + 1 ≤ f.body.length) (destination : String) (future : FutureExpr) (sourceType : Parser.STyp)
    {boundary : Boundary} {rest : List Command}
    (command : f.body.drop tag = Command.await destination future boundary :: rest)
    (same : taskResultType types [tag] future = types.ordinary sourceType)
    (binding : (f.params ++ f.fields).lookup destination = some sourceType)
    (plan : PollPlan elaboration future)
    (payload : Var Γ (phaseType types f (.waiting tag future)))
    (state : Var Γ (stateType types f)) (finished : Var Γ .bool) :
    Block D V l Γ Λ Λ :=
  .bind (.prodGet (.var payload) .head)
    (.bind (.prodGet (.var (.there payload)) (.tail .head))
      (lowerAwaitPoll elaboration tag within destination future sourceType command same binding plan
        .here (.there .here) (.there (.there state)) (.there (.there finished))))

/-- The same simulation holds when the poll takes its task and frame
    from the selected record and discards the ephemeral bindings. -/
public theorem waitingPhaseBlock_simulates (elaboration : Elaboration D V Λ types f) (inventory : Inventory D)
    (tag : Nat) (within : tag + 1 ≤ f.body.length) (destination : String) (future : FutureExpr) (sourceType : Parser.STyp)
    {boundary : Boundary} {rest : List Command}
    (command : f.body.drop tag = Command.await destination future boundary :: rest)
    (same : taskResultType types [tag] future = types.ordinary sourceType)
    (binding : (f.params ++ f.fields).lookup destination = some sourceType)
    (plan : PollPlan elaboration future)
    (payload : Var Γ (phaseType types f (.waiting tag future)))
    (state : Var Γ (stateType types f)) (finished : Var Γ .bool)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn) (prices : D.Fn → Nat)
    (world : World D) (env : Env D Γ) (frame : Frame (Value D)) (task : Task (Value D) (Child D types))
    (represented : PhaseRep D types f (.waiting tag future) (.waiting tag frame task) (env.get payload))
    (owned : MarksRep inventory (.waiting tag future) (.waiting tag frame task))
    (sameInventory : inventory.owned (.running (tag + 1)) = inventory.owned (.waiting tag future)) :
    let executed := execBlock oracle passes calls
      (waitingPhaseBlock (l := l) elaboration tag within destination future sourceType command same binding
        plan payload state finished) world env
    match runWaitingPoll elaboration calls prices tag destination frame task world with
    | .error (.inl failure) => executed = .logik failure
    | .error (.inr failure) => executed = .hardware failure
    | .ok (event, target, after, _) =>
      ∃ value, executed = .ok after
          (match event with
           | .pending => (env.set state value).set finished true
           | _ => env.set state value) ∧
        Inv f types inventory target value ∧ encode D types f target = some value := by
  intro executed
  generalize loaded : env.get payload = record at represented
  cases represented with
  | waiting _ _ _ _ frameValue taskValue slots child =>
    let extended : Env D (taskStorageType types [tag] future :: frameType types f :: Γ) :=
      .cons taskValue (.cons frameValue env)
    let inner := execBlock oracle passes calls
      (lowerAwaitPoll (l := l) elaboration tag within destination future sourceType command same binding
        plan .here (.there .here) (.there (.there state)) (.there (.there finished))) world extended
    have runs : executed = inner.schrumpf.schrumpf := by
      unfold executed waitingPhaseBlock inner
      simp only [execBlock, Expr.orte, List.nil_append, eval, prodGetW, World.lese, World.merke, List.map_nil]
      erw [loaded]
      have right : (Env.cons frameValue env).get (.there payload) = (frameValue, taskValue, ()) := loaded
      erw [right]
    have distinct : (Var.here : Var (taskStorageType types [tag] future :: frameType types f :: Γ)
        (taskStorageType types [tag] future)).position ≠
      (Var.there Var.here : Var (taskStorageType types [tag] future :: frameType types f :: Γ)
        (frameType types f)).position := Nat.zero_ne_one
    have simulated := lowerAwaitPoll_simulates (l := l) elaboration inventory tag within destination future sourceType
      command same binding plan .here (.there .here) (.there (.there state)) (.there (.there finished)) distinct
      oracle passes calls prices world extended frame task slots child owned sameInventory
    change (match runWaitingPoll elaboration calls prices tag destination frame task world with
      | .error (.inl failure) => inner = .logik failure
      | .error (.inr failure) => inner = .hardware failure
      | .ok (event, target, after, _) =>
        ∃ updated value, inner = .ok after
          (match event with
           | .pending => (((extended.set .here updated).set (.there (.there state)) value).set
               (.there (.there finished)) true)
           | _ => ((extended.set .here updated).set (.there (.there state)) value)) ∧
          Inv f types inventory target value ∧ encode D types f target = some value) at simulated
    cases result : runWaitingPoll elaboration calls prices tag destination frame task world with
    | error failure =>
      cases failure <;> simp only [result] at simulated <;> rw [runs, simulated] <;> rfl
    | ok answer =>
      obtain ⟨event, target, after, cost⟩ := answer
      simp only [result] at simulated
      obtain ⟨updated, value, correct, invariant, encoded⟩ := simulated
      refine ⟨value, ?_, invariant, encoded⟩
      rw [runs, correct]
      cases event <;> rfl

end Gabbro.Grammatik.Async.Representation
