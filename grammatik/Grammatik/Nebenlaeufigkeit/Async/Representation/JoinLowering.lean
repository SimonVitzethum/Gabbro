module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.TaskLowering

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {V : Vertrag D} {Λ : List (Res D)} {l : Bool} {Γ : Ctx}

/-- Keep both updated slots when a child is still active. When both
    children have finished, cache the payloads in source order. -/
@[expose] public def collectJoin (types : TypeResolution) (path : List Nat) (left right : FutureExpr)
    (first : Var Γ (taskStorageType types (0 :: path) left))
    (second : Var Γ (taskStorageType types (1 :: path) right))
    (out : Var Γ (taskStorageType types path (.join left right))) : Stmt D V l Γ Λ Λ :=
  collectStored first second
    (.cons (.assignVar (.there out)
      (joinChildrenExpr types path left right (.var (.there first)) (.var (.there second)))) .nil)
    (.cons (.assignVar (.there (.there out))
      (joinChildrenExpr types path left right (.var (.there (.there first))) (.var (.there (.there second))))) .nil)
    (.cons (.assignVar (.there (.there out))
      (.case [some (taskActiveType types path (.join left right)), some (taskResultType types path (.join left right))]
        ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩
        (.val (.prod (types.recordName (3 :: path)) (.cons (.var (.there .here)) (.cons (.var .here) .nil)))))) .nil)

-- Each recursive statement is generated in the environment containing
-- the two private child slots and the active parent payload.
@[expose] public abbrev JoinCtx (types : TypeResolution) (path : List Nat) (left right : FutureExpr) (Γ : Ctx) :=
  taskStorageType types (1 :: path) right :: taskStorageType types (0 :: path) left ::
    taskActiveType types path (.join left right) :: Γ

@[expose] public def joinActiveBlock (types : TypeResolution) (path : List Nat) (left right : FutureExpr)
    (out : Var Γ (taskStorageType types path (.join left right)))
    (first second : Stmt D V l (JoinCtx types path left right Γ) Λ Λ) :
    Block D V l (taskActiveType types path (.join left right) :: Γ) Λ Λ :=
  .bind (.prodGet (.var .here) .head)
    (.bind (.prodGet (.var (.there .here)) (.tail .head))
      (.cons first (.cons second (.cons
        (collectJoin types path left right (.there .here) .here (.there (.there (.there out)))) .nil))))

/-- The cached branch skips the join's entire child tree. -/
@[expose] public def joinTaskStmt (types : TypeResolution) (path : List Nat) (left right : FutureExpr)
    (out : Var Γ (taskStorageType types path (.join left right)))
    (first second : Stmt D V l (JoinCtx types path left right Γ) Λ Λ) :
    Stmt D V l Γ Λ Λ :=
  .onTag (.var out) (.cons (joinActiveBlock types path left right out first second) (.cons .nil .nil))

/-- Sample the two slots from the active payload before any poll, then
    run the second statement in the actual world of the first. -/
public theorem joinActiveBlock_exec (types : TypeResolution) (path : List Nat) (left right : FutureExpr)
    (out : Var Γ (taskStorageType types path (.join left right)))
    (first second : Stmt D V l (JoinCtx types path left right Γ) Λ Λ)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ)
    (a : Wert D (taskStorageType types (0 :: path) left)) (b : Wert D (taskStorageType types (1 :: path) right)) :
    let initial : Env D (JoinCtx types path left right Γ) := .cons b (.cons a (.cons (a, b, ()) env))
    execBlock oracle passes calls (joinActiveBlock types path left right out first second) world (.cons (a, b, ()) env) =
      (((match execStmt oracle passes calls first world initial with
        | .ok middle leftDone =>
          match execStmt oracle passes calls second middle leftDone with
          | .ok final rightDone => execStmt oracle passes calls
              (collectJoin (Λ := Λ) types path left right (.there .here) .here (.there (.there (.there out)))) final rightDone
          | failure => failure
        | failure => failure) : Ausgang V l (JoinCtx types path left right Γ)).schrumpf).schrumpf := by
  intro initial
  let collect : Stmt D V l (JoinCtx types path left right Γ) Λ Λ :=
    collectJoin types path left right (.there .here) .here (.there (.there (.there out)))
  have lastStep (final : World D) (context : Env D (JoinCtx types path left right Γ)) :
      execBlock oracle passes calls (.cons collect .nil) final context =
        execStmt oracle passes calls collect final context := by
    simp only [execBlock]
    cases execStmt oracle passes calls collect final context <;> rfl
  change ((execBlock oracle passes calls (.cons first (.cons second (.cons collect .nil)))
    world initial).schrumpf).schrumpf = _
  simp only [lastStep, execBlock]

/-- The semantic poll event determines the physical tag. A Ready tag
    additionally carries the result of the exact typed projection. -/
public theorem pollRep_tag {types : TypeResolution} {path : List Nat} {future : FutureExpr}
    {event : Poll (Value D)} {task : Task (Value D) (Child D types)}
    {record : Wert D (taskStorageType types path future)}
    (polled : PollRep D types path future event task)
    (stored : TaskRep D types path future task record) :
    match event with
    | .pending => ∃ payload, record =
        readyAnswer D (taskActiveType types path future) (taskResultType types path future) payload
    | .ready value => ∃ result, record =
        pendingAnswer D (taskActiveType types path future) (taskResultType types path future) result ∧
        valueAt D (taskResultType types path future) value = some result := by
  cases polled with
  | pending _ active =>
    cases stored with
    | callActive => exact ⟨_, rfl⟩
    | joinActive => exact ⟨_, rfl⟩
    | callReady | joinReady => exact (active _ rfl).elim
  | ready _ _ =>
    cases stored with
    | callReady | joinReady => exact ⟨_, rfl, by assumption⟩

/-- A reconstructed parent value is the exact encoding of the semantic
    join successor. Both children have already been evaluated. -/
public theorem collectJoin_exec {types : TypeResolution} (path : List Nat) (left right : FutureExpr)
    (first : Var Γ (taskStorageType types (0 :: path) left))
    (second : Var Γ (taskStorageType types (1 :: path) right))
    (out : Var Γ (taskStorageType types path (.join left right)))
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ) {lp rp : Poll (Value D)} {a b : Task (Value D) (Child D types)}
    (leftTask : TaskRep D types (0 :: path) left a (env.get first))
    (rightTask : TaskRep D types (1 :: path) right b (env.get second))
    (leftEvent : PollRep D types (0 :: path) left lp a) (rightEvent : PollRep D types (1 :: path) right rp b) :
    let successor : Task (Value D) (Child D types) :=
      match lp, rp with
      | .ready first, .ready second => .ready (.pair first second)
      | _, _ => .join a b
    ∃ value, execStmt oracle passes calls (collectJoin (V := V) (Λ := Λ) (l := l) types path left right
        first second out) world env = .ok world (env.set out value) ∧
      TaskRep D types path (.join left right) successor value := by
  obtain leftTag := pollRep_tag leftEvent leftTask
  obtain rightTag := pollRep_tag rightEvent rightTask
  cases lp with
  | pending =>
    obtain ⟨payload, tag⟩ := leftTag
    unfold collectJoin
    erw [collectStored_leftActive oracle passes calls first second _ _ _ world env payload tag]
    exact ⟨_, rfl, .joinActive leftTask rightTask⟩
  | ready aValue =>
    obtain ⟨aResult, aTag, aTyped⟩ := leftTag
    cases rp with
    | pending =>
      obtain ⟨payload, tag⟩ := rightTag
      unfold collectJoin
      erw [collectStored_rightActive oracle passes calls first second _ _ _ world env aResult payload aTag tag]
      exact ⟨_, rfl, .joinActive leftTask rightTask⟩
    | ready bValue =>
      obtain ⟨bResult, bTag, bTyped⟩ := rightTag
      unfold collectJoin
      erw [collectStored_bothCached oracle passes calls first second _ _ _ world env aResult bResult aTag bTag]
      refine ⟨_, rfl, .joinReady ?_⟩
      change valueAt D (taskResultType types path (.join left right)) (.pair aValue bValue) =
        some (aResult, bResult, ())
      simp only [taskResultType, valueAt, aTyped, bTyped, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def] <;> rfl

/-- Compositional simulation of a join. Left failure suppresses the
    right statement, while right failure suppresses record reconstruction. -/
public theorem joinTaskStmt_simulates {types : TypeResolution} {f : AsyncFn}
    (elaboration : Elaboration D V Λ types f) (path : List Nat) (left right : FutureExpr)
    (leftResolved : ResolvedFuture elaboration left) (rightResolved : ResolvedFuture elaboration right)
    (out : Var Γ (taskStorageType types path (.join left right)))
    (first second : Stmt D V l (JoinCtx types path left right Γ) Λ Λ)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn) (prices : D.Fn → Nat)
    (firstCorrect : ∀ world (env : Env D (JoinCtx types path left right Γ)) task,
      TaskRep D types (0 :: path) left task (env.get (.there .here)) →
      TaskStepRep types (0 :: path) left (.there .here) env
        (execStmt oracle passes calls first world env) (runTaskPoll elaboration calls prices task world))
    (secondCorrect : ∀ world (env : Env D (JoinCtx types path left right Γ)) task,
      TaskRep D types (1 :: path) right task (env.get .here) →
      TaskStepRep types (1 :: path) right .here env
        (execStmt oracle passes calls second world env) (runTaskPoll elaboration calls prices task world))
    (world : World D) (env : Env D Γ) (task : Task (Value D) (Child D types))
    (represented : TaskRep D types path (.join left right) task (env.get out)) :
    TaskStepRep types path (.join left right) out env
      (execStmt oracle passes calls (joinTaskStmt types path left right out first second) world env)
      (runTaskPoll elaboration calls prices task world) := by
  generalize same : env.get out = record at represented
  cases represented with
  | joinReady typed =>
    unfold joinTaskStmt
    erw [storedTag_cached oracle passes calls out (joinActiveBlock types path left right out first second) .nil
      world env _ same]
    simp only [runTaskPoll, pollTaskWith, pure, Except.pure, TaskStepRep]
    refine ⟨_, ?_, .joinReady (by assumption)⟩
    rw [← same, setCurrent]
    rfl
  | @joinActive _ _ a aValue _ b bValue aRep bRep =>
    unfold joinTaskStmt
    erw [storedTag_active oracle passes calls out (joinActiveBlock types path left right out first second) .nil
      world env (aValue, bValue, ()) same]
    rw [joinActiveBlock_exec, runTaskPoll_join]
    let initial : Env D (JoinCtx types path left right Γ) := .cons bValue (.cons aValue (.cons (aValue, bValue, ()) env))
    have ranLeft := firstCorrect world initial a aRep
    cases leftOutcome : runTaskPoll elaboration calls prices a world with
    | error cause =>
      cases cause <;> simp only [leftOutcome, TaskStepRep, bind, Except.bind] at ranLeft ⊢ <;>
        erw [ranLeft] <;> rfl
    | ok leftAnswer =>
      obtain ⟨lp, aNext, middle, lc⟩ := leftAnswer
      simp only [leftOutcome, TaskStepRep] at ranLeft
      obtain ⟨aUpdated, firstRan, aNextRep⟩ := ranLeft
      let middleEnv := initial.set (.there .here) aUpdated
      have ranRight := secondCorrect middle middleEnv b bRep
      simp only [leftOutcome, bind, Except.bind]
      erw [firstRan]
      cases rightOutcome : runTaskPoll elaboration calls prices b middle with
      | error cause =>
        cases cause <;> simp only [rightOutcome, TaskStepRep, Except.bind] at ranRight ⊢ <;>
          erw [ranRight] <;> rfl
      | ok rightAnswer =>
        obtain ⟨rp, bNext, final, rc⟩ := rightAnswer
        simp only [rightOutcome, TaskStepRep] at ranRight
        obtain ⟨bUpdated, secondRan, bNextRep⟩ := ranRight
        simp only [rightOutcome, Except.bind]
        erw [secondRan]
        let finalEnv := middleEnv.set .here bUpdated
        have lpRep := runTaskPoll_rep elaboration calls prices aRep leftResolved leftOutcome
        have rpRep := runTaskPoll_rep elaboration calls prices bRep rightResolved rightOutcome
        obtain ⟨value, collected, successorRep⟩ := collectJoin_exec (V := V) (l := l) (Λ := Λ) path left right
          (.there .here) .here (.there (.there (.there out))) oracle passes calls final finalEnv
          aNextRep bNextRep lpRep rpRep
        erw [collected]
        cases lp <;> cases rp <;> exact ⟨value, rfl, successorRep⟩

variable {types : TypeResolution} {f : AsyncFn}

/-- The executable traversal records exactly the callees found in the
    elaboration table, preserving the shape of the source future. -/
public inductive PollPlan (elaboration : Elaboration D V Λ types f) : FutureExpr → Type where
  | call (name : String) (args : List Parser.SExpr) (callee : AwaitedCall D V Λ types name)
      (known : elaboration.callee name = some callee) : PollPlan elaboration (.call name args)
  | join : PollPlan elaboration left → PollPlan elaboration right → PollPlan elaboration (.join left right)

@[expose] public def PollPlan.resolve (elaboration : Elaboration D V Λ types f) :
    (future : FutureExpr) → Option (PollPlan elaboration future)
  | .call name args =>
    match found : elaboration.callee name with
    | none => none
    | some callee => some (.call name args callee found)
  | .join left right => do
    let first ← resolve elaboration left
    let second ← resolve elaboration right
    pure (.join first second)

public theorem PollPlan.resolve_complete (elaboration : Elaboration D V Λ types f) (future : FutureExpr)
    (resolved : ResolvedFuture elaboration future) :
    ∃ plan, PollPlan.resolve elaboration future = some plan := by
  induction future with
  | call name args =>
    obtain ⟨callee, known⟩ := resolved
    refine ⟨.call name args callee known, ?_⟩
    unfold PollPlan.resolve
    split
    · rename_i missing
      rw [known] at missing
      cases missing
    · rename_i actual found
      have equal : actual = callee := Option.some.inj (found.symm.trans known)
      subst actual
      rfl
  | join left right leftIH rightIH =>
    obtain ⟨first, foundFirst⟩ := leftIH resolved.1
    obtain ⟨second, foundSecond⟩ := rightIH resolved.2
    exact ⟨.join first second, by simp only [PollPlan.resolve, foundFirst, foundSecond, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]⟩

public theorem PollPlan.resolved {elaboration : Elaboration D V Λ types f} {future : FutureExpr}
    (plan : PollPlan elaboration future) : ResolvedFuture elaboration future := by
  induction plan with
  | call _ _ callee known => exact ⟨callee, known⟩
  | join _ _ first second => exact ⟨first, second⟩

/-- Recursively generate ordinary G for every finite future tree. -/
@[expose] public def PollPlan.lower {elaboration : Elaboration D V Λ types f} :
    {future : FutureExpr} → PollPlan elaboration future →
    (path : List Nat) → {Γ : Ctx} → Var Γ (taskStorageType types path future) → Stmt D V l Γ Λ Λ
  | _, .call name args callee _, path, _, slot => leafTaskStmt path name args callee slot
  | _, @PollPlan.join _ _ _ _ _ _ left right first second, path, _, slot =>
    joinTaskStmt types path left right slot
      (lower first (0 :: path) (.there .here)) (lower second (1 :: path) .here)

/-- The generated task poll realizes the nested semantic future for
    all typed representations and all actual ordinary call outcomes. -/
public theorem PollPlan.lower_simulates {elaboration : Elaboration D V Λ types f}
    {future : FutureExpr} (plan : PollPlan elaboration future)
    (path : List Nat) (slot : Var Γ (taskStorageType types path future))
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn) (prices : D.Fn → Nat)
    (world : World D) (env : Env D Γ) (task : Task (Value D) (Child D types))
    (represented : TaskRep D types path future task (env.get slot)) :
    TaskStepRep types path future slot env (execStmt oracle passes calls (plan.lower (l := l) path slot) world env)
      (runTaskPoll elaboration calls prices task world) := by
  induction plan generalizing path Γ world task with
  | call name args callee known =>
    exact leafTaskStmt_simulates elaboration path name args callee known slot oracle passes calls prices
      world env task represented
  | @join left right first second firstIH secondIH =>
    exact joinTaskStmt_simulates elaboration path left right first.resolved second.resolved slot
      (first.lower (0 :: path) (.there .here)) (second.lower (1 :: path) .here)
      oracle passes calls prices
      (fun initial context child stored => firstIH (0 :: path) (.there .here) initial context child stored)
      (fun initial context child stored => secondIH (1 :: path) .here initial context child stored)
      world env task represented

end Gabbro.Grammatik.Async.Representation
