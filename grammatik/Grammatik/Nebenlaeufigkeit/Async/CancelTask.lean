module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.JoinLowering
public import Grammatik.Nebenlaeufigkeit.Async.Representation.Dispatch
public import Grammatik.Nebenlaeufigkeit.Async.Representation.Reachability

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {types : TypeResolution} {V : Vertrag D} {Λ : List (Res D)}

/-- A child destructor receives only the typed child state. The owning
    parent releases its resource index after disposing the child tree. -/
public structure ChildDisposer (D : Deklaration) (types : TypeResolution)
    (V : Vertrag D) (resources : List (Res D)) (name : String) where
  function : D.Fn
  parameters : D.params function = [types.childState name]
  contract : RufPasst D V (D.signatur function) resources
  infallible : D.gruende function = 0
  retained : nach D function resources = resources

public inductive TaskDropPlan (D : Deklaration) (types : TypeResolution)
    (V : Vertrag D) (resources : List (Res D)) : FutureExpr → Type where
  | call (name : String) (arguments : List Parser.SExpr) (disposer : ChildDisposer D types V resources name) :
      TaskDropPlan D types V resources (.call name arguments)
  | join {left right : FutureExpr} (first : TaskDropPlan D types V resources left)
      (second : TaskDropPlan D types V resources right) : TaskDropPlan D types V resources (.join left right)

@[expose] public def ChildDisposer.args {name : String} (disposer : ChildDisposer D types V Λ name) (Γ : Ctx) :
    Args D (types.childState name :: Γ) Λ (D.params disposer.function) :=
  disposer.parameters.symm ▸ .cons (.var .here) .nil

@[expose] public def ChildDisposer.lower {name : String} (disposer : ChildDisposer D types V Λ name)
    (Γ : Ctx) (l : Bool) : Stmt D V l (types.childState name :: Γ) Λ Λ :=
  cast (congrArg (Stmt D V l (types.childState name :: Γ) Λ) disposer.retained)
    (.call disposer.function (disposer.args Γ) disposer.contract disposer.infallible)

/-- Cleanup dispatches over the same represented task tree as polling.
    A Ready tag skips its entire subtree, and live children run in order. -/
@[expose] public def TaskDropPlan.lower :
    {future : FutureExpr} → TaskDropPlan D types V Λ future → (path : List Nat) →
    {Γ : Ctx} → {l : Bool} → Var Γ (taskStorageType types path future) → Stmt D V l Γ Λ Λ
  | _, .call _ _ disposer, _, Γ, l, task =>
    .onTag (.var task) (.cons (.cons (disposer.lower Γ l) .nil) (.cons .nil .nil))
  | _, @TaskDropPlan.join _ _ _ _ left right first second, path, _, _, task =>
    .onTag (.var task) (.cons
      (.bind (.prodGet (.var .here) .head)
        (.bind (.prodGet (.var (.there .here)) (.tail .head))
          (.cons (lower first (0 :: path) (.there .here))
            (.cons (lower second (1 :: path) .here) .nil))))
      (.cons .nil .nil))

@[expose] public def ChildDisposer.drop {name : String} (disposer : ChildDisposer D types V Λ name)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (state : Wert D (types.childState name)) (world : World D) : Except (Logik D ⊕ Hardware D) (World D) :=
  match calls disposer.function world (disposer.parameters.symm ▸ Env.cons state .nil) with
  | .ok next _ => .ok next
  | .why _ why => Fin.elim0 (disposer.infallible ▸ why)
  | .logik failure => .error (.inl failure)
  | .hardware failure => .error (.inr failure)

/-- The semantic destructor traverses active children only. A malformed
    state has no corresponding model transition. -/
@[expose] public def TaskDropPlan.run
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn) :
    {future : FutureExpr} → TaskDropPlan D types V Λ future →
    Task (Value D) (Child D types) → World D → Option (Except (Logik D ⊕ Hardware D) (World D))
  | _, _, .ready _, world => some (.ok world)
  | _, .call name _ disposer, .leaf (.active actual storage), world =>
    if same : actual = name then some (disposer.drop calls (same ▸ storage) world) else none
  | _, .join first second, .join left right, world =>
    match run calls first left world with
    | some (.ok between) => run calls second right between
    | other => other
  | _, _, _, _ => none

@[expose] public def dropOutcome {Γ : Ctx} {l : Bool}
    (env : Env D Γ) : Except (Logik D ⊕ Hardware D) (World D) → Ausgang V l Γ
  | .ok after => .ok after env
  | .error (.inl failure) => .logik failure
  | .error (.inr failure) => .hardware failure

private theorem ChildDisposer.args_value {name : String} (disposer : ChildDisposer D types V Λ name)
    {Γ : Ctx} (world : World D) (env : Env D Γ) (state : Wert D (types.childState name)) :
    (disposer.args Γ).orte = [] ∧
    evalArgs world (disposer.args Γ) world (.cons state env) = disposer.parameters.symm ▸ Env.cons state .nil := by
  have castArgs {input : Ctx} (parameters : input = [types.childState name]) :
      let arguments : Args D (types.childState name :: Γ) Λ input :=
        parameters.symm ▸ .cons (.var .here) .nil
      arguments.orte = [] ∧
        evalArgs world arguments world (.cons state env) = parameters.symm ▸ Env.cons state .nil := by
    subst input
    exact ⟨rfl, rfl⟩
  exact castArgs disposer.parameters

private theorem ChildDisposer.lower_exec {name : String} (disposer : ChildDisposer D types V Λ name)
    {Γ : Ctx} {l : Bool} (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ) (state : Wert D (types.childState name)) :
    execStmt oracle passes calls (disposer.lower Γ l) world (.cons state env) =
      dropOutcome (.cons state env) (disposer.drop calls state world) := by
  have castExec {endResources : List (Res D)} (equal : endResources = Λ)
      (stmt : Stmt D V l (types.childState name :: Γ) Λ endResources) :
      execStmt oracle passes calls (cast (congrArg (Stmt D V l (types.childState name :: Γ) Λ) equal) stmt)
        world (.cons state env) = execStmt oracle passes calls stmt world (.cons state env) := by
    subst endResources
    rfl
  unfold ChildDisposer.lower
  rw [castExec disposer.retained]
  obtain ⟨reads, args⟩ := disposer.args_value world env state
  have noReads : world.lese Λ [] = world := by cases world; rfl
  simp only [execStmt, reads, noReads, args, ChildDisposer.drop]
  cases calls disposer.function world (disposer.parameters.symm ▸ Env.cons state .nil) with
  | ok => rfl
  | why _ reason => exact Fin.elim0 (disposer.infallible ▸ reason)
  | logik => rfl
  | hardware => rfl

/-- Cancellation of every represented task uses exactly its typed child
    destructors, skips completed branches, and propagates the first
    failure with the same world transition as the model. -/
public theorem TaskDropPlan.lower_simulates {future : FutureExpr} (plan : TaskDropPlan D types V Λ future)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn) :
    ∀ (path : List Nat) {Γ : Ctx} {l : Bool} (slot : Var Γ (taskStorageType types path future))
      (world : World D) (env : Env D Γ) {task : Task (Value D) (Child D types)}
      {stored : Wert D (taskStorageType types path future)},
      TaskRep D types path future task stored → env.get slot = stored →
      ∃ outcome, plan.run calls task world = some outcome ∧
        execStmt oracle passes calls (plan.lower path (l := l) slot) world env = dropOutcome env outcome := by
  induction plan with
  | call name arguments disposer =>
    intro path Γ l slot world env task stored represented exactState
    cases represented with
    | callReady typed =>
      refine ⟨.ok world, rfl, ?_⟩
      exact storedTag_cached oracle passes calls slot (.cons (disposer.lower Γ l) .nil) .nil
        world env _ exactState
    | callActive _ _ _ state =>
      refine ⟨disposer.drop calls state world, by simp only [TaskDropPlan.run, dite_eq_left rfl]; rfl, ?_⟩
      unfold TaskDropPlan.lower
      erw [storedTag_active oracle passes calls slot (.cons (disposer.lower Γ l) .nil) .nil
        world env state exactState]
      simp only [execBlock]
      erw [ChildDisposer.lower_exec disposer oracle passes calls world env state]
      cases disposer.drop calls state world with
      | ok => rfl
      | error failure => cases failure <;> rfl
  | @join left right first second firstIH secondIH =>
    intro path Γ l slot world env task stored represented exactState
    let firstStmt : Stmt D V l (JoinCtx types path left right Γ) Λ Λ :=
      first.lower (0 :: path) (.there .here)
    let secondStmt : Stmt D V l (JoinCtx types path left right Γ) Λ Λ :=
      second.lower (1 :: path) .here
    let live : Block D V l (taskActiveType types path (.join left right) :: Γ) Λ Λ :=
      .bind (.prodGet (.var .here) .head)
        (.bind (.prodGet (.var (.there .here)) (.tail .head)) (.cons firstStmt (.cons secondStmt .nil)))
    cases represented with
    | joinReady typed =>
      exact ⟨.ok world, rfl, storedTag_cached oracle passes calls slot live .nil world env _ exactState⟩
    | joinActive leftRep rightRep =>
      rename_i leftTask rightTask leftValue rightValue
      let loaded : Env D (JoinCtx types path left right Γ) :=
        .cons rightValue (.cons leftValue (.cons (leftValue, rightValue, ()) env))
      have began := storedTag_active oracle passes calls slot live .nil
        world env (leftValue, rightValue, ()) exactState
      have restored :
          execStmt oracle passes calls ((TaskDropPlan.join first second).lower path (l := l) slot) world env =
          (((execBlock oracle passes calls (.cons firstStmt (.cons secondStmt .nil)) world loaded).schrumpf).schrumpf).schrumpf := by
        exact began.trans rfl
      obtain ⟨firstOutcome, modelFirst, firstRun⟩ :=
        firstIH (0 :: path) (l := l) (.there .here) world loaded leftRep rfl
      change execStmt oracle passes calls firstStmt world loaded = _ at firstRun
      cases firstOutcome with
      | error failure =>
        refine ⟨.error failure, ?_, ?_⟩
        · simp only [TaskDropPlan.run, modelFirst]
        · rw [restored]
          simp only [execBlock, firstRun]
          cases failure <;> rfl
      | ok between =>
        obtain ⟨secondOutcome, modelSecond, secondRun⟩ :=
          secondIH (1 :: path) (l := l) .here between loaded rightRep rfl
        change execStmt oracle passes calls secondStmt between loaded = _ at secondRun
        refine ⟨secondOutcome, ?_, ?_⟩
        · simpa only [TaskDropPlan.run, modelFirst] using modelSecond
        · rw [restored]
          simp only [execBlock, firstRun, dropOutcome, secondRun]
          cases secondOutcome with
          | ok => rfl
          | error failure => cases failure <;> rfl

/-- The generated waiting arm reads the child from the actual saved
    record. The saved continuation frame remains available for release. -/
@[expose] public def TaskDropPlan.waitingBlock {future : FutureExpr} (plan : TaskDropPlan D types V Λ future)
    (function : AsyncFn) (tag : Nat) {Γ : Ctx} {l : Bool} :
    Block D V l (phaseType types function (.waiting tag future) :: Γ) Λ Λ :=
  .bind (.prodGet (.var .here) (.tail .head)) (.cons (plan.lower [tag] .here) .nil)

public theorem TaskDropPlan.waitingBlock_simulates {future : FutureExpr} (plan : TaskDropPlan D types V Λ future)
    (function : AsyncFn) (tag : Nat) {Γ : Ctx} {l : Bool}
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (before : World D) (env : Env D Γ) (saved : Wert D (frameType types function))
    {task : Task (Value D) (Child D types)} {child : Wert D (taskStorageType types [tag] future)}
    (represented : TaskRep D types [tag] future task child) :
    ∃ outcome, plan.run calls task before = some outcome ∧
      (execBlock oracle passes calls (plan.waitingBlock function tag (l := l))
        before (.cons (saved, child, ()) env)).schrumpf = dropOutcome env outcome := by
  let stored : Env D (phaseType types function (.waiting tag future) :: Γ) :=
    .cons (saved, child, ()) env
  obtain ⟨outcome, dropped, executed⟩ :=
    plan.lower_simulates oracle passes calls [tag] (l := l) .here before (.cons child stored) represented rfl
  refine ⟨outcome, dropped, ?_⟩
  have noReads : before.lese Λ [] = before := by cases before; rfl
  simp only [TaskDropPlan.waitingBlock, execBlock, Expr.orte, noReads, eval, Env.get, prodGetW]
  erw [executed]
  cases outcome with
  | ok => rfl
  | error failure => cases failure <;> rfl

@[expose] public def TaskDropPlan.resolve
    (resolve : (name : String) → Except String (ChildDisposer D types V Λ name)) :
    (future : FutureExpr) → Except String (TaskDropPlan D types V Λ future)
  | .call name args => .call name args <$> resolve name
  | .join first second => do
    pure (.join (← TaskDropPlan.resolve resolve first) (← TaskDropPlan.resolve resolve second))

@[expose] public def PhaseDropPlan (D : Deklaration) (types : TypeResolution)
    (V : Vertrag D) (Λ : List (Res D)) : Phase → Type
  | .waiting _ future => TaskDropPlan D types V Λ future
  | _ => Unit

@[expose] public def PhaseDropPlan.resolve
    (resolve : (name : String) → Except String (ChildDisposer D types V Λ name)) :
    (phase : Phase) → Except String (PhaseDropPlan D types V Λ phase)
  | .waiting _ future => TaskDropPlan.resolve resolve future
  | .cancelled | .completed | .running _ => pure ()

@[expose] public def PhaseDropPlan.lower (f : AsyncFn) {Γ : Ctx} {l : Bool} :
    {phase : Phase} → PhaseDropPlan D types V Λ phase →
      Block D V l (phaseType types f phase :: Γ) Λ Λ
  | .waiting tag _, plan => plan.waitingBlock f tag
  | .cancelled, _ | .completed, _ | .running _, _ => .nil

@[expose] public def PhaseDropPlan.run
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn) :
    {phase : Phase} → PhaseDropPlan D types V Λ phase →
      State (Value D) (Child D types) → World D → Option (Except (Logik D ⊕ Hardware D) (World D))
  | .waiting tag _, plan, .waiting position _ task, world =>
    if position = tag then plan.run calls task world else none
  | .waiting .., _, _, _ => none
  | .cancelled, _, .cancelled, world | .completed, _, .completed .., world => some (.ok world)
  | .running tag, _, .running position _, world =>
    if position = tag then some (.ok world) else none
  | _, _, _, _ => none

private theorem phaseDrop_exec {f : AsyncFn} {phase : Phase} {Γ : Ctx} {l : Bool}
    (plan : PhaseDropPlan D types V Λ phase) (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ)
    {source : State (Value D) (Child D types)} {value : Wert D (phaseType types f phase)}
    (represented : PhaseRep D types f phase source value) :
    ∃ outcome, plan.run calls source world = some outcome ∧
      (execBlock oracle passes calls (plan.lower f (l := l)) world (.cons value env)).schrumpf =
        dropOutcome env outcome := by
  cases represented with
  | cancelled | completed => exact ⟨.ok world, rfl, rfl⟩
  | running =>
    exact ⟨.ok world, by simp only [PhaseDropPlan.run, if_pos rfl], rfl⟩
  | waiting tag future frame task saved child _ childRep =>
    simpa only [PhaseDropPlan.run, PhaseDropPlan.lower, if_pos rfl] using
      (TaskDropPlan.waitingBlock_simulates plan f tag (l := l) oracle passes calls world env saved childRep)

@[expose] public def resolveDropTable (f : AsyncFn)
    (resolve : (name : String) → Except String (ChildDisposer D types V Λ name)) :
    Except String ((i : Fin (phases f).length) → PhaseDropPlan D types V Λ ((phases f).get i)) :=
  Parser.sammle (phases f).length (fun i => PhaseDropPlan D types V Λ ((phases f).get i))
    (fun i => PhaseDropPlan.resolve resolve ((phases f).get i))

@[expose] public def dropChildren {f : AsyncFn} {Γ : Ctx} {l : Bool}
    (table : (i : Fin (phases f).length) → PhaseDropPlan D types V Λ ((phases f).get i))
    (state : Var Γ (stateType types f)) : Stmt D V l Γ Λ Λ :=
  phaseDispatch types f state (fun i => (table i).lower f)

/-- A cancellation dispatch reads the actual encoded state and runs only
    the cleanup of that phase. This covers all await sites and join trees. -/
public theorem dropChildren_simulates {f : AsyncFn} {Γ : Ctx} {l : Bool}
    (table : (i : Fin (phases f).length) → PhaseDropPlan D types V Λ ((phases f).get i))
    (inventory : Inventory D) (state : Var Γ (stateType types f))
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ) (source : State (Value D) (Child D types))
    (represented : Inv f types inventory source (env.get state)) :
    ∃ (index : Fin (phases f).length) (value : Wert D (phaseType types f ((phases f).get index))) outcome,
      PhaseRep D types f ((phases f).get index) source value ∧
      MarksRep inventory ((phases f).get index) source ∧
      (table index).run calls source world = some outcome ∧
      execStmt oracle passes calls (dropChildren (l := l) table state) world env = dropOutcome env outcome := by
  obtain ⟨index, value, exactPhase, owners, selected⟩ :=
    phaseDispatch_selects types f inventory state (fun i => (table i).lower f (l := l))
      oracle passes calls world env source represented
  obtain ⟨outcome, ran, executed⟩ := phaseDrop_exec (table index) oracle passes calls world env exactPhase
  exact ⟨index, value, outcome, exactPhase, owners, ran, selected.trans executed⟩

end Gabbro.Grammatik.Async.Representation
