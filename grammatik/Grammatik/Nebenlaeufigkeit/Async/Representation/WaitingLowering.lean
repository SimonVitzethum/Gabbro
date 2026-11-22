module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.Construction

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {types : TypeResolution} {f : AsyncFn}
  {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

@[expose] public def activeLeafExpr (types : TypeResolution) (path : List Nat)
    (name : String) (args : List Parser.SExpr) (storage : Expr D Γ Λ (types.childState name)) :
    Expr D Γ Λ (taskStorageType types path (.call name args)) :=
  .case [some (types.childState name), some (types.childResult name)] ⟨0, Nat.zero_lt_succ 1⟩ (.val storage)

/-- Generate the active child case from the resolved constructor. The
    constructor receives just its already evaluated argument bindings. -/
@[expose] public def activeChildExpr {name : String}
    (callee : AwaitedCall D V Λ types name) (path : List Nat) (args : List Parser.SExpr)
    (rename : ∀ {τ : Ty}, Var callee.parameters τ → Var Γ τ) :
    Expr D Γ Λ (taskStorageType types path (.call name args)) :=
  activeLeafExpr types path name args (callee.construct.ren rename)

/-- The emitted leaf constructor produces the exact lazy child in the
    world reached by the semantic constructor on the typed arguments. -/
public theorem activeChildExpr_rep (elaboration : Elaboration D V Λ types f) (path : List Nat)
    (name : String) (args : List Parser.SExpr) (callee : AwaitedCall D V Λ types name)
    (known : elaboration.callee name = some callee) (arguments : List (Value D))
    (parameters : Env D callee.parameters) (typed : argumentsEnv D callee.parameters arguments = some parameters)
    (world : World D) (env : Env D Γ) (rename : ∀ {τ : Ty}, Var callee.parameters τ → Var Γ τ)
    (agrees : parameters.AgreesUnder env rename) :
    let actual := evaluateExpression (activeChildExpr callee path args rename) world env
    let model := constructChild elaboration name arguments world
    TaskRep D types path (.call name args) (.leaf model.1) actual.1 ∧
      actual.2.1 = model.2.1 ∧ actual.2.2 = 1 + model.2.2 := by
  intro actual model
  have preserved := callee.construct.ren_sound rename
  have exactStorage := preserved.2.2 (world.lese Λ callee.construct.orte)
    (world.lese Λ callee.construct.orte) parameters env agrees
  have computed := constructChild_resolved elaboration name callee known arguments parameters typed world
  change TaskRep D types path (.call name args) (.leaf (constructChild elaboration name arguments world).1)
      (evaluateExpression (activeChildExpr callee path args rename) world env).1 ∧
    (evaluateExpression (activeChildExpr callee path args rename) world env).2.1 =
      (constructChild elaboration name arguments world).2.1 ∧
    (evaluateExpression (activeChildExpr callee path args rename) world env).2.2 =
      1 + (constructChild elaboration name arguments world).2.2
  rw [computed]
  simp only [activeChildExpr, activeLeafExpr, evaluateExpression, Expr.orte, NutzlastExpr.orte, preserved.1,
    eval, evalNutz, exactStorage, kostenExpr, kostenNutz, preserved.2.1]
  refine ⟨.callActive path name args _, ?_, ?_⟩ <;> first | trivial | rfl

/-- Combine the two typed child slots of a generated join in source order. -/
@[expose] public def joinChildrenExpr (types : TypeResolution) (path : List Nat) (left right : FutureExpr)
    (first : Expr D Γ Λ (taskStorageType types (0 :: path) left))
    (second : Expr D Γ Λ (taskStorageType types (1 :: path) right)) :
    Expr D Γ Λ (taskStorageType types path (.join left right)) :=
  let pair := Ty.prod (types.recordName (4 :: path))
    [taskStorageType types (0 :: path) left, taskStorageType types (1 :: path) right]
  .case [some pair, some (taskResultType types path (.join left right))] ⟨0, Nat.zero_lt_succ 1⟩
    (.val (.prod (types.recordName (4 :: path)) (.cons first (.cons second .nil))))

public theorem joinChildrenExpr_rep (types : TypeResolution) (path : List Nat) (left right : FutureExpr)
    (first : Expr D Γ Λ (taskStorageType types (0 :: path) left))
    (second : Expr D Γ Λ (taskStorageType types (1 :: path) right))
    (entry world : World D) (env : Env D Γ) (l r : Task (Value D) (Child D types))
    (leftRep : TaskRep D types (0 :: path) left l (eval entry first world env))
    (rightRep : TaskRep D types (1 :: path) right r (eval entry second world env)) :
    TaskRep D types path (.join left right) (.join l r)
      (eval entry (joinChildrenExpr types path left right first second) world env) :=
  .joinActive leftRep rightRep

/-- Enter Waiting by evaluating the child constructor once and retaining
    just the live continuation frame. This block never polls the child. -/
@[expose] public def lowerAwaitConstruction (types : TypeResolution) (f : AsyncFn) (tag : Nat)
    {destination : String} {future : FutureExpr} {boundary : Boundary} {rest : List Command}
    (command : f.body.drop tag = Command.await destination future boundary :: rest)
    (saved : Var Γ (frameType types f)) (state : Var Γ (stateType types f))
    (construct : Expr D Γ Λ (taskStorageType types [tag] future)) : Block D V l Γ Λ Λ :=
  evaluateBlock construct state (waitingExpr types f tag command
    (trimFrameExpr types f (liveAt f (.waiting tag future)) (.there saved)) (.var .here))

/-- With the exact lazy child storage, the generated Waiting block
    preserves the modeled frame, resource inventory and construction reads. -/
public theorem lowerAwaitConstruction_rep (inventory : Inventory D) (tag : Nat)
    {destination : String} {future : FutureExpr} {boundary : Boundary} {rest : List Command}
    (command : f.body.drop tag = Command.await destination future boundary :: rest)
    (saved : Var Γ (frameType types f)) (state : Var Γ (stateType types f))
    (construct : Expr D Γ Λ (taskStorageType types [tag] future))
    (oracle : Orakel D) (passes : Nat) (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ) (frame : Frame (Value D)) (task : Task (Value D) (Child D types))
    (represented : FrameRep D types f (.running tag) frame (env.get saved))
    (current : MarksRep inventory (.running tag) (.running (Child := Child D types) tag frame))
    (sameInventory : inventory.owned (.waiting tag future) = inventory.owned (.running tag))
    (child : TaskRep D types [tag] future task (evaluateExpression construct world env).1) :
    let answer := evaluateExpression construct world env
    ∃ value, execBlock oracle passes calls (lowerAwaitConstruction (V := V) (l := l) types f tag command
        saved state construct) world env = .ok answer.2.1 (env.set state value) ∧
      Inv f types inventory (.waiting tag frame task) value ∧
      encode D types f (.waiting tag frame task) = some value := by
  intro answer
  have retained : liveAt f (.waiting tag future) ⊆ liveAt f (.running tag) := by
    simp only [liveAt, command, liveBefore]
    intro name member
    exact List.mem_append_right _ member
  let extended : Env D (taskStorageType types [tag] future :: Γ) := .cons answer.1 env
  let storage : Expr D (taskStorageType types [tag] future :: Γ) Λ (frameType types f) :=
    trimFrameExpr types f (liveAt f (.waiting tag future)) (.there saved)
  let successor := waitingExpr types f tag command storage (.var .here)
  obtain ⟨noFrameReads, trimmed⟩ := trimFrameExpr_rep (Λ := Λ) (.there saved) retained
    answer.2.1 answer.2.1 extended represented.slots
  change storage.orte = [] at noFrameReads
  have silent : successor.orte = [] := by
    change (waitingExpr types f tag command storage (Expr.var .here)).orte = []
    simp only [waitingExpr_reads, noFrameReads, Expr.orte, List.nil_append]
  let frameValue := eval answer.2.1 storage answer.2.1 extended
  let value := waitingValue D types f tag command frameValue answer.1
  have savedFrame : FrameRep D types f (.waiting tag future) frame frameValue :=
    ⟨trimmed, fun name member => represented.declared name (retained member), represented.unique⟩
  have owned : MarksRep inventory (.waiting tag future) (.waiting tag frame task) :=
    by simpa only [MarksRep, State.marks, sameInventory] using current
  have invariant := waitingValue_inv types f inventory tag command frame task frameValue answer.1 savedFrame child owned
  have execution := evaluateBlock_exec (V := V) (l := l) oracle passes calls construct state successor world env
  have noRead (current : World D) : current.lese Λ [] = current := rfl
  simp only [silent, noRead] at execution
  change execBlock oracle passes calls (lowerAwaitConstruction (V := V) (l := l) types f tag command
      saved state construct) world env =
    .ok answer.2.1 (env.set state (eval answer.2.1 successor answer.2.1 extended)) at execution
  have exactValue : eval answer.2.1 successor answer.2.1 extended = value :=
    waitingExpr_eval types f tag command storage (.var .here) answer.2.1 answer.2.1 extended
  rw [exactValue] at execution
  exact ⟨value, execution, invariant, inv_encoded f types inventory _ value invariant⟩

/-- Once arguments have been evaluated, a leaf await uses its resolved
    lazy constructor and enters the model's Waiting state in one G block. -/
public theorem lowerAwaitLeaf_rep (elaboration : Elaboration D V Λ types f) (inventory : Inventory D)
    (tag : Nat) (destination name : String) (args : List Parser.SExpr) (boundary : Boundary) (rest : List Command)
    (command : f.body.drop tag = Command.await destination (.call name args) boundary :: rest)
    (callee : AwaitedCall D V Λ types name) (known : elaboration.callee name = some callee)
    (arguments : List (Value D)) (parameters : Env D callee.parameters)
    (typed : argumentsEnv D callee.parameters arguments = some parameters)
    (saved : Var Γ (frameType types f)) (state : Var Γ (stateType types f))
    (world : World D) (env : Env D Γ) (rename : ∀ {τ : Ty}, Var callee.parameters τ → Var Γ τ)
    (agrees : parameters.AgreesUnder env rename) (frame : Frame (Value D))
    (represented : FrameRep D types f (.running tag) frame (env.get saved))
    (current : MarksRep inventory (.running tag) (.running (Child := Child D types) tag frame))
    (sameInventory : inventory.owned (.waiting tag (.call name args)) = inventory.owned (.running tag))
    (oracle : Orakel D) (passes : Nat) (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn) :
    let model := constructChild elaboration name arguments world
    let target := State.waiting (Value := Value D) tag frame (Task.leaf model.1)
    ∃ value, execBlock oracle passes calls
        (lowerAwaitConstruction (V := V) (l := l) types f tag command saved state (activeChildExpr callee [tag] args rename))
          world env = .ok model.2.1 (env.set state value) ∧
      Inv f types inventory target value ∧ encode D types f target = some value := by
  intro model target
  let construct := activeChildExpr callee [tag] args rename
  obtain ⟨child, sameWorld, _⟩ := activeChildExpr_rep elaboration [tag] name args callee known arguments parameters
    typed world env rename agrees
  obtain ⟨value, executed, invariant, encoded⟩ := lowerAwaitConstruction_rep (V := V) (l := l)
    inventory tag command saved state construct oracle passes calls world env frame (.leaf model.1) represented
    current sameInventory child
  change (evaluateExpression construct world env).2.1 = model.2.1 at sameWorld
  rw [sameWorld] at executed
  exact ⟨value, executed, invariant, encoded⟩

@[expose] public def leafPollArguments {name : String} (callee : AwaitedCall D V Λ types name)
    (child : Var Γ (types.childState name)) : Args D Γ Λ (D.params callee.poll) :=
  callee.pollParams.symm ▸ Args.cons (.var child) Args.nil

public theorem leafPollArguments_eval {name : String} (callee : AwaitedCall D V Λ types name)
    (child : Var Γ (types.childState name)) (entry world : World D) (env : Env D Γ) :
    (leafPollArguments callee child).orte = [] ∧
      evalArgs entry (leafPollArguments callee child) world env = pollEnvironment callee (env.get child) := by
  have lift {params params' : Ctx} (same : params = params') (args : Args D Γ Λ params) :
      (same ▸ args : Args D Γ Λ params').orte = args.orte ∧
      evalArgs entry (same ▸ args) world env = (same ▸ evalArgs entry args world env) := by
    cases same
    exact ⟨rfl, rfl⟩
  exact lift callee.pollParams.symm (.cons (.var child) .nil)

/-- The Pending branch keeps the old continuation frame and saves the
    actual child returned by the poll, rather than the old child input. -/
@[expose] public def leafPendingExpr (types : TypeResolution) (f : AsyncFn) (tag : Nat)
    {destination name : String} {args : List Parser.SExpr} {boundary : Boundary} {rest : List Command}
    (command : f.body.drop tag = Command.await destination (.call name args) boundary :: rest)
    (saved : Var Γ (frameType types f)) :
    Expr D (types.childState name :: .sum [some (types.childResult name), some (types.childState name)] :: Γ)
      Λ (stateType types f) :=
  waitingExpr types f tag command (.var (.there (.there saved)))
    (activeLeafExpr types [tag] name args (.var .here))

@[expose] public def lowerLeafPoll (types : TypeResolution) (f : AsyncFn) (tag : Nat)
    {destination name : String} {args : List Parser.SExpr} {boundary : Boundary} {rest : List Command}
    (command : f.body.drop tag = Command.await destination (.call name args) boundary :: rest)
    (callee : AwaitedCall D V Λ types name) (child : Var Γ (types.childState name)) (saved : Var Γ (frameType types f))
    (state : Var Γ (stateType types f)) (finished : Var Γ .bool)
    (ready : Expr D (types.childResult name :: .sum [some (types.childResult name), some (types.childState name)] :: Γ)
      Λ (stateType types f)) : Block D V l Γ Λ Λ :=
  childPollBlock callee (leafPollArguments callee child)
    (pollAnswerArms state finished ready (leafPendingExpr types f tag command saved))

/-- In the Pending branch both the ordinary G poll and the semantic
    await keep the exact updated child and the same owned resources. -/
public theorem lowerLeafPoll_pending (elaboration : Elaboration D V Λ types f) (inventory : Inventory D)
    (tag : Nat) {destination name : String} {args : List Parser.SExpr} {boundary : Boundary} {rest : List Command}
    (command : f.body.drop tag = Command.await destination (.call name args) boundary :: rest)
    (callee : AwaitedCall D V Λ types name) (known : elaboration.callee name = some callee)
    (child : Var Γ (types.childState name)) (saved : Var Γ (frameType types f))
    (state : Var Γ (stateType types f)) (finished : Var Γ .bool)
    (ready : Expr D (types.childResult name :: .sum [some (types.childResult name), some (types.childState name)] :: Γ)
      Λ (stateType types f)) (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn) (prices : D.Fn → Nat)
    (world after : World D) (env : Env D Γ) (frame : Frame (Value D))
    (stored : FrameRep D types f (.waiting tag (.call name args)) frame (env.get saved))
    (owned : MarksRep inventory (.waiting tag (.call name args)) (.waiting tag frame (.leaf (.active name (env.get child)))))
    (answer : ErgVal D (D.erg callee.poll)) (updated : Wert D (types.childState name))
    (returned : calls callee.poll world (pollEnvironment callee (env.get child)) = .ok after answer)
    (pending : ergWert callee.pollResult answer = pendingAnswer D (types.childResult name) (types.childState name) updated) :
    let target := State.waiting (Value := Value D) tag frame (.leaf (.active name updated))
    runWaitingPoll elaboration calls prices tag destination frame (.leaf (.active name (env.get child))) world =
        .ok (.pending, target, after, prices callee.poll + 1) ∧
    ∃ value, execBlock oracle passes calls (lowerLeafPoll (V := V) (l := l) types f tag command
        callee child saved state finished ready) world env = .ok after ((env.set state value).set finished true) ∧
      Inv f types inventory target value ∧ encode D types f target = some value := by
  intro target
  constructor
  · simp only [runWaitingPoll, runTaskPoll, pollTaskWith, known, runChildPoll, returned, decodeChildOutcome,
      pending, decodePollAnswer, pendingAnswer, bind, Except.bind, Except.pure, pure, waitingReply] <;> rfl
  let arguments := leafPollArguments callee child
  let arm := leafPendingExpr (Λ := Λ) types f tag command saved
  obtain ⟨silentArgs, exactArgs⟩ := leafPollArguments_eval callee child world world env
  have noRead (current : World D) : current.lese Λ [] = current := rfl
  have called : calls callee.poll (world.lese Λ arguments.orte)
      (evalArgs (world.lese Λ arguments.orte) arguments (world.lese Λ arguments.orte) env) = .ok after answer := by
    simp only [arguments, silentArgs, noRead, exactArgs]
    exact returned
  have executed := childPollBlock_exec_return callee arguments
    (pollAnswerArms (V := V) (l := l) state finished ready arm) oracle passes calls world after env answer called
  dsimp only at executed
  rw [pending, pollAnswerArms_pending] at executed
  have silent : arm.orte = [] := by
    change (waitingExpr types f tag command (Expr.var (.there (.there saved)))
      (activeLeafExpr types [tag] name args (Expr.var .here)) :
      Expr D (types.childState name :: .sum [some (types.childResult name), some (types.childState name)] :: Γ)
        Λ (stateType types f)).orte = []
    rw [waitingExpr_reads]
    rfl
  simp only [silent, noRead] at executed
  let current : Wert D (taskStorageType types [tag] (.call name args)) :=
    readyAnswer D (types.childState name) (types.childResult name) updated
  let value := waitingValue D types f tag command (env.get saved) current
  have content := waitingExpr_eval (Λ := Λ) types f tag command (.var (.there (.there saved)))
    (activeLeafExpr types [tag] name args (.var .here)) after after
    (.cons updated (.cons (pendingAnswer D (types.childResult name) (types.childState name) updated) env))
  change eval after arm after (.cons updated (.cons
    (pendingAnswer D (types.childResult name) (types.childState name) updated) env)) = value at content
  rw [content] at executed
  have invariant : Inv f types inventory target value := waitingValue_inv types f inventory tag command frame _ _ current
    stored (.callActive [tag] name args updated) owned
  exact ⟨value, executed, invariant, inv_encoded f types inventory _ value invariant⟩

@[expose] public def readyBindingFrame (types : TypeResolution) (f : AsyncFn) (next : Phase)
    (destination : String) (sourceType : Parser.STyp) {actual : Ty} (same : actual = types.ordinary sourceType)
    (binding : (f.params ++ f.fields).lookup destination = some sourceType) (saved : Var Γ (frameType types f)) :
    Expr D (actual :: Γ) Λ (frameType types f) :=
  Eq.mp (congrArg (fun ty => Expr D (ty :: Γ) Λ (frameType types f)) same.symm)
    (bindingFrameExpr types f next destination sourceType binding saved)

public theorem readyBindingFrame_rep {before next : Phase} (destination : String) (sourceType : Parser.STyp)
    {actual : Ty} (same : actual = types.ordinary sourceType)
    (binding : (f.params ++ f.fields).lookup destination = some sourceType)
    (retained : ∀ name ∈ liveAt f next, name ≠ destination → name ∈ liveAt f before)
    (saved : Var Γ (frameType types f)) (world : World D) (env : Env D Γ) (result : Wert D actual)
    (frame : Frame (Value D)) (represented : FrameRep D types f before frame (env.get saved)) :
    let expression : Expr D (actual :: Γ) Λ (frameType types f) :=
      readyBindingFrame types f next destination sourceType same binding saved
    expression.orte = [] ∧ FrameRep D types f next (save frame destination (Value.typed actual result))
      (eval world expression world (.cons result env)) := by
  subst actual
  exact ⟨bindingFrameExpr_reads types f next destination sourceType binding saved,
    bindingFrameExpr_rep (Λ := Λ) destination sourceType binding retained saved world world
      (.cons result env) frame represented⟩

/-- The Ready arm saves its typed result, clears dead slots and advances
    to the selected Running case. -/
@[expose] public def leafReadyExpr (types : TypeResolution) (f : AsyncFn) (tag : Nat)
    (within : tag + 1 ≤ f.body.length) (destination name : String) (sourceType : Parser.STyp)
    (same : types.childResult name = types.ordinary sourceType)
    (binding : (f.params ++ f.fields).lookup destination = some sourceType) (saved : Var Γ (frameType types f)) :
    Expr D (types.childResult name :: .sum [some (types.childResult name), some (types.childState name)] :: Γ)
      Λ (stateType types f) :=
  runningExpr types f (tag + 1) within
    (readyBindingFrame types f (.running (tag + 1)) destination sourceType same binding (.there saved))

/-- The real Ready result is the value in the semantic successor and
    in its generated frame. The ordinary call's returned world is kept. -/
public theorem lowerLeafPoll_ready (elaboration : Elaboration D V Λ types f) (inventory : Inventory D)
    (tag : Nat) (within : tag + 1 ≤ f.body.length) (destination name : String)
    {args : List Parser.SExpr} {boundary : Boundary} {rest : List Command}
    (command : f.body.drop tag = Command.await destination (.call name args) boundary :: rest)
    (sourceType : Parser.STyp) (same : types.childResult name = types.ordinary sourceType)
    (binding : (f.params ++ f.fields).lookup destination = some sourceType)
    (callee : AwaitedCall D V Λ types name) (known : elaboration.callee name = some callee)
    (child : Var Γ (types.childState name)) (saved : Var Γ (frameType types f))
    (state : Var Γ (stateType types f)) (finished : Var Γ .bool) (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn) (prices : D.Fn → Nat)
    (world after : World D) (env : Env D Γ) (frame : Frame (Value D))
    (stored : FrameRep D types f (.waiting tag (.call name args)) frame (env.get saved))
    (owned : MarksRep inventory (.waiting tag (.call name args)) (.waiting tag frame (.leaf (.active name (env.get child)))))
    (sameInventory : inventory.owned (.running (tag + 1)) = inventory.owned (.waiting tag (.call name args)))
    (answer : ErgVal D (D.erg callee.poll)) (result : Wert D (types.childResult name))
    (returned : calls callee.poll world (pollEnvironment callee (env.get child)) = .ok after answer)
    (completed : ergWert callee.pollResult answer = readyAnswer D (types.childResult name) (types.childState name) result) :
    let target := State.running (Child := Child D types) (tag + 1)
      (save frame destination (Value.typed (types.childResult name) result))
    runWaitingPoll elaboration calls prices tag destination frame (.leaf (.active name (env.get child))) world =
        .ok (.next, target, after, prices callee.poll + 1) ∧
    ∃ value, execBlock oracle passes calls (lowerLeafPoll (V := V) (l := l) types f tag command callee child saved
        state finished (leafReadyExpr types f tag within destination name sourceType same binding saved)) world env =
          .ok after (env.set state value) ∧
      Inv f types inventory target value ∧ encode D types f target = some value := by
  intro target
  constructor
  · simp only [runWaitingPoll, runTaskPoll, pollTaskWith, known, runChildPoll, returned, decodeChildOutcome,
      completed, decodePollAnswer, readyAnswer, bind, Except.bind, Except.pure, pure, waitingReply] <;> rfl
  let arguments := leafPollArguments callee child
  let ready := leafReadyExpr (Λ := Λ) types f tag within destination name sourceType same binding saved
  let pending := leafPendingExpr (Λ := Λ) types f tag command saved
  let reply := readyAnswer D (types.childResult name) (types.childState name) result
  obtain ⟨silentArgs, exactArgs⟩ := leafPollArguments_eval callee child world world env
  have noRead (current : World D) : current.lese Λ [] = current := rfl
  have called : calls callee.poll (world.lese Λ arguments.orte)
      (evalArgs (world.lese Λ arguments.orte) arguments (world.lese Λ arguments.orte) env) = .ok after answer := by
    simp only [arguments, silentArgs, noRead, exactArgs]
    exact returned
  have executed := childPollBlock_exec_return callee arguments
    (pollAnswerArms (V := V) (l := l) state finished ready pending) oracle passes calls world after env answer called
  dsimp only at executed
  rw [completed, pollAnswerArms_ready] at executed
  let extended := Env.cons result (.cons reply env)
  let storage : Expr D (types.childResult name :: .sum [some (types.childResult name), some (types.childState name)] :: Γ)
      Λ (frameType types f) :=
    readyBindingFrame types f (.running (tag + 1)) destination sourceType same binding (.there saved)
  obtain ⟨silentFrame, frameRep⟩ := readyBindingFrame_rep (Λ := Λ) destination sourceType same binding
    (await_retains_live tag destination (.call name args) boundary rest command) (.there saved) after
    (.cons reply env) result frame stored
  have silent : ready.orte = [] := (runningExpr_reads types f (tag + 1) within storage).trans silentFrame
  simp only [silent, noRead] at executed
  let nextFrame := eval after storage after extended
  let value := runningValue D types f (tag + 1) within nextFrame
  have content : eval after ready after extended = value :=
    runningExpr_eval types f (tag + 1) within storage after after extended
  change execBlock oracle passes calls (lowerLeafPoll (V := V) (l := l) types f tag command callee child saved
    state finished ready) world env = .ok after (env.set state (eval after ready after extended)) at executed
  rw [content] at executed
  have marks : MarksRep inventory (.running (tag + 1)) target :=
    by simpa only [MarksRep, target, State.marks, sameInventory, save] using owned
  have invariant : Inv f types inventory target value :=
    runningValue_inv types f inventory (tag + 1) within _ nextFrame frameRep marks
  exact ⟨value, executed, invariant, inv_encoded f types inventory _ value invariant⟩

/-- A resolved leaf await simulates the actual poll outcome. Every typed
    successful answer is accounted for, and a failed call propagates its cause. -/
public theorem lowerLeafPoll_simulates (elaboration : Elaboration D V Λ types f) (inventory : Inventory D)
    (tag : Nat) (within : tag + 1 ≤ f.body.length) (destination name : String)
    {args : List Parser.SExpr} {boundary : Boundary} {rest : List Command}
    (command : f.body.drop tag = Command.await destination (.call name args) boundary :: rest)
    (sourceType : Parser.STyp) (same : types.childResult name = types.ordinary sourceType)
    (binding : (f.params ++ f.fields).lookup destination = some sourceType)
    (callee : AwaitedCall D V Λ types name) (known : elaboration.callee name = some callee)
    (child : Var Γ (types.childState name)) (saved : Var Γ (frameType types f))
    (state : Var Γ (stateType types f)) (finished : Var Γ .bool) (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn) (prices : D.Fn → Nat)
    (world : World D) (env : Env D Γ) (frame : Frame (Value D))
    (stored : FrameRep D types f (.waiting tag (.call name args)) frame (env.get saved))
    (owned : MarksRep inventory (.waiting tag (.call name args)) (.waiting tag frame (.leaf (.active name (env.get child)))))
    (sameInventory : inventory.owned (.running (tag + 1)) = inventory.owned (.waiting tag (.call name args))) :
    let ready := leafReadyExpr (Λ := Λ) types f tag within destination name sourceType same binding saved
    let executed := execBlock oracle passes calls (lowerLeafPoll (V := V) (l := l) types f tag command
      callee child saved state finished ready) world env
    match runWaitingPoll elaboration calls prices tag destination frame (.leaf (.active name (env.get child))) world with
    | .error (.inl logic) => executed = .logik logic
    | .error (.inr hardware) => executed = .hardware hardware
    | .ok (event, target, after, _) =>
      ∃ value, executed = .ok after
          (match event with | .pending => (env.set state value).set finished true | _ => env.set state value) ∧
        Inv f types inventory target value ∧ encode D types f target = some value := by
  intro ready executed
  have fails {cause : Logik D ⊕ Hardware D}
      (failed : runChildPoll callee calls prices (env.get child) world = .error cause) :
      executed = (match cause with | .inl logic => .logik logic | .inr hardware => .hardware hardware) := by
    let arguments := leafPollArguments callee child
    obtain ⟨silent, argsEval⟩ := leafPollArguments_eval callee child world world env
    have evaluated : world.lese Λ arguments.orte = world := by
      change world.lese Λ (leafPollArguments callee child).orte = world
      rw [silent]
      rfl
    exact childPollBlock_reports_failure oracle passes calls prices callee arguments
      (pollAnswerArms state finished ready (leafPendingExpr types f tag command saved)) world env (env.get child)
      (by simpa only [evaluated, arguments] using argsEval) (by simpa only [evaluated] using failed)
  cases returned : calls callee.poll world (pollEnvironment callee (env.get child)) with
  | why _ reason => exact keinGrund callee.pollInfallible reason
  | logik logic =>
    simp only [runWaitingPoll, runTaskPoll, pollTaskWith, known, runChildPoll, returned, decodeChildOutcome,
      bind, Except.bind]
    exact fails (by simp only [runChildPoll, returned, decodeChildOutcome])
  | hardware hardware =>
    simp only [runWaitingPoll, runTaskPoll, pollTaskWith, known, runChildPoll, returned, decodeChildOutcome,
      bind, Except.bind]
    exact fails (by simp only [runChildPoll, returned, decodeChildOutcome])
  | ok after answer =>
    generalize converted : ergWert callee.pollResult answer = reply
    obtain ⟨⟨caseTag, bound⟩, payload⟩ := reply
    cases caseTag with
    | zero =>
      obtain ⟨run, proof⟩ := lowerLeafPoll_ready (V := V) (l := l) elaboration inventory tag within destination name
        command sourceType same binding callee known child saved state finished oracle passes calls prices world after
        env frame stored owned sameInventory answer payload returned converted
      rw [run]
      exact proof
    | succ caseTag =>
      cases caseTag with
      | zero =>
        obtain ⟨run, proof⟩ := lowerLeafPoll_pending (V := V) (l := l) elaboration inventory tag command
          callee known child saved state finished ready oracle passes calls prices world after env frame stored owned
          answer payload returned converted
        rw [run]
        exact proof
      | succ caseTag =>
        have invalid : caseTag + 2 < 2 := bound
        omega

end Gabbro.Grammatik.Async.Representation
