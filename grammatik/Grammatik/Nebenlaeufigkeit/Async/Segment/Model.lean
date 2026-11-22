module

public import Grammatik.Nebenlaeufigkeit.Async.Segment.Elaboration

namespace Gabbro.Grammatik.Async.Segment

variable {D : Deklaration} {V : Vertrag D} {Λ : List (Res D)}
  {types : TypeResolution} {f : AsyncFn}

/-- Normal-call evidence is user logic about the ordinary call environment,
    separate from the elaborator interface. It records the ACTUAL successful
    call, rather than postulating an async execution rule. A failure cannot
    supply this evidence. The present total semantic Model is used only
    under this explicit normal-call duty. -/
public abbrev PollRuns (elaboration : Elaboration D V Λ types f)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn) :=
  ∀ name (callee : AwaitedCall D V Λ types name), elaboration.callee name = some callee →
    ∀ (world : World D) (storage : Wert D (types.childState name)),
    { answer : World D × ErgVal D (D.erg callee.poll) //
      calls callee.poll world (pollEnvironment callee storage) =
        RufAusgang.ok answer.1 answer.2 }

/-- Interpret the two typed answers of an ordinary child poll. -/
@[expose] public def decodePollAnswer (D : Deklaration) (types : TypeResolution)
    (name : String) (previous : Wert D (types.childState name)) :
    Wert D (Ty.sum [some (types.childResult name), some (types.childState name)]) →
      Poll (Value D) × Child D types
  | ⟨⟨0, _⟩, result⟩ =>
      (Poll.ready (Value.typed (types.childResult name) result), Child.active name previous)
  | ⟨⟨1, _⟩, updated⟩ => (Poll.pending, Child.active name updated)
  | ⟨⟨n + 2, impossible⟩, _⟩ =>
      (Nat.not_lt_zero n
        (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ impossible))).elim

@[expose] public def decodeChildOutcome {name : String} (callee : AwaitedCall D V Λ types name)
    (prices : D.Fn → Nat) (storage : Wert D (types.childState name)) :
    RufAusgang callee.poll → Except (Logik D ⊕ Hardware D) (Poll (Value D) × Child D types × World D × Nat)
  | .ok after answer =>
    let (event, next) := decodePollAnswer D types name storage (ergWert callee.pollResult answer)
    .ok (event, next, after, prices callee.poll)
  | .why _ reason => keinGrund callee.pollInfallible reason
  | .logik failure => .error (.inl failure)
  | .hardware failure => .error (.inr failure)

/-- Poll a resolved child through the ordinary G call interface. A
    hardware or logic outcome is retained even when there is no
    Ready/Pending answer and no global success hypothesis. -/
@[expose] public def runChildPoll {name : String} (callee : AwaitedCall D V Λ types name)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (prices : D.Fn → Nat) (storage : Wert D (types.childState name)) (world : World D) :
    Except (Logik D ⊕ Hardware D) (Poll (Value D) × Child D types × World D × Nat) :=
  decodeChildOutcome callee prices storage (calls callee.poll world (pollEnvironment callee storage))

/-- On an ordinary success, the outcome-aware call uses the exact same
    answer, successor storage, world and cost as the total poll model. -/
public theorem runChildPoll_normal (elaboration : Elaboration D V Λ types f)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (prices : D.Fn → Nat) (normal : PollRuns elaboration calls) (name : String)
    (callee : AwaitedCall D V Λ types name) (known : elaboration.callee name = some callee)
    (storage : Wert D (types.childState name)) (world : World D) :
    runChildPoll callee calls prices storage world =
      (let answer := normal name callee known world storage
       let (event, next) := decodePollAnswer D types name storage (ergWert callee.pollResult answer.val.2)
       .ok (event, next, answer.val.1, prices callee.poll)) := by
  exact congrArg (decodeChildOutcome callee prices storage) (normal name callee known world storage).property

/-- A failed outcome of the resolved poll is also the outcome of the
    generated waiting block with its actual argument evaluation. -/
public theorem childPollBlock_reports_failure {l : Bool} {Γ : Ctx} {name : String}
    (O : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (prices : D.Fn → Nat) (callee : AwaitedCall D V Λ types name)
    (arguments : Args D Γ Λ (D.params callee.poll))
    (arms : Arms D V l (Ty.sum [some (types.childResult name), some (types.childState name)] :: Γ)
      Λ Λ [some (types.childResult name), some (types.childState name)])
    (world : World D) (environment : Env D Γ) (storage : Wert D (types.childState name))
    (argumentsAre : evalArgs (world.lese Λ arguments.orte) arguments
      (world.lese Λ arguments.orte) environment = pollEnvironment callee storage)
    {failure : Logik D ⊕ Hardware D}
    (failed : runChildPoll callee calls prices storage (world.lese Λ arguments.orte) = .error failure) :
    execBlock O passes calls (childPollBlock callee arguments arms) world environment =
      match failure with
      | .inl logic => .logik logic
      | .inr hardware => .hardware hardware := by
  cases failure <;> dsimp only
  all_goals
    rw [childPollBlock, waitingBlock_exec_outcome, argumentsAre]
    unfold runChildPoll decodeChildOutcome at failed
    generalize calls callee.poll (world.lese Λ arguments.orte) (pollEnvironment callee storage) = result
      at failed ⊢
    cases result with
    | ok after value =>
      cases decoded : decodePollAnswer D types name storage (ergWert callee.pollResult value)
      simp only [decoded, reduceCtorEq] at failed
    | why _ reason => exact keinGrund callee.pollInfallible reason
    | logik cause => cases failed <;> rfl
    | hardware cause => cases failed <;> rfl

/-- Run the same ordered task tree using actual ordinary call outcomes.
    A failure is terminal for this poll; Pending continues to preserve
    the updated child storage and Ready results stay cached. -/
@[expose] public def runTaskPoll (elaboration : Elaboration D V Λ types f)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (prices : D.Fn → Nat) :
    Task (Value D) (Child D types) → World D →
      Except (Logik D ⊕ Hardware D) (Poll (Value D) × Task (Value D) (Child D types) × World D × Nat) :=
  pollTaskWith (M := Except (Logik D ⊕ Hardware D))
    (fun child world => match child with
      | .invalid => .ok (.pending, .invalid, world, 0)
      | .active name storage =>
        match elaboration.callee name with
        | none => .ok (.pending, .invalid, world, 0)
        | some callee => runChildPoll callee calls prices storage world)
    Value.pair

/-- Left failure stops the join before a right poll can change the world. -/
public theorem runTaskPoll_join_left_failure (elaboration : Elaboration D V Λ types f)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (prices : D.Fn → Nat) (left right : Task (Value D) (Child D types)) (world : World D)
    (failure : Logik D ⊕ Hardware D)
    (failed : runTaskPoll elaboration calls prices left world = .error failure) :
    runTaskPoll elaboration calls prices (.join left right) world = .error failure := by
  unfold runTaskPoll at failed ⊢
  simp only [pollTaskWith, failed, bind, Except.bind]

/-- A right failure is observed in the actual successor world of the
    left poll, even if that left answer was Pending. -/
public theorem runTaskPoll_join_right_failure (elaboration : Elaboration D V Λ types f)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (prices : D.Fn → Nat) (left right : Task (Value D) (Child D types)) (world middle : World D)
    (event : Poll (Value D)) (successor : Task (Value D) (Child D types)) (cost : Nat)
    (failure : Logik D ⊕ Hardware D)
    (first : runTaskPoll elaboration calls prices left world = .ok (event, successor, middle, cost))
    (second : runTaskPoll elaboration calls prices right middle = .error failure) :
    runTaskPoll elaboration calls prices (.join left right) world = .error failure := by
  unfold runTaskPoll at first second ⊢
  simp only [pollTaskWith, first, second, bind, Except.bind]

/-- These semantics are computed from resolved G expressions. Missing
    resolution or an ill-typed frame produces Invalid, which the storage
    invariant excludes; it never fabricates an inhabitant of a source type. -/
@[expose] public def evaluateBound (elaboration : Elaboration D V Λ types f)
    (source : Parser.SExpr) (frame : Frame (Value D)) (world : World D) :
    Value D × World D × Nat :=
  match elaboration.expression source with
  | none => (Value.invalid, world, 0)
  | some resolved =>
    match localsEnv D resolved.locals frame with
    | none => (Value.invalid, world, 0)
    | some environment =>
      let (value, after, cost) := evaluateExpression resolved.expression world environment
      (Value.typed resolved.result value, after, cost)

@[expose] public def constructChild (elaboration : Elaboration D V Λ types f)
    (name : String) (arguments : List (Value D)) (world : World D) :
    Child D types × World D × Nat :=
  match elaboration.callee name with
  | none => (Child.invalid, world, 0)
  | some callee =>
    match argumentsEnv D callee.parameters arguments with
    | none => (Child.invalid, world, 0)
    | some environment =>
      let (storage, after, cost) := evaluateExpression callee.construct world environment
      (Child.active name storage, after, cost)

/-- Poll cost is the price of the resolved G function. Ready caches the
    typed result; Pending retains exactly the returned updated storage. -/
@[expose] public def pollChild (elaboration : Elaboration D V Λ types f)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (prices : D.Fn → Nat) (normal : PollRuns elaboration calls) :
    Child D types → World D → Poll (Value D) × Child D types × World D × Nat
  | Child.invalid, world => (Poll.pending, Child.invalid, world, 0)
  | Child.active name storage, world =>
    match known : elaboration.callee name with
    | none => (Poll.pending, Child.invalid, world, 0)
    | some callee =>
      let answer := normal name callee known world storage
      let (result, updated) := decodePollAnswer D types name storage
        (ergWert callee.pollResult answer.val.2)
      (result, updated, answer.val.1, prices callee.poll)

/-- There is no independently supplied evaluate/newChild/pollChild callback.
    Ordinary G syntax, signature resolution and actual normal call results
    determine every Model field over W = World D. -/
@[expose] public def inducedModel (elaboration : Elaboration D V Λ types f)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (prices : D.Fn → Nat) (normal : PollRuns elaboration calls) :
    Model (Value D) (Child D types) (World D) where
  evaluate := evaluateBound elaboration
  newChild := constructChild elaboration
  pollChild := pollChild elaboration calls prices normal
  pair := Value.pair

/-- The resource and state representation already proved for normal
    polls uses this same task scheduler and these same leaf answers. -/
public theorem runTaskPoll_agrees_with_inducedModel (elaboration : Elaboration D V Λ types f)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (prices : D.Fn → Nat) (normal : PollRuns elaboration calls)
    (task : Task (Value D) (Child D types)) (world : World D) :
    runTaskPoll elaboration calls prices task world =
      .ok (pollTask (inducedModel elaboration calls prices normal) task world) := by
  unfold runTaskPoll
  apply pollTaskWith_except_normal
  intro child before
  cases child with
  | invalid => rfl
  | active name storage =>
    cases selected : elaboration.callee name with
    | none => simp only [inducedModel, pollChild, selected]
    | some callee =>
      simp only [inducedModel, pollChild, selected]
      exact runChildPoll_normal elaboration calls prices normal name callee selected storage before

public theorem evaluateBound_resolved (elaboration : Elaboration D V Λ types f)
    (source : Parser.SExpr) (resolved : BoundExpression D Λ)
    (known : elaboration.expression source = some resolved)
    (frame : Frame (Value D)) (environment : Env D (resolved.locals.map Prod.snd))
    (restored : localsEnv D resolved.locals frame = some environment) (world : World D) :
    evaluateBound elaboration source frame world =
      (let (value, after, cost) := evaluateExpression resolved.expression world environment
       (Value.typed resolved.result value, after, cost)) := by
  simp only [evaluateBound, known, restored]

public theorem constructChild_resolved (elaboration : Elaboration D V Λ types f)
    (name : String) (callee : AwaitedCall D V Λ types name)
    (known : elaboration.callee name = some callee)
    (arguments : List (Value D)) (environment : Env D callee.parameters)
    (typed : argumentsEnv D callee.parameters arguments = some environment) (world : World D) :
    constructChild elaboration name arguments world =
      (let (storage, after, cost) := evaluateExpression callee.construct world environment
       (Child.active name storage, after, cost)) := by
  simp only [constructChild, known, typed]

/-- The selected normal result is an ordinary G execution fact. -/
public theorem pollChild_call (elaboration : Elaboration D V Λ types f)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (normal : PollRuns elaboration calls) (name : String)
    (callee : AwaitedCall D V Λ types name) (known : elaboration.callee name = some callee)
    (world : World D) (storage : Wert D (types.childState name)) :
    calls callee.poll world (pollEnvironment callee storage) =
      RufAusgang.ok (normal name callee known world storage).val.1
        (normal name callee known world storage).val.2 :=
  (normal name callee known world storage).property

end Gabbro.Grammatik.Async.Segment
