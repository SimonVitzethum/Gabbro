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
