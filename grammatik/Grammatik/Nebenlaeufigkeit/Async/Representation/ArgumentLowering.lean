module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.Dispatch
public import Grammatik.Nebenlaeufigkeit.Async.Representation.Restore

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {V : Vertrag D} {Λ : List (Res D)} {l : Bool} {Γ : Ctx}
  {types : TypeResolution} {f : AsyncFn}

/-- A source argument uses the actual term and live bindings furnished
    by ordinary elaboration. -/
public structure CheckedArgument (elaboration : Elaboration D V Λ types f) (tag : Nat)
    (source : Parser.SExpr) where
  term : BoundExpression D Λ
  known : elaboration.expression source = some term
  restore : RestorePlan types f term.locals
  live : ∀ entry ∈ term.locals, entry.1 ∈ liveAt f (.running tag)

@[expose] public def checkArgument (elaboration : Elaboration D V Λ types f) (tag : Nat) (argument : Parser.SExpr) :
    Except String (CheckedArgument elaboration tag argument) := do
  match found : elaboration.expression argument with
  | none => throw "async: unresolved argument expression"
  | some term =>
    if live : term.locals.all (fun entry => decide (entry.1 ∈ liveAt f (.running tag))) = true then
      let restore ← restorePlanFor types f term.locals
      return ⟨term, found, restore, fun entry member => of_decide_eq_true (List.all_eq_true.mp live entry member)⟩
    else throw "async: argument expression uses an unavailable local"

/-- Bind the value of an argument once. Restored locals are visible only
    to the expression; the continuation receives a binding for the result
    and an embedding of its original scope. -/
@[expose] public def CheckedArgument.lower {elaboration : Elaboration D V Λ types f} {tag : Nat}
    {source : Parser.SExpr} (checked : CheckedArgument elaboration tag source)
    (saved : Var Γ (frameType types f))
    (body : ∀ {Δ : Ctx}, (∀ {τ : Ty}, Var Γ τ → Var Δ τ) → Var Δ checked.term.result → Block D V l Δ Λ Λ) :
    Block D V l Γ Λ Λ :=
  restoreFrameBlock checked.restore saved
    (.bind (checked.term.expression.ren (keepLocal Γ))
      (body (fun x => .there (prependLocal x (checked.term.locals.map Prod.snd))) .here))

/-- The emitted local restoration and argument binder match exactly one
    semantic expression step, including its reads and new world. -/
public theorem CheckedArgument.lower_exec {elaboration : Elaboration D V Λ types f} {tag : Nat}
    {source : Parser.SExpr} (checked : CheckedArgument elaboration tag source)
    (saved : Var Γ (frameType types f))
    (body : ∀ {Δ : Ctx}, (∀ {τ : Ty}, Var Γ τ → Var Δ τ) → Var Δ checked.term.result → Block D V l Δ Λ Λ)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ) (frame : Frame (Value D))
    (represented : FrameRep D types f (.running tag) frame (env.get saved)) :
    ∃ (scope : Env D (checked.term.locals.map Prod.snd)),
      localsEnv D checked.term.locals frame = some scope ∧
      let continuation := body (fun x => .there (prependLocal x (checked.term.locals.map Prod.snd))) .here
      let answer := evaluateExpression checked.term.expression world scope
      evaluateBound elaboration source frame world = (Value.typed checked.term.result answer.1, answer.2) ∧
      execBlock oracle passes calls (checked.lower saved body) world env =
        removeLocals (checked.term.locals.map Prod.snd)
          (execBlock oracle passes calls continuation answer.2.1 (.cons answer.1 (appendLocals scope env))).schrumpf := by
  obtain ⟨scope, localValues⟩ := checked.restore.locals_defined (.running tag) frame (env.get saved) represented checked.live
  refine ⟨scope, localValues, evaluateBound_resolved elaboration source checked.term checked.known frame scope
    localValues world, ?_⟩
  let embedded : ∀ {τ : Ty}, Var (checked.term.locals.map Prod.snd) τ →
      Var (checked.term.locals.map Prod.snd ++ Γ) τ := keepLocal Γ
  let expression := checked.term.expression.ren embedded
  let continuation : Block D V l (checked.term.result :: checked.term.locals.map Prod.snd ++ Γ) Λ Λ :=
    body (fun x => .there (prependLocal x (checked.term.locals.map Prod.snd))) .here
  have installed := restoreFrameBlock_rep checked.restore saved oracle passes calls world env frame (.running tag)
    represented (.bind expression continuation) scope checked.live localValues
  change execBlock oracle passes calls (checked.lower saved body) world env = _ at installed
  rw [installed]
  have same := checked.term.expression.ren_sound embedded
  simp only [execBlock, expression, same.1, evaluateExpression]
  rw [same.2.2 _ _ scope (appendLocals scope env) (get_keepLocal env scope)]

/-- The list of evaluated arguments records the ordinary type at every
    source position. The list order is the call's parameter order. -/
public inductive CheckedArguments (elaboration : Elaboration D V Λ types f) (tag : Nat) :
    List Parser.SExpr → Ctx → Type where
  | nil : CheckedArguments elaboration tag [] []
  | cons (head : CheckedArgument elaboration tag source) (tail : CheckedArguments elaboration tag rest parameters) :
      CheckedArguments elaboration tag (source :: rest) (head.term.result :: parameters)

@[expose] public def checkArguments (elaboration : Elaboration D V Λ types f) (tag : Nat) :
    (sources : List Parser.SExpr) → Except String (Σ parameters, CheckedArguments elaboration tag sources parameters)
  | [] => .ok ⟨[], .nil⟩
  | source :: rest => do
    let head ← checkArgument elaboration tag source
    let ⟨parameters, tail⟩ ← checkArguments elaboration tag rest
    pure ⟨head.term.result :: parameters, .cons head tail⟩

@[expose] public def parameterVars {τ : Ty} {parameters : Ctx} (head : Var Γ τ)
    (tail : ∀ {type : Ty}, Var parameters type → Var Γ type) :
    ∀ {type : Ty}, Var (τ :: parameters) type → Var Γ type
  | _, .here => head
  | _, .there field => tail field

/-- Arguments are evaluated from left to right. All their values are
    available at the final continuation in actual parameter order. -/
@[expose] public def CheckedArguments.lower {elaboration : Elaboration D V Λ types f} {tag : Nat} :
    {sources : List Parser.SExpr} → {parameters : Ctx} → CheckedArguments elaboration tag sources parameters →
    {Γ : Ctx} → Var Γ (frameType types f) →
    (∀ {Δ : Ctx}, (∀ {τ : Ty}, Var Γ τ → Var Δ τ) →
      (∀ {τ : Ty}, Var parameters τ → Var Δ τ) → Block D V l Δ Λ Λ) →
    Block D V l Γ Λ Λ
  | [], [], .nil, _, _, body => body (fun var => var) (fun var => nomatch var)
  | _ :: _, _, .cons head tail, _, saved, body =>
    head.lower saved (fun extend first =>
      tail.lower (extend saved) (fun later rest =>
        body (fun var => later (extend var)) (parameterVars (later first) rest)))

/-- The compiler's checked argument order and types are exactly those
    required by the ordinary elaborator. -/
public theorem CheckedArguments.exactTypes {elaboration : Elaboration D V Λ types f} {tag : Nat}
    {sources : List Parser.SExpr} {parameters : Ctx} (checked : CheckedArguments elaboration tag sources parameters)
    {terms : List (BoundExpression D Λ)} (resolved : ExpressionsResolved elaboration.expression sources terms) :
    parameters = terms.map BoundExpression.result := by
  induction checked generalizing terms with
  | nil => cases resolved; rfl
  | cons head tail ih =>
    cases resolved with
    | cons found rest =>
      have term := Option.some.inj (head.known.symm.trans found)
      rw [List.map_cons, ← term, ← ih rest]

/-- Annotate an executed continuation by the exact final parameter
    environment. This relation compares the lowered block's result after
    each temporary argument and local slot has left its scope. -/
public theorem CheckedArguments.lower_assign {elaboration : Elaboration D V Λ types f} {tag : Nat}
    {sources : List Parser.SExpr} {parameters : Ctx} (checked : CheckedArguments elaboration tag sources parameters)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    {τ : Ty} (destination : Var Γ τ) (saved : Var Γ (frameType types f))
    (body : ∀ {Δ : Ctx}, (∀ {type : Ty}, Var Γ type → Var Δ type) →
      (∀ {type : Ty}, Var parameters type → Var Δ type) → Block D V l Δ Λ Λ)
    (oracle : Orakel D) (passes : Nat)
    (effect : Env D parameters → World D → Wert D τ × World D)
    (frame : Frame (Value D)) (world : World D) (env : Env D Γ)
    (represented : FrameRep D types f (.running tag) frame (env.get saved))
    (correct : ∀ {Δ : Ctx} (extend : ∀ {type : Ty}, Var Γ type → Var Δ type)
      (formals : ∀ {type : Ty}, Var parameters type → Var Δ type)
      (scope : Env D Δ) (arguments : Env D parameters) (world : World D),
      env.AgreesUnder scope extend → arguments.AgreesUnder scope formals →
      execBlock oracle passes calls (body extend formals) world scope =
        let answer := effect arguments world
        .ok answer.2 (scope.set (extend destination) answer.1)) :
    let args := evalArgumentsBy (evaluateBound elaboration) frame sources world
    ∃ arguments, argumentsEnv D parameters args.1 = some arguments ∧
      execBlock oracle passes calls (checked.lower saved body) world env =
        let answer := effect arguments args.2.1
        .ok answer.2 (env.set destination answer.1) := by
  induction checked generalizing Γ world with
  | nil =>
    exact ⟨.nil, rfl, correct (fun var => var) (fun var => nomatch var) env .nil world (fun _ => rfl) (fun var => nomatch var)⟩
  | @cons source rest parameters head tail ih =>
    let continuation : ∀ {Δ : Ctx}, (∀ {type : Ty}, Var Γ type → Var Δ type) →
        Var Δ head.term.result → Block D V l Δ Λ Λ :=
      fun extend first => tail.lower (extend saved) (fun later parameters =>
        body (fun var => later (extend var)) (parameterVars (later first) parameters))
    obtain ⟨locals, _, value, ran⟩ := head.lower_exec saved continuation oracle passes calls world env frame represented
    let answer := evaluateExpression head.term.expression world locals
    let extension : ∀ {type : Ty}, Var Γ type → Var (head.term.result :: head.term.locals.map Prod.snd ++ Γ) type :=
      fun var => .there (prependLocal var (head.term.locals.map Prod.snd))
    let scope : Env D (head.term.result :: head.term.locals.map Prod.snd ++ Γ) :=
      .cons answer.1 (appendLocals locals env)
    have newFrame : FrameRep D types f (.running tag) frame (scope.get (extension saved)) := by
      change FrameRep D types f (.running tag) frame
        ((appendLocals locals env).get (prependLocal saved (head.term.locals.map Prod.snd)))
      rw [get_prependLocal]
      exact represented
    let restEffect := fun arguments middle => effect (.cons answer.1 arguments) middle
    let restBody : ∀ {Δ : Ctx},
        (∀ {type : Ty}, Var (head.term.result :: head.term.locals.map Prod.snd ++ Γ) type → Var Δ type) →
        (∀ {type : Ty}, Var parameters type → Var Δ type) → Block D V l Δ Λ Λ :=
      fun later params => body (fun var => later (extension var)) (parameterVars (later .here) params)
    have restCorrect {Δ : Ctx} (later : ∀ {type : Ty},
          Var (head.term.result :: head.term.locals.map Prod.snd ++ Γ) type → Var Δ type)
        (params : ∀ {type : Ty}, Var parameters type → Var Δ type) (context : Env D Δ)
        (arguments : Env D parameters) (middle : World D) (retained : scope.AgreesUnder context later)
        (agrees : arguments.AgreesUnder context params) :
        execBlock oracle passes calls (restBody later params) middle context =
          .ok (restEffect arguments middle).2 (context.set (later (extension destination)) (restEffect arguments middle).1) := by
      apply correct
      · intro type var
        exact (retained (extension var)).trans (get_prependLocal var env locals)
      · intro type var
        cases var with
        | here => exact retained .here
        | there var => exact agrees var
    obtain ⟨arguments, typed, lowered⟩ := ih (extension destination) (extension saved) restBody restEffect
      answer.2.1 scope newFrame restCorrect
    refine ⟨.cons answer.1 arguments, ?_, ?_⟩
    · simp only [evalArgumentsBy, value, argumentsEnv, valueAt_typed, typed,
        Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    · change execBlock oracle passes calls (head.lower saved continuation) world env = _
      rw [ran]
      change removeLocals (head.term.locals.map Prod.snd)
        (execBlock oracle passes calls (tail.lower (extension saved) restBody) answer.2.1 scope).schrumpf = _
      rw [lowered]
      simp only [evalArgumentsBy, value]
      let result := effect (.cons answer.1 arguments)
        (evalArgumentsBy (evaluateBound elaboration) frame rest answer.2.1).2.1
      change removeLocals (head.term.locals.map Prod.snd)
        (.ok result.2 ((appendLocals locals env).set (prependLocal destination (head.term.locals.map Prod.snd)) result.1)) =
        .ok result.2 (env.set destination result.1)
      rw [set_prependLocal, removeLocals_ok]

end Gabbro.Grammatik.Async.Representation
