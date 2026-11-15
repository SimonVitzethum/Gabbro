module

public import Grammatik.Nebenlaeufigkeit.Async.Segment.Values
public import Grammatik.Nebenlaeufigkeit.Async.Segment.Answers

namespace Gabbro.Grammatik.Async.Segment

variable {D : Deklaration}

/-- Ordinary expression elaboration supplies its actual local context and
    result type. The expression is G syntax, not a semantic callback. -/
public structure BoundExpression (D : Deklaration) (Λ : List (Res D)) where
  locals : List (String × Ty)
  result : Ty
  expression : Expr D (locals.map Prod.snd) Λ result
  lifted : (storage : Ty) → Expr D (storage :: locals.map Prod.snd) Λ result
  liftedPlaces : ∀ storage, (lifted storage).orte = expression.orte
  liftedCost : ∀ storage, kostenExpr (lifted storage) = kostenExpr expression
  liftedEval : ∀ storage (saved : Wert D storage) entry world environment,
    eval entry (lifted storage) world (Env.cons saved environment) =
      eval entry expression world environment

/-- One resolved lazy callee. Construction is a pure, ordinary expression;
    polling is an actual named G call. The two answer payloads are Ready's
    result and Pending's updated state, in that order. -/
public structure AwaitedCall (D : Deklaration) (V : Vertrag D) (Λ : List (Res D))
    (types : TypeResolution) (name : String) where
  parameters : List Ty
  construct : Expr D parameters Λ (types.childState name)
  poll : D.Fn
  pollParams : D.params poll = [types.childState name]
  pollResult : D.erg poll = some (Ty.sum [some (types.childResult name), some (types.childState name)])
  pollContract : RufPasst D V (D.signatur poll) Λ
  pollInfallible : D.gruende poll = 0
  pollInventory : nach D poll Λ = Λ

/-- Include nested joins without executing either child. -/
@[expose] public def callsIn : FutureExpr → List FutureExpr
  | FutureExpr.call name args => [FutureExpr.call name args]
  | FutureExpr.join left right => callsIn left ++ callsIn right

public inductive ExpressionsResolved {Λ : List (Res D)}
    (resolve : Parser.SExpr → Option (BoundExpression D Λ)) :
    List Parser.SExpr → List (BoundExpression D Λ) → Prop where
  | nil : ExpressionsResolved resolve [] []
  | cons (found : resolve source = some expression)
      (rest : ExpressionsResolved resolve sources expressions) :
      ExpressionsResolved resolve (source :: sources) (expression :: expressions)

/-- The ONE elaborator interface. It contains only resolved syntax and
    ordinary signature obligations. Resolution is explicitly partial; the
    coverage fields rule out missing entries for this declaration. No
    SegmentDuty, Model callback, or representation theorem is an input. -/
public structure Elaboration (D : Deklaration) (V : Vertrag D) (Λ : List (Res D))
    (types : TypeResolution) (f : AsyncFn) where
  expression : Parser.SExpr → Option (BoundExpression D Λ)
  callee : (name : String) → Option (AwaitedCall D V Λ types name)
  bound : ∀ name source bound, Command.bind name source bound ∈ f.body →
    ∃ resolved sourceType, expression source = some resolved ∧
      (f.params ++ f.fields).lookup name = some sourceType ∧
      resolved.result = types.ordinary sourceType
  returned : ∃ resolved, expression f.result = some resolved ∧
    resolved.result = types.ordinary f.resultType
  arguments : ∀ name args, FutureExpr.call name args ∈
    (f.body.flatMap fun command => match command with
      | Command.bind _ _ _ => []
      | Command.await _ future _ => callsIn future) →
    ∃ resolved resolvedArgs, callee name = some resolved ∧
      ExpressionsResolved expression args resolvedArgs ∧
      resolvedArgs.map BoundExpression.result = resolved.parameters
  awaited : ∀ tag name future boundary rest,
    f.body.drop tag = Command.await name future boundary :: rest →
      ∃ sourceType, (f.params ++ f.fields).lookup name = some sourceType ∧
        taskResultType types [tag] future = types.ordinary sourceType

/-- Actual singleton argument environment of the resolved child's poll. -/
@[expose] public def pollEnvironment {V : Vertrag D} {Λ : List (Res D)}
    {types : TypeResolution} {name : String}
    (callee : AwaitedCall D V Λ types name) (storage : Wert D (types.childState name)) :
    Env D (D.params callee.poll) :=
  callee.pollParams.symm ▸ Env.cons storage Env.nil

/-- The same checked signature is used to generate the child call. Resource
    transport is justified by the callee's exact inventory equality. -/
@[expose] public def childPollBlock {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {types : TypeResolution} {name : String}
    (callee : AwaitedCall D V Λ types name)
    (arguments : Args D Γ Λ (D.params callee.poll))
    (arms : Arms D V l
      (Ty.sum [some (types.childResult name), some (types.childState name)] :: Γ)
      Λ Λ [some (types.childResult name), some (types.childState name)]) : Block D V l Γ Λ Λ :=
  waitingBlock (V := V) (l := l) callee.poll arguments callee.pollResult callee.pollContract
    callee.pollInfallible
    (Eq.mp (congrArg
      (fun resources => Arms D V l
        (Ty.sum [some (types.childResult name), some (types.childState name)] :: Γ)
        resources Λ [some (types.childResult name), some (types.childState name)])
      callee.pollInventory.symm) arms)

end Gabbro.Grammatik.Async.Segment
