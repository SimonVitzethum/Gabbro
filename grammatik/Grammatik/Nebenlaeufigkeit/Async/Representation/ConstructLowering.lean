module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.ArgumentLowering

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {V : Vertrag D} {Λ : List (Res D)} {l : Bool} {Γ : Ctx}
  {types : TypeResolution} {f : AsyncFn}

/-- The executable leaf construction restores and evaluates its arguments,
    binds the resulting active child, and transfers to ordinary continuation code. -/
@[expose] public def constructLeafBlock {elaboration : Elaboration D V Λ types f}
    (tag : Nat) (path : List Nat) (name : String) (args : List Parser.SExpr)
    (callee : AwaitedCall D V Λ types name) (checked : CheckedArguments elaboration tag args callee.parameters)
    (saved : Var Γ (frameType types f))
    (body : ∀ {Δ : Ctx}, (∀ {τ : Ty}, Var Γ τ → Var Δ τ) →
      Var Δ (taskStorageType types path (.call name args)) → Block D V l Δ Λ Λ) :
    Block D V l Γ Λ Λ :=
  checked.lower saved (fun extend parameters =>
    .bind (activeChildExpr callee path args parameters) (body (fun var => .there (extend var)) .here))

/-- The emitted child constructor receives exactly the actual source
    argument values, in order. It makes no call to the child's poll. -/
public theorem constructLeafBlock_assign (elaboration : Elaboration D V Λ types f)
    (tag : Nat) (path : List Nat) (name : String) (args : List Parser.SExpr)
    (callee : AwaitedCall D V Λ types name) (known : elaboration.callee name = some callee)
    (checked : CheckedArguments elaboration tag args callee.parameters)
    {τ : Ty} (destination : Var Γ τ) (saved : Var Γ (frameType types f))
    (body : ∀ {Δ : Ctx}, (∀ {type : Ty}, Var Γ type → Var Δ type) →
      Var Δ (taskStorageType types path (.call name args)) → Block D V l Δ Λ Λ)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (effect : Wert D (taskStorageType types path (.call name args)) → World D → Wert D τ × World D)
    (frame : Frame (Value D)) (world : World D) (env : Env D Γ)
    (represented : FrameRep D types f (.running tag) frame (env.get saved))
    (correct : ∀ {Δ : Ctx} (extend : ∀ {type : Ty}, Var Γ type → Var Δ type)
      (slot : Var Δ (taskStorageType types path (.call name args))) (scope : Env D Δ) (world : World D),
      env.AgreesUnder scope extend →
      execBlock oracle passes calls (body extend slot) world scope =
        let answer := effect (scope.get slot) world
        .ok answer.2 (scope.set (extend destination) answer.1)) :
    let built := makeTaskBy (evaluateBound elaboration) (constructChild elaboration) frame (.call name args) world
    ∃ storage, TaskRep D types path (.call name args) built.1 storage ∧
      execBlock oracle passes calls (constructLeafBlock (l := l) tag path name args callee checked saved body) world env =
        let answer := effect storage built.2.1
        .ok answer.2 (env.set destination answer.1) := by
  intro built
  let generated : ∀ {Δ : Ctx}, (∀ {type : Ty}, Var Γ type → Var Δ type) →
      (∀ {type : Ty}, Var callee.parameters type → Var Δ type) → Block D V l Δ Λ Λ :=
    fun extend parameters =>
      .bind (activeChildExpr callee path args parameters) (body (fun var => .there (extend var)) .here)
  let evaluateChild := fun (parameters : Env D callee.parameters) middle =>
    evaluateExpression (activeChildExpr callee path args (fun var => var)) middle parameters
  let finish := fun parameters middle =>
    let child := evaluateChild parameters middle
    effect child.1 child.2.1
  have executes {Δ : Ctx} (extend : ∀ {type : Ty}, Var Γ type → Var Δ type)
      (rename : ∀ {type : Ty}, Var callee.parameters type → Var Δ type)
      (scope : Env D Δ) (parameters : Env D callee.parameters) (middle : World D)
      (outer : env.AgreesUnder scope extend) (formals : parameters.AgreesUnder scope rename) :
      execBlock oracle passes calls (generated extend rename) middle scope =
        .ok (finish parameters middle).2 (scope.set (extend destination) (finish parameters middle).1) := by
    obtain ⟨sameReads, _, sameEval⟩ := callee.construct.ren_sound rename
    let template := activeChildExpr callee path args (fun var => var)
    let atCall := activeChildExpr callee path args rename
    have samePlaces : atCall.orte = template.orte := by
      simp only [atCall, template, activeChildExpr, activeLeafExpr, Expr.orte, NutzlastExpr.orte, sameReads]
      rw [(callee.construct.ren_sound (fun var => var)).1]
    have inherited (now : World D) : eval now atCall now scope = eval now template now parameters := by
      simp only [atCall, template, activeChildExpr, activeLeafExpr, eval, evalNutz]
      rw [sameEval now now parameters scope formals]
      rw [(callee.construct.ren_sound (fun var => var)).2.2 now now parameters parameters (fun _ => rfl)]
    let read := middle.lese Λ template.orte
    let value := eval read template read parameters
    change (execBlock oracle passes calls (body (fun var => .there (extend var)) .here)
      (middle.lese Λ atCall.orte)
      (.cons (eval (middle.lese Λ atCall.orte) atCall (middle.lese Λ atCall.orte) scope) scope)).schrumpf = _
    rw [samePlaces, inherited]
    have done := correct (fun var => .there (extend var)) .here (.cons value scope) read outer
    change (execBlock oracle passes calls (body (fun var => .there (extend var)) .here) read
      (.cons value scope)).schrumpf = _
    rw [done]
    rfl
  obtain ⟨parameters, typed, ran⟩ :=
    checked.lower_assign calls destination saved generated oracle passes finish frame world env represented executes
  let evaluated := evalArgumentsBy (evaluateBound elaboration) frame args world
  let actual := evaluateChild parameters evaluated.2.1
  have exactChild := activeChildExpr_rep elaboration path name args callee known evaluated.1 parameters typed
    evaluated.2.1 parameters (fun var => var) (fun _ => rfl)
  change TaskRep D types path (.call name args) (.leaf (constructChild elaboration name evaluated.1 evaluated.2.1).1)
    actual.1 ∧ actual.2.1 = (constructChild elaboration name evaluated.1 evaluated.2.1).2.1 ∧ _ at exactChild
  refine ⟨actual.1, exactChild.1, ?_⟩
  change execBlock oracle passes calls (checked.lower saved generated) world env =
    .ok (effect actual.1 built.2.1).2 (env.set destination (effect actual.1 built.2.1).1)
  rw [ran]
  change _ = Ausgang.ok (effect actual.1 (constructChild elaboration name evaluated.1 evaluated.2.1).2.1).2
    (env.set destination (effect actual.1 (constructChild elaboration name evaluated.1 evaluated.2.1).2.1).1)
  rw [← exactChild.2.1]
  rfl

/-- The checked construction plan follows the exact finite source tree.
    Each leaf establishes the arglist types against the callee signature. -/
public inductive ConstructPlan (elaboration : Elaboration D V Λ types f) (tag : Nat) :
    FutureExpr → Type where
  | call (name : String) (args : List Parser.SExpr) (callee : AwaitedCall D V Λ types name)
      (known : elaboration.callee name = some callee)
      (arguments : CheckedArguments elaboration tag args callee.parameters) :
      ConstructPlan elaboration tag (.call name args)
  | join : ConstructPlan elaboration tag left → ConstructPlan elaboration tag right →
      ConstructPlan elaboration tag (.join left right)

@[expose] public def ConstructPlan.resolve (elaboration : Elaboration D V Λ types f) (tag : Nat) :
    (future : FutureExpr) → Except String (ConstructPlan elaboration tag future)
  | .call name args => do
    match found : elaboration.callee name with
    | none => throw "async: unresolved child constructor"
    | some callee =>
      let ⟨parameterTypes, checked⟩ ← checkArguments elaboration tag args
      if same : parameterTypes = callee.parameters then
        pure (.call name args callee found (same ▸ checked))
      else throw "async: constructor arguments disagree with the resolved signature"
  | .join left right => do
    let first ← resolve elaboration tag left
    let second ← resolve elaboration tag right
    pure (.join first second)

/-- The G syntax is nested in source order. The left constructor
    completes before any argument of the right child is evaluated. -/
@[expose] public def ConstructPlan.lower {elaboration : Elaboration D V Λ types f} {tag : Nat} :
    {future : FutureExpr} → ConstructPlan elaboration tag future →
    (path : List Nat) → {Γ : Ctx} → Var Γ (frameType types f) →
    (∀ {Δ : Ctx}, (∀ {τ : Ty}, Var Γ τ → Var Δ τ) →
      Var Δ (taskStorageType types path future) → Block D V l Δ Λ Λ) → Block D V l Γ Λ Λ
  | _, .call name args callee _ checked, path, _, saved, body =>
    constructLeafBlock tag path name args callee checked saved body
  | _, @ConstructPlan.join _ _ _ _ _ _ _ left right first second, path, _, saved, body =>
    lower first (0 :: path) saved (fun extend a =>
      lower second (1 :: path) (extend saved) (fun later b =>
        .bind (joinChildrenExpr types path left right (.var (later a)) (.var b))
          (body (fun var => .there (later (extend var))) .here)))

public theorem CheckedArguments.expressions {elaboration : Elaboration D V Λ types f} {tag : Nat}
    {args : List Parser.SExpr} {parameters : Ctx} (checked : CheckedArguments elaboration tag args parameters) :
    ∃ terms, ExpressionsResolved elaboration.expression args terms ∧ terms.map BoundExpression.result = parameters := by
  induction checked with
  | nil => exact ⟨[], .nil, rfl⟩
  | cons head tail ih =>
    obtain ⟨terms, resolved, typesEq⟩ := ih
    exact ⟨head.term :: terms, .cons head.known resolved, congrArg (head.term.result :: ·) typesEq⟩

public theorem CheckedArguments.locals_defined {elaboration : Elaboration D V Λ types f} {tag : Nat}
    {args : List Parser.SExpr} {parameters : Ctx} (checked : CheckedArguments elaboration tag args parameters)
    (frame : Frame (Value D)) (saved : Wert D (frameType types f))
    (represented : FrameRep D types f (.running tag) frame saved) :
    ∀ source ∈ args, ∀ expression, elaboration.expression source = some expression →
      ∃ environment, localsEnv D expression.locals frame = some environment := by
  induction checked with
  | nil =>
    intro source member
    cases member
  | cons head tail ih =>
    intro source member expression known
    rcases List.mem_cons.mp member with rfl | rest
    · have equal := Option.some.inj (known.symm.trans head.known)
      subst expression
      exact head.restore.locals_defined (.running tag) frame saved represented head.live
    · exact ih source rest expression known

/-- Every represented running frame provides a typed encoding of the
    future described by this executable constructor plan. -/
public theorem ConstructPlan.representable {elaboration : Elaboration D V Λ types f} {tag : Nat}
    {future : FutureExpr} (plan : ConstructPlan elaboration tag future)
    (frame : Frame (Value D)) (saved : Wert D (frameType types f))
    (represented : FrameRep D types f (.running tag) frame saved)
    (path : List Nat) (world : World D) :
    ∃ record, TaskRep D types path future
      (makeTaskBy (evaluateBound elaboration) (constructChild elaboration) frame future world).1 record := by
  apply makeTask_rep elaboration frame future _ _ path world
  · intro name args selected
    induction plan with
    | call declaredName declaredArgs callee known checked =>
      simp only [callsIn, List.mem_singleton, FutureExpr.call.injEq] at selected
      obtain ⟨rfl, rfl⟩ := selected
      obtain ⟨terms, resolved, same⟩ := checked.expressions
      exact ⟨callee, terms, known, resolved, same⟩
    | join _ _ first second =>
      rcases List.mem_append.mp selected with left | right
      · exact first left
      · exact second right
  · intro name args selected source used term known
    induction plan with
    | call declaredName declaredArgs callee found checked =>
      simp only [callsIn, List.mem_singleton, FutureExpr.call.injEq] at selected
      obtain ⟨rfl, rfl⟩ := selected
      exact checked.locals_defined frame saved represented source used term known
    | join _ _ first second =>
      rcases List.mem_append.mp selected with left | right
      · exact first left
      · exact second right

end Gabbro.Grammatik.Async.Representation
