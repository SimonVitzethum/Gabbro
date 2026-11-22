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

@[expose] public def activeJoinValue (types : TypeResolution) (path : List Nat) (left right : FutureExpr)
    (first : Wert D (taskStorageType types (0 :: path) left))
    (second : Wert D (taskStorageType types (1 :: path) right)) :
    Wert D (taskStorageType types path (.join left right)) :=
  readyAnswer D (taskActiveType types path (.join left right))
    (taskResultType types path (.join left right)) (first, second, ())

/-- The generated code binds the exact lazy future of the source tree.
    The result of its continuation is preserved when the constructor's
    private temporaries leave their lexical scopes. -/
public theorem ConstructPlan.lower_assign {elaboration : Elaboration D V Λ types f} {tag : Nat}
    {future : FutureExpr} (plan : ConstructPlan elaboration tag future)
    (path : List Nat) {τ : Ty} (destination : Var Γ τ) (saved : Var Γ (frameType types f))
    (body : ∀ {Δ : Ctx}, (∀ {type : Ty}, Var Γ type → Var Δ type) →
      Var Δ (taskStorageType types path future) → Block D V l Δ Λ Λ)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (effect : Wert D (taskStorageType types path future) → World D → Wert D τ × World D)
    (frame : Frame (Value D)) (world : World D) (env : Env D Γ)
    (represented : FrameRep D types f (.running tag) frame (env.get saved))
    (correct : ∀ {Δ : Ctx} (extend : ∀ {type : Ty}, Var Γ type → Var Δ type)
      (slot : Var Δ (taskStorageType types path future)) (scope : Env D Δ) (world : World D),
      env.AgreesUnder scope extend →
      execBlock oracle passes calls (body extend slot) world scope =
        let answer := effect (scope.get slot) world
        .ok answer.2 (scope.set (extend destination) answer.1)) :
    let built := makeTaskBy (evaluateBound elaboration) (constructChild elaboration) frame future world
    ∃ storage, TaskRep D types path future built.1 storage ∧
      execBlock oracle passes calls (plan.lower path saved body) world env =
        let answer := effect storage built.2.1
        .ok answer.2 (env.set destination answer.1) := by
  induction plan generalizing path Γ world with
  | call name args callee known checked =>
    exact constructLeafBlock_assign elaboration tag path name args callee known checked destination saved body
      oracle passes calls effect frame world env represented correct
  | @join left right first second firstIH secondIH =>
    let make := makeTaskBy (evaluateBound elaboration) (constructChild elaboration) frame
    let collect := activeJoinValue (D := D) types path left right
    let secondEffect := fun a b (now : World D) => effect (collect a b) now
    let firstEffect := fun a (now : World D) =>
      let b := make right now
      match encodeTask D types (1 :: path) right b.1 with
      | some code => secondEffect a code b.2.1
      | none => (env.get destination, now)
    let rest : ∀ {Δ : Ctx}, (∀ {type : Ty}, Var Γ type → Var Δ type) →
        Var Δ (taskStorageType types (0 :: path) left) → Block D V l Δ Λ Λ :=
      fun extend a =>
        second.lower (1 :: path) (extend saved) (fun later b =>
          .bind (joinChildrenExpr types path left right (.var (later a)) (.var b))
            (body (fun var => .there (later (extend var))) .here))
    have executes {Δ : Ctx} (extend : ∀ {type : Ty}, Var Γ type → Var Δ type)
        (a : Var Δ (taskStorageType types (0 :: path) left)) (middleEnv : Env D Δ) (middle : World D)
        (agrees : env.AgreesUnder middleEnv extend) :
        execBlock oracle passes calls (rest extend a) middle middleEnv =
          .ok (firstEffect (middleEnv.get a) middle).2
            (middleEnv.set (extend destination) (firstEffect (middleEnv.get a) middle).1) := by
      let finish : ∀ {Ξ : Ctx}, (∀ {type : Ty}, Var Δ type → Var Ξ type) →
          Var Ξ (taskStorageType types (1 :: path) right) → Block D V l Ξ Λ Λ :=
        fun later b => .bind (joinChildrenExpr types path left right (.var (later a)) (.var b))
          (body (fun var => .there (later (extend var))) .here)
      have frameRep : FrameRep D types f (.running tag) frame (middleEnv.get (extend saved)) := by
        rw [agrees saved]
        exact represented
      have finishes {Ξ : Ctx} (later : ∀ {type : Ty}, Var Δ type → Var Ξ type)
          (b : Var Ξ (taskStorageType types (1 :: path) right)) (context : Env D Ξ) (now : World D)
          (retained : middleEnv.AgreesUnder context later) :
          execBlock oracle passes calls (finish later b) now context =
            .ok (secondEffect (middleEnv.get a) (context.get b) now).2
              (context.set (later (extend destination)) (secondEffect (middleEnv.get a) (context.get b) now).1) := by
        let value := collect (context.get (later a)) (context.get b)
        have ran := correct (fun var => .there (later (extend var))) .here (.cons value context) now
          (fun var => (retained (extend var)).trans (agrees var))
        change (execBlock oracle passes calls (body (fun var => .there (later (extend var))) .here) now
          (.cons value context)).schrumpf = _
        rw [ran]
        change Ausgang.ok (effect value now).2 (context.set (later (extend destination)) (effect value now).1) = _
        unfold value secondEffect
        rw [retained a]
      obtain ⟨bStorage, bRep, ran⟩ := secondIH (1 :: path) (extend destination) (extend saved)
        finish (secondEffect (middleEnv.get a)) middle middleEnv frameRep finishes
      have code := taskRep_encoded types (1 :: path) right (make right middle).1 bStorage bRep
      change execBlock oracle passes calls (second.lower (1 :: path) (extend saved) finish) middle middleEnv = _
      rw [ran]
      simp only [firstEffect, code] <;> rfl
    obtain ⟨aStorage, aRep, ran⟩ := firstIH (0 :: path) destination saved rest firstEffect world env represented executes
    obtain ⟨bStorage, bRep⟩ := second.representable frame (env.get saved) represented (1 :: path) (make left world).2.1
    have encoded := taskRep_encoded types (1 :: path) right _ bStorage bRep
    refine ⟨collect aStorage bStorage, .joinActive aRep bRep, ?_⟩
    change execBlock oracle passes calls (first.lower (0 :: path) saved rest) world env =
      .ok (effect (collect aStorage bStorage) (make right (make left world).2.1).2.1).2
        (env.set destination (effect (collect aStorage bStorage) (make right (make left world).2.1).2.1).1)
    rw [ran]
    simp only [firstEffect, secondEffect]
    erw [encoded]

/-- The Running await arm evaluates the actual argument tree and saves
    the constructed task together with only the live continuation slots. -/
@[expose] public def beginAwaitBlock {elaboration : Elaboration D V Λ types f}
    (tag : Nat) {destination : String} {future : FutureExpr} {boundary : Boundary} {rest : List Command}
    (command : f.body.drop tag = Command.await destination future boundary :: rest)
    (plan : ConstructPlan elaboration tag future)
    (saved : Var Γ (frameType types f)) (state : Var Γ (stateType types f)) :
    Block D V l Γ Λ Λ :=
  plan.lower [tag] saved (fun extend task =>
    constructBlock (extend state)
      (waitingExpr types f tag command (trimFrameExpr types f (liveAt f (.waiting tag future)) (extend saved)) (.var task)))

/-- Execution of the generated starting arm produces the precise canonical
    Waiting record. The first poll is a separate ordinary G segment. -/
public theorem beginAwaitBlock_simulates {elaboration : Elaboration D V Λ types f}
    (inventory : Inventory D) (tag : Nat) {destination : String} {future : FutureExpr} {boundary : Boundary}
    {rest : List Command} (command : f.body.drop tag = Command.await destination future boundary :: rest)
    (plan : ConstructPlan elaboration tag future)
    (saved : Var Γ (frameType types f)) (state : Var Γ (stateType types f))
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ) (frame : Frame (Value D))
    (represented : FrameRep D types f (.running tag) frame (env.get saved))
    (marks : MarksRep inventory (.running tag) (.running (Child := Child D types) tag frame))
    (sameInventory : inventory.owned (.waiting tag future) = inventory.owned (.running tag)) :
    let built := makeTaskBy (evaluateBound elaboration) (constructChild elaboration) frame future world
    let target := State.waiting tag frame built.1
    ∃ value, execBlock oracle passes calls (beginAwaitBlock (l := l) tag command plan saved state) world env =
        .ok built.2.1 (env.set state value) ∧
      Inv f types inventory target value ∧ encode D types f target = some value := by
  intro built target
  have retained : liveAt f (.waiting tag future) ⊆ liveAt f (.running tag) := by
    simp only [liveAt, command, liveBefore]
    intro name member
    exact List.mem_append_right _ member
  let trimmed := eval world (trimFrameExpr (Λ := Λ) types f (liveAt f (.waiting tag future)) saved) world env
  have trimmedSlots := (trimFrameExpr_rep (Λ := Λ) saved retained world world env represented.slots).2
  have trimmedFrame : FrameRep D types f (.waiting tag future) frame trimmed :=
    ⟨trimmedSlots, fun name member => represented.declared name (retained member), represented.unique⟩
  let body : ∀ {Δ : Ctx}, (∀ {type : Ty}, Var Γ type → Var Δ type) →
      Var Δ (taskStorageType types [tag] future) → Block D V l Δ Λ Λ := fun extend task =>
    constructBlock (extend state)
      (waitingExpr types f tag command (trimFrameExpr types f (liveAt f (.waiting tag future)) (extend saved)) (.var task))
  let effect := fun child (next : World D) => (waitingValue D types f tag command trimmed child, next)
  have correct {Δ : Ctx} (extend : ∀ {type : Ty}, Var Γ type → Var Δ type)
      (slot : Var Δ (taskStorageType types [tag] future)) (scope : Env D Δ) (now : World D)
      (inherited : env.AgreesUnder scope extend) :
      execBlock oracle passes calls (body extend slot) now scope =
        .ok (effect (scope.get slot) now).2 (scope.set (extend state) (effect (scope.get slot) now).1) := by
    have previous : FrameRep D types f (.running tag) frame (scope.get (extend saved)) := by
      rw [inherited saved]
      exact represented
    let scan : Expr D Δ Λ (frameType types f) :=
      trimFrameExpr types f (liveAt f (.waiting tag future)) (extend saved)
    obtain ⟨silent, slots⟩ := trimFrameExpr_rep (Λ := Λ) (extend saved) retained now now scope previous.slots
    have sameFrame : FrameRep D types f (.waiting tag future) frame (eval now scan now scope) :=
      ⟨slots, trimmedFrame.declared, trimmedFrame.unique⟩
    have exactFrame : eval now scan now scope = trimmed := Option.some.inj
      ((frameRep_encoded types f (.waiting tag future) frame _ sameFrame).symm.trans
        (frameRep_encoded types f (.waiting tag future) frame trimmed trimmedFrame))
    let store := waitingExpr types f tag command scan (.var slot)
    have noReads : store.orte = [] := by
      unfold store
      rw [waitingExpr_reads, silent]
      rfl
    have noRead : now.lese Λ [] = now := rfl
    have execution := constructBlock_exec (V := V) (l := l) oracle passes calls (extend state) store now scope
    simp only [noReads, noRead] at execution
    have content := waitingExpr_eval types f tag command scan (.var slot) now now scope
    rw [exactFrame] at content
    erw [content] at execution
    exact execution
  obtain ⟨taskValue, taskRep, executed⟩ := plan.lower_assign [tag] state saved body oracle passes calls effect
    frame world env represented correct
  let value := waitingValue D types f tag command trimmed taskValue
  have owned : MarksRep inventory (.waiting tag future) target := by
    simpa only [target, MarksRep, State.marks, sameInventory] using marks
  have invariant : Inv f types inventory target value :=
    waitingValue_inv types f inventory tag command frame _ trimmed taskValue trimmedFrame taskRep owned
  exact ⟨value, executed, invariant, inv_encoded f types inventory target value invariant⟩

end Gabbro.Grammatik.Async.Representation
