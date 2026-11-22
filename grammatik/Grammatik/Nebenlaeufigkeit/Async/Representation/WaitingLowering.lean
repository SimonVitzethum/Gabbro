module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.Construction

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {types : TypeResolution} {f : AsyncFn}
  {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- Generate the active child case from the resolved constructor. The
    constructor receives just its already evaluated argument bindings. -/
@[expose] public def activeChildExpr {name : String}
    (callee : AwaitedCall D V Λ types name) (path : List Nat) (args : List Parser.SExpr)
    (rename : ∀ {τ : Ty}, Var callee.parameters τ → Var Γ τ) :
    Expr D Γ Λ (taskStorageType types path (.call name args)) :=
  .case [some (types.childState name), some (types.childResult name)] ⟨0, Nat.zero_lt_succ 1⟩
    (.val (callee.construct.ren rename))

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
  simp only [activeChildExpr, evaluateExpression, Expr.orte, NutzlastExpr.orte, preserved.1,
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

end Gabbro.Grammatik.Async.Representation
