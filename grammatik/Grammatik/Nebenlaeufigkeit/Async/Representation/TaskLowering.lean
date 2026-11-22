module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.WaitingLowering
import Lean.Elab.Tactic.Omega

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {V : Vertrag D} {Λ : List (Res D)} {l : Bool} {Γ : Ctx}
  {types : TypeResolution} {f : AsyncFn}

/-- Read the tag of an existing task slot without creating a world event. -/
public theorem storedTag_active {active result : Ty}
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (slot : Var Γ (.sum [some active, some result]))
    (poll : Block D V l (active :: Γ) Λ Λ) (cached : Block D V l (result :: Γ) Λ Λ)
    (world : World D) (env : Env D Γ) (payload : Wert D active)
    (stored : env.get slot = readyAnswer D active result payload) :
    execStmt oracle passes calls (.onTag (.var slot) (.cons poll (.cons cached .nil))) world env =
      (execBlock oracle passes calls poll world (.cons payload env)).schrumpf := by
  simp only [execStmt, Expr.orte, World.lese, World.merke, List.map_nil, List.nil_append, eval, stored]
  rfl

public theorem storedTag_cached {active result : Ty}
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (slot : Var Γ (.sum [some active, some result]))
    (poll : Block D V l (active :: Γ) Λ Λ) (cached : Block D V l (result :: Γ) Λ Λ)
    (world : World D) (env : Env D Γ) (payload : Wert D result)
    (stored : env.get slot = pendingAnswer D active result payload) :
    execStmt oracle passes calls (.onTag (.var slot) (.cons poll (.cons cached .nil))) world env =
      (execBlock oracle passes calls cached world (.cons payload env)).schrumpf := by
  simp only [execStmt, Expr.orte, World.lese, World.merke, List.map_nil, List.nil_append, eval, stored]
  rfl

/-- An inner leaf poll saves its own task slot. A finished leaf is skipped
    on subsequent polls of its enclosing join. -/
@[expose] public def leafTaskStmt (path : List Nat) (name : String) (args : List Parser.SExpr)
    (callee : AwaitedCall D V Λ types name) (slot : Var Γ (taskStorageType types path (.call name args))) :
    Stmt D V l Γ Λ Λ :=
  .onTag (.var slot) (.cons
    (childPollBlock callee (leafPollArguments callee .here)
      (.cons (.cons (.assignVar (.there (.there (.there slot)))
          (.case [some (types.childState name), some (types.childResult name)]
            ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩ (.val (.var .here)))) .nil)
        (.cons (.cons (.assignVar (.there (.there (.there slot)))
          (activeLeafExpr types path name args (.var .here))) .nil) .nil)))
    (.cons .nil .nil))

/-- A task step updates only its own private value slot and preserves the
    exact world and error returned by the ordinary calls. -/
public def TaskStepRep (types : TypeResolution) (path : List Nat) (future : FutureExpr)
    (slot : Var Γ (taskStorageType types path future)) (env : Env D Γ) (output : Ausgang V l Γ)
    (model : Except (Logik D ⊕ Hardware D)
      (Poll (Value D) × Task (Value D) (Child D types) × World D × Nat)) : Prop :=
  match model with
  | .error (.inl failure) => output = .logik failure
  | .error (.inr failure) => output = .hardware failure
  | .ok (_, successor, after, _) =>
    ∃ value, output = .ok after (env.set slot value) ∧ TaskRep D types path future successor value

private theorem setCurrent {D : Deklaration} {Γ : Ctx} {τ : Ty}
    (slot : Var Γ τ) (env : Env D Γ) : env.set slot (env.get slot) = env := by
  induction slot with
  | here => cases env; rfl
  | there slot ih =>
    cases env with
    | cons value env => exact congrArg (Env.cons value) (ih env)

/-- A leaf of a join uses the actual call result, including on error.
    The representation of a cached result suppresses the ordinary call. -/
public theorem leafTaskStmt_simulates (elaboration : Elaboration D V Λ types f)
    (path : List Nat) (name : String) (args : List Parser.SExpr)
    (callee : AwaitedCall D V Λ types name) (known : elaboration.callee name = some callee)
    (slot : Var Γ (taskStorageType types path (.call name args)))
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn) (prices : D.Fn → Nat)
    (world : World D) (env : Env D Γ) (task : Task (Value D) (Child D types))
    (represented : TaskRep D types path (.call name args) task (env.get slot)) :
    TaskStepRep types path (.call name args) slot env
      (execStmt oracle passes calls (leafTaskStmt (V := V) (l := l) path name args callee slot) world env)
      (runTaskPoll elaboration calls prices task world) := by
  generalize same : env.get slot = storage at represented
  cases represented with
  | callReady typed =>
    simp only [leafTaskStmt, execStmt, Expr.orte, World.lese, World.merke, List.map_nil, List.nil_append, eval]
    erw [same]
    simp only [pendingAnswer, readyAnswer, execArms]
    simp only [runTaskPoll, pollTaskWith, pure, Except.pure, TaskStepRep]
    refine ⟨_, ?_, .callReady path name args (by assumption)⟩
    rw [← same, setCurrent]
    rfl
  | callActive _ _ _ payload =>
    simp only [leafTaskStmt, execStmt, Expr.orte, World.lese, World.merke, List.map_nil, List.nil_append, eval]
    erw [same]
    simp only [pendingAnswer, readyAnswer, execArms]
    rw [childPollBlock, waitingBlock_exec_outcome]
    obtain ⟨silent, evaluated⟩ := leafPollArguments_eval callee .here world world (.cons payload env)
    have noRead : world.lese Λ [] = world := rfl
    erw [silent, noRead, evaluated]
    simp only [Env.get]
    cases returned : calls callee.poll world (pollEnvironment callee payload) with
    | why _ reason => exact keinGrund callee.pollInfallible reason
    | logik _ | hardware _ =>
      simp only [runTaskPoll, pollTaskWith, known, runChildPoll, returned, decodeChildOutcome,
        bind, Except.bind, TaskStepRep, Ausgang.schrumpf] <;> rfl
    | ok after answer =>
      simp only [runTaskPoll, pollTaskWith, known, runChildPoll, returned, decodeChildOutcome]
      generalize ergWert callee.pollResult answer = reply
      obtain ⟨⟨tag, bound⟩, value⟩ := reply
      cases tag with
      | zero =>
        exact ⟨_, rfl, .callReady path name args (valueAt_typed D _ value)⟩
      | succ tag =>
        cases tag with
        | zero => exact ⟨_, rfl, .callActive path name args value⟩
        | succ tag =>
          have invalid : tag + 2 < 2 := bound
          omega

end Gabbro.Grammatik.Async.Representation
