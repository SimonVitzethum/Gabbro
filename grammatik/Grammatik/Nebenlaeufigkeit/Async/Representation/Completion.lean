module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.Reachability
public import Grammatik.Nebenlaeufigkeit.Async.Segment.Model

@[expose] public section

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {V : Vertrag D} {Λ : List (Res D)}
  {types : TypeResolution} {f : AsyncFn}

/-- A successful checked release reaches the actual cleared G record.
    The release itself is responsible for consuming the entire inventory. -/
theorem cancelEpilogue_encoded {Γ : Ctx} {l : Bool}
    (inventory : Inventory D) (empty : inventory.owned Phase.cancelled = [])
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (state : Var Γ (stateType types f)) (release : Stmt D V l Γ Λ [])
    (before after : World D) (environment environment' : Env D Γ)
    (released : execStmt oracle passes calls release before environment = .ok after environment') :
    execBlock oracle passes calls (cancelEpilogue types f state release) before environment =
        .ok after (environment'.set state (cancelledValue types f D)) ∧
      encode D types f State.cancelled = some (cancelledValue types f D) :=
  ⟨cancelEpilogue_success types f oracle passes calls state release
      before after environment environment' released,
    inv_encoded f types inventory State.cancelled _ (cancelled_inv types f inventory empty)⟩

def completedIndex (types : TypeResolution) (f : AsyncFn) :
    Fin (stateCases types f).length :=
  ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩

def completedValue (D : Deklaration) (types : TypeResolution) (f : AsyncFn)
    (result : Wert D (types.ordinary f.resultType)) : Wert D (stateType types f) :=
  (⟨completedIndex types f, (result, ())⟩, ())

def completedExpr {Γ : Ctx} (value : Expr D Γ Λ (types.ordinary f.resultType)) :
    Expr D Γ Λ (stateType types f) :=
  stateExpr types f (completedIndex types f)
    (.val (.prod (types.recordName [5]) (.cons value .nil)))

/-- Ready storage contains the typed return and the completed tag. No
    saved frame or resource inventory remains in the future. -/
theorem completed_inv (inventory : Inventory D) (value : Value D)
    (payload : Wert D (types.ordinary f.resultType))
    (typed : valueAt D (types.ordinary f.resultType) value = some payload)
    (empty : inventory.owned Phase.completed = []) :
    Inv f types inventory (.completed value ⟨[], []⟩) (completedValue D types f payload) := by
  have marks : MarksRep inventory Phase.completed
      (State.completed (Child := Child D types) value ⟨[], []⟩) := by
    simp only [MarksRep, State.marks, empty, List.map_nil]
  exact .later _ _ _ _ rfl (.first _ _ _ _ (.completed value payload typed) marks)

/-- The induced model's final segment reads the actual typed G return
    expression. Its Ready event carries the original marks, and the
    resulting completed record contains the returned value only. -/
theorem final_segment_encoded
    (elaboration : Elaboration D V Λ types f)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (prices : D.Fn → Nat) (normal : PollRuns elaboration calls)
    (inventory : Inventory D) (empty : inventory.owned Phase.completed = [])
    (resolved : BoundExpression D Λ)
    (known : elaboration.expression f.result = some resolved)
    (resultType : resolved.result = types.ordinary f.resultType)
    (frame : Frame (Value D)) (environment : Env D (resolved.locals.map Prod.snd))
    (restored : localsEnv D resolved.locals frame = some environment)
    (world : World D) :
    let result := evaluateExpression resolved.expression world environment
    let value := Value.typed resolved.result result.1
    let model := inducedModel elaboration calls prices normal
    let done := State.completed (Child := Child D types) value ⟨[], []⟩
    machineStep model (asyncExpand model f) (.running f.body.length frame) world =
        (.ready value frame.marks, done, result.2.1, result.2.2 + 1) ∧
      Inv f types inventory done (completedValue D types f (resultType ▸ result.1)) ∧
      encode D types f done = some (completedValue D types f (resultType ▸ result.1)) := by
  let result := evaluateExpression resolved.expression world environment
  let value := Value.typed resolved.result result.1
  let model := inducedModel elaboration calls prices normal
  let done := State.completed (Child := Child D types) value ⟨[], []⟩
  have atType (actual expected : Ty) (same : actual = expected) (payload : Wert D actual) :
      valueAt D expected (Value.typed actual payload) = some (same ▸ payload) := by
    subst expected
    exact valueAt_typed D actual payload
  have typed := atType resolved.result (types.ordinary f.resultType) resultType result.1
  have represented := completed_inv (f := f) inventory value _ typed empty
  refine ⟨?_, represented, inv_encoded f types inventory done _ represented⟩
  change machineStep model (asyncExpand model f) (.running f.body.length frame) world =
    (.ready value frame.marks, done, result.2.1, result.2.2 + 1)
  simp only [machineStep, asyncExpand_end]
  have evaluates : model.evaluate f.result frame world = (value, result.2.1, result.2.2) := by
    exact evaluateBound_resolved elaboration f.result resolved known frame environment restored world
  change (let (value, world', cost) := model.evaluate f.result frame world
      (Event.ready value frame.marks, State.completed (Child := Child D types) value (clear frame),
        world', cost + 1)) = _
  rw [evaluates]
  rfl

/-- Evaluate the return expression once and replace the saved state by the
    completed record. The temporary result is local to the generated block. -/
def finalBlock {l : Bool} (resolved : BoundExpression D Λ)
    (resultType : resolved.result = types.ordinary f.resultType) :
    Block D V l (stateType types f :: resolved.locals.map Prod.snd) Λ Λ :=
  evaluateBlock (resolved.lifted (stateType types f)) .here
    (completedExpr (resultType ▸ (Expr.var .here :
      Expr D (resolved.result :: stateType types f :: resolved.locals.map Prod.snd) Λ resolved.result)))

theorem finalBlock_exec {l : Bool} (resolved : BoundExpression D Λ)
    (resultType : resolved.result = types.ordinary f.resultType)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (record : Wert D (stateType types f)) (world : World D)
    (locals : Env D (resolved.locals.map Prod.snd)) :
    let result := evaluateExpression resolved.expression world locals
    execBlock oracle passes calls (finalBlock (V := V) (l := l) resolved resultType)
        world (.cons record locals) =
      .ok result.2.1 (.cons (completedValue D types f (resultType ▸ result.1)) locals) := by
  unfold finalBlock
  rw [evaluateBlock_exec, resolved.liftedPlaces]
  have successor {Γ : Ctx} {actual : Ty}
      (same : actual = types.ordinary f.resultType) (value : Wert D actual)
      (world : World D) (environment : Env D Γ) :
      let expression : Expr D (actual :: Γ) Λ (stateType types f) :=
        completedExpr (same ▸ (Expr.var .here : Expr D (actual :: Γ) Λ actual))
      expression.orte = [] ∧
        eval world expression world (.cons value environment) =
          completedValue D types f (same ▸ value) := by
    subst actual
    exact ⟨rfl, rfl⟩
  let read := world.lese Λ resolved.expression.orte
  have payload := successor resultType
    (eval read (resolved.lifted (stateType types f)) read (.cons record locals))
    read (.cons record locals)
  dsimp only at payload ⊢
  have noRead (world : World D) : world.lese Λ [] = world := rfl
  rw [payload.1, noRead, payload.2, resolved.liftedEval]
  rfl

/-- The generated final block and the semantic final step return the same
    world and completed state. The semantic Ready event carries the frame
    marks, which this block still leaves in the surrounding G inventory. -/
theorem finalBlock_simulates {l : Bool}
    (elaboration : Elaboration D V Λ types f)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (prices : D.Fn → Nat) (normal : PollRuns elaboration calls)
    (inventory : Inventory D) (empty : inventory.owned Phase.completed = [])
    (resolved : BoundExpression D Λ)
    (known : elaboration.expression f.result = some resolved)
    (resultType : resolved.result = types.ordinary f.resultType)
    (frame : Frame (Value D)) (locals : Env D (resolved.locals.map Prod.snd))
    (restored : localsEnv D resolved.locals frame = some locals)
    (record : Wert D (stateType types f)) (world : World D) :
    ∃ value after cost next,
      machineStep (inducedModel elaboration calls prices normal)
        (asyncExpand (inducedModel elaboration calls prices normal) f)
        (.running f.body.length frame) world =
          (.ready value frame.marks, .completed value ⟨[], []⟩, after, cost) ∧
      encode D types f (.completed value ⟨[], []⟩) = some next ∧
      execBlock oracle passes calls (finalBlock (V := V) (l := l) resolved resultType)
        world (.cons record locals) = .ok after (.cons next locals) := by
  obtain ⟨step, _, encoded⟩ := final_segment_encoded elaboration calls prices normal
    inventory empty resolved known resultType frame locals restored world
  exact ⟨_, _, _, _, step, encoded,
    finalBlock_exec resolved resultType oracle passes calls record world locals⟩

end Gabbro.Grammatik.Async.Representation
