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

/-- Ready storage contains the typed return and the completed tag. No
    saved frame or resource inventory remains in the future. -/
theorem completed_inv (inventory : Inventory D) (value : Value D)
    (payload : Wert D (types.ordinary f.resultType))
    (typed : valueAt D (types.ordinary f.resultType) value = some payload)
    (empty : inventory.owned Phase.completed = []) :
    ∃ record, Inv f types inventory (.completed value ⟨[], []⟩) record := by
  have marks : MarksRep inventory Phase.completed
      (State.completed (Child := Child D types) value ⟨[], []⟩) := by
    simp only [MarksRep, State.marks, empty, List.map_nil]
  let cases := commandPhases 0 f.body
  let completed := firstPhaseValue D types f Phase.completed cases (payload, ())
  refine ⟨(laterPhaseValue D types f Phase.cancelled (Phase.completed :: cases) completed, ()), ?_⟩
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
      ∃ record, Inv f types inventory done record ∧ encode D types f done = some record := by
  let result := evaluateExpression resolved.expression world environment
  let value := Value.typed resolved.result result.1
  let model := inducedModel elaboration calls prices normal
  let done := State.completed (Child := Child D types) value ⟨[], []⟩
  have atType (actual expected : Ty) (same : actual = expected) (payload : Wert D actual) :
      valueAt D expected (Value.typed actual payload) = some (same ▸ payload) := by
    subst expected
    exact valueAt_typed D actual payload
  have typed := atType resolved.result (types.ordinary f.resultType) resultType result.1
  obtain ⟨record, represented⟩ :=
    completed_inv (f := f) inventory value _ typed empty
  refine ⟨?_, record, represented, inv_encoded f types inventory done record represented⟩
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

end Gabbro.Grammatik.Async.Representation
