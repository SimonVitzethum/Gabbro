module

public import Grammatik.Nebenlaeufigkeit.Async.Expand
import Init.Data.List.TakeDrop

namespace Gabbro.Grammatik.Async

/-- Reconstruction is a proof device, not stored runtime data. An invalid wait
    tag decodes as a refused/cancelled configuration; AsyncOk callers must
    start with create and retain reachable states. -/
@[expose] public def decode (f : AsyncFn) : State Value Child → Direct Value Child
  | .running tag frame => .running (f.body.drop tag) frame
  | .waiting tag frame child =>
    match f.body.drop tag with
    | .await name _ _ :: rest => .waiting name rest frame child
    | _ => .cancelled
  | .completed value _ => .completed value
  | .cancelled => .cancelled

public theorem table_drop (model : Model Value Child) (f : AsyncFn) (tag : Nat) :
    (asyncExpand model f).code.drop tag =
      (f.body.drop tag).map (compileCommand model) := by
  simp only [asyncExpand, List.map_drop]

public theorem drop_compiled (model : Model Value Child) (body : List Command) (tag : Nat) :
    (body.map (compileCommand model)).drop tag = (body.drop tag).map (compileCommand model) := by
  simp only [List.map_drop]

/-- One generated dispatch step commutes with direct-style evaluation,
    including changed Pending children and the exact observed cost. -/
public theorem step_commutes (model : Model Value Child) (f : AsyncFn)
    (source : State Value Child) :
    (let (event, target, cost) := machineStep model (asyncExpand model f) source
     (event, decode f target, cost)) = directStep model f (decode f source) := by
  cases source with
  | running tag frame =>
    cases h : f.body.drop tag with
    | nil =>
      simp only [machineStep, table_drop, drop_compiled, h, decode, directStep, asyncExpand, List.map_nil, List.map_cons]
    | cons command rest =>
      have tail : f.body.drop (tag + 1) = rest := by
        rw [List.drop_add_one_eq_tail_drop, h]
        rfl
      cases command with
      | bind name expr bound =>
        cases he : model.evaluate expr frame with
        | mk value cost =>
          simp only [machineStep, table_drop, drop_compiled, h, compileCommand, decode, directStep, tail, he, List.map_nil, List.map_cons]
      | await name expr boundary =>
        cases hm : makeTask model frame expr with
        | mk child cost =>
          simp only [machineStep, table_drop, drop_compiled, h, compileCommand, decode, directStep, hm, List.map_nil, List.map_cons]
  | waiting tag frame child =>
    cases h : f.body.drop tag with
    | nil => simp only [machineStep, table_drop, drop_compiled, h, decode, directStep, List.map_nil, List.map_cons]
    | cons command rest =>
      have tail : f.body.drop (tag + 1) = rest := by
        rw [List.drop_add_one_eq_tail_drop, h]
        rfl
      cases command with
      | bind name expr bound =>
        simp only [machineStep, table_drop, drop_compiled, h, compileCommand, decode, directStep, List.map_nil, List.map_cons]
      | await name expr boundary =>
        cases hp : pollTask model child with
        | mk result payload =>
          cases payload with
          | mk child' cost =>
            cases result <;>
              simp only [machineStep, table_drop, drop_compiled, h, compileCommand, decode, directStep, hp, tail, List.map_nil, List.map_cons]
  | completed value frame => rfl
  | cancelled => rfl

/-- Equality is stronger than a stuttering simulation for this table model. -/
public theorem step_refines (model : Model Value Child) (f : AsyncFn)
    {source target : State Value Child} {event : Event Value} {cost : Nat}
    (h : machineStep model (asyncExpand model f) source = (event, target, cost)) :
    directStep model f (decode f source) = (event, decode f target, cost) := by
  have commute := step_commutes model f source
  rw [h] at commute
  exact commute.symm

public theorem poll_refines (model : Model Value Child) (f : AsyncFn)
    {source target : State Value Child} {event : Event Value} {cost : Nat}
    (h : MachinePoll model (asyncExpand model f) source event target cost) :
    DirectPoll model f (decode f source) event (decode f target) cost := by
  induction h with
  | stop step terminal => exact .stop (step_refines model f step) terminal
  | next step rest ih => exact .next (step_refines model f step) ih

/-- A finite sequence of polls; no scheduler fairness premise is hidden here. -/
public inductive MachineTrace (model : Model Value Child) (p : Program Value Child) :
    State Value Child → List (Event Value × Nat) → State Value Child → Prop where
  | nil : MachineTrace model p state [] state
  | cons (head : MachinePoll model p source event middle cost)
      (tail : MachineTrace model p middle observations target) :
      MachineTrace model p source ((event, cost) :: observations) target

public inductive DirectTrace (model : Model Value Child) (f : AsyncFn) :
    Direct Value Child → List (Event Value × Nat) → Direct Value Child → Prop where
  | nil : DirectTrace model f state [] state
  | cons (head : DirectPoll model f source event middle cost)
      (tail : DirectTrace model f middle observations target) :
      DirectTrace model f source ((event, cost) :: observations) target

/-- Generic trace elimination for the semantic state-table transformation.
    This does NOT assert that an emitted canonical G program has been checked. -/
public theorem async_elimination (model : Model Value Child) (f : AsyncFn)
    {source target : State Value Child} {observations : List (Event Value × Nat)}
    (h : MachineTrace model (asyncExpand model f) source observations target) :
    DirectTrace model f (decode f source) observations (decode f target) := by
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons (poll_refines model f head) ih

public theorem decode_create (f : AsyncFn) (frame : Frame Value) :
    decode f (create (Child := Child) f frame).state = .running f.body frame := rfl

end Gabbro.Grammatik.Async
