module

public import Grammatik.Nebenlaeufigkeit.Async.Expand
import Init.Data.List.TakeDrop

namespace Gabbro.Grammatik.Async

@[expose] public def decode (f : AsyncFn) : State Value Child → Direct Value Child
  | .running tag frame => .running (f.body.drop tag) frame
  | .waiting tag frame child =>
    match f.body.drop tag with
    | .await name _ _ :: rest => .waiting name rest frame child
    | _ => .cancelled
  | .completed value _ => .completed value
  | .cancelled => .cancelled

public theorem table_drop (model : Model Value Child W) (f : AsyncFn) (tag : Nat) :
    (asyncExpand model f).code.drop tag =
      (f.body.drop tag).map (compileCommand model) := by
  simp only [asyncExpand, List.map_drop]

public theorem drop_compiled (model : Model Value Child W) (body : List Command) (tag : Nat) :
    (body.map (compileCommand model)).drop tag = (body.drop tag).map (compileCommand model) := by
  simp only [List.map_drop]

/-- Dispatch preserves event, world and exact cost, including Pending writes. -/
public theorem step_commutes (model : Model Value Child W) (f : AsyncFn)
    (source : State Value Child) (world : W) :
    (let (event, target, world', cost) := machineStep model (asyncExpand model f) source world
     (event, decode f target, world', cost)) = directStep model f (decode f source) world := by
  cases source with
  | running tag frame =>
    cases h : f.body.drop tag with
    | nil =>
      simp only [machineStep, table_drop, drop_compiled, h, decode, directStep,
        asyncExpand, List.map_nil, List.map_cons]
    | cons command rest =>
      have tail : f.body.drop (tag + 1) = rest := by
        rw [List.drop_add_one_eq_tail_drop, h]
        rfl
      cases command with
      | bind name expr bound =>
        rcases he : model.evaluate expr frame world with ⟨value, world', cost⟩
        simp only [machineStep, table_drop, drop_compiled, h, compileCommand,
          decode, directStep, tail, he, List.map_nil, List.map_cons]
      | await name expr boundary =>
        rcases hm : makeTask model frame expr world with ⟨child, world', cost⟩
        simp only [machineStep, table_drop, drop_compiled, h, compileCommand,
          decode, directStep, hm, List.map_nil, List.map_cons]
  | waiting tag frame child =>
    cases h : f.body.drop tag with
    | nil =>
      simp only [machineStep, table_drop, drop_compiled, h, decode, directStep,
        List.map_nil, List.map_cons]
    | cons command rest =>
      have tail : f.body.drop (tag + 1) = rest := by
        rw [List.drop_add_one_eq_tail_drop, h]
        rfl
      cases command with
      | bind name expr bound =>
        simp only [machineStep, table_drop, drop_compiled, h, compileCommand,
          decode, directStep, List.map_nil, List.map_cons]
      | await name expr boundary =>
        rcases hp : pollTask model child world with ⟨result, child', world', cost⟩
        cases result <;>
          simp only [machineStep, table_drop, drop_compiled, h, compileCommand,
            decode, directStep, hp, tail, List.map_nil, List.map_cons]
  | completed value frame => rfl
  | cancelled => rfl

public theorem step_refines (model : Model Value Child W) (f : AsyncFn)
    {source target : State Value Child} {before after : W} {event : Event Value} {cost : Nat}
    (h : machineStep model (asyncExpand model f) source before = (event, target, after, cost)) :
    directStep model f (decode f source) before = (event, decode f target, after, cost) := by
  have commute := step_commutes model f source before
  rw [h] at commute
  exact commute.symm

public theorem poll_refines (model : Model Value Child W) (f : AsyncFn)
    {source target : State Value Child} {before after : W} {event : Event Value} {cost : Nat}
    (h : MachinePoll model (asyncExpand model f) source before event target after cost) :
    DirectPoll model f (decode f source) before event (decode f target) after cost := by
  induction h with
  | stop step terminal => exact .stop (step_refines model f step) terminal
  | next step rest ih => exact .next (step_refines model f step) ih

/-- Observations retain event/cost pairs; endpoints additionally expose worlds.
    A poll sequence composes only when its intermediate worlds agree. -/
public inductive MachineTrace (model : Model Value Child W) (p : Program Value Child W) :
    State Value Child → W → List (Event Value × Nat) → State Value Child → W → Prop where
  | nil : MachineTrace model p state world [] state world
  | cons (head : MachinePoll model p source before event middle between cost)
      (tail : MachineTrace model p middle between observations target after) :
      MachineTrace model p source before ((event, cost) :: observations) target after

public inductive DirectTrace (model : Model Value Child W) (f : AsyncFn) :
    Direct Value Child → W → List (Event Value × Nat) → Direct Value Child → W → Prop where
  | nil : DirectTrace model f state world [] state world
  | cons (head : DirectPoll model f source before event middle between cost)
      (tail : DirectTrace model f middle between observations target after) :
      DirectTrace model f source before ((event, cost) :: observations) target after

/-- Semantic table elimination; canonical G reification remains a separate duty. -/
public theorem async_elimination (model : Model Value Child W) (f : AsyncFn)
    {source target : State Value Child} {before after : W}
    {observations : List (Event Value × Nat)}
    (h : MachineTrace model (asyncExpand model f) source before observations target after) :
    DirectTrace model f (decode f source) before observations (decode f target) after := by
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons (poll_refines model f head) ih

public theorem decode_create (f : AsyncFn) (frame : Frame Value) :
    decode f (create (Child := Child) f frame).state = .running f.body frame := rfl

end Gabbro.Grammatik.Async
