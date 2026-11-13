module

public import Grammatik.Nebenlaeufigkeit.Async.Semantik

namespace Gabbro.Grammatik.Async

/-! Defunctionalisation into a finite table. Callbacks below are immutable
    CODE, never fields of a Future. Runtime storage is exactly Syntax.State.
    This is the semantic transformation target, not yet a canonical G Block.
    The remaining G reification obligation is stated in Regeln.lean. -/

/-- Ordinary straight-line code and child constructors. Neither instruction
    stores a source continuation or an async surface expression. -/
public inductive Instruction (Value Child : Type) where
  | evaluate (name : String) (code : Frame Value → Value × Nat)
  | construct (name : String) (code : Frame Value → Task Value Child × Nat)

public structure Program (Value Child : Type) where
  code : List (Instruction Value Child)
  finish : Frame Value → Value × Nat

/-- The constructor callback is code belonging to the generated function.
    It is invoked on first reaching the await, never on subsequent polls. -/
@[expose] public def compileCommand (model : Model Value Child) : Command → Instruction Value Child
  | .bind name expr _ => .evaluate name (model.evaluate expr)
  | .await name expr _ => .construct name (fun frame => makeTask model frame expr)

/-- Finite state-table expansion, with every source instruction assigned a
    deterministic tag. Tables and match suffice to implement its dispatch;
    reification as typed G forms is still required before source admission. -/
@[expose] public def asyncExpand (model : Model Value Child) (f : AsyncFn) : Program Value Child :=
  { code := f.body.map (compileCommand model), finish := model.evaluate f.result }

/-- An invalid wait tag is refused. A running tag is meaningful only under
    tagValid; preservation is established by the simulation relation. -/
@[expose] public def machineStep (model : Model Value Child) (p : Program Value Child) :
    State Value Child → Event Value × State Value Child × Nat
  | .running tag frame =>
    match p.code.drop tag with
    | [] =>
      let (value, cost) := p.finish frame
      (.ready value frame.marks, .completed value (clear frame), cost + 1)
    | .evaluate name code :: _ =>
      let (value, cost) := code frame
      (.next, .running (tag + 1) (save frame name value), cost + 1)
    | .construct _ code :: _ =>
      let (child, cost) := code frame
      (.next, .waiting tag frame child, cost + 1)
  | .waiting tag frame child =>
    match p.code.drop tag with
    | .construct name _ :: _ =>
      let (result, child', cost) := pollTask model child
      match result with
      | .pending => (.pending, .waiting tag frame child', cost + 1)
      | .ready value => (.next, .running (tag + 1) (save frame name value), cost + 1)
    | _ => (.refused, .waiting tag frame child, 0)
  | .completed value frame => (.refused, .completed value frame, 0)
  | .cancelled => (.refused, .cancelled, 0)

/-- Poll closure stops at the first externally observable result. -/
public inductive MachinePoll (model : Model Value Child) (p : Program Value Child) :
    State Value Child → Event Value → State Value Child → Nat → Prop where
  | stop (h : machineStep model p source = (event, target, cost))
      (terminal : event ≠ .next) : MachinePoll model p source event target cost
  | next (h : machineStep model p source = (.next, middle, cost))
      (rest : MachinePoll model p middle event target remaining) :
      MachinePoll model p source event target (cost + remaining)

/-- Cancellation is an ownership transfer to a destructor, never a silent
    release. Regeln.DropDuty specifies what must consume this receipt. -/
@[expose] public def machineCancel (state : State Value Child) : List Nat × State Value Child :=
  (state.marks, .cancelled)

/-- Exact finite code-table elimination: there is one ordinary code entry per
    source command, and no async Command in the target instruction type. -/
public theorem asyncExpand_length (model : Model Value Child) (f : AsyncFn) :
    (asyncExpand model f).code.length = f.body.length := by
  simp only [asyncExpand, List.length_map]

/-- The final running tag is the ordinary return segment. -/
public theorem asyncExpand_end (model : Model Value Child) (f : AsyncFn) :
    (asyncExpand model f).code.drop f.body.length = [] := by
  simp only [asyncExpand, ← List.length_map (compileCommand model) (as := f.body),
    List.drop_length]

public theorem machine_poll_after_ready (model : Model Value Child)
    (p : Program Value Child) (value : Value) (frame : Frame Value) :
    machineStep model p (.completed value frame) =
      (.refused, .completed value frame, 0) := rfl

public theorem machine_cancel_empty (s : State Value Child) :
    (machineCancel s).2.marks = [] := rfl

public theorem machine_cancel_twice (s : State Value Child) :
    (machineCancel (machineCancel s).2).1 = [] := rfl

end Gabbro.Grammatik.Async
