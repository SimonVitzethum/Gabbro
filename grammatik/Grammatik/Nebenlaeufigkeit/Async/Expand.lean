module

public import Grammatik.Nebenlaeufigkeit.Async.Semantik

namespace Gabbro.Grammatik.Async

/-! Defunctionalisation into a finite table. Callbacks below are immutable
    CODE, never fields of a Future. Runtime storage is exactly Syntax.State.
    This is the semantic transformation target, not yet a canonical G Block.
    The remaining G reification obligation is stated in Regeln.lean. -/

/-- Ordinary straight-line code and child constructors. Neither instruction
    stores a source continuation or an async surface expression. -/
public inductive Instruction (Value Child W : Type) where
  | evaluate (name : String) (code : Frame Value → W → Value × W × Nat)
  | construct (name : String) (code : Frame Value → W → Task Value Child × W × Nat)

public structure Program (Value Child W : Type) where
  code : List (Instruction Value Child W)
  finish : Frame Value → W → Value × W × Nat

/-- The constructor callback is code belonging to the generated function.
    It is invoked on first reaching the await, never on subsequent polls. -/
@[expose] public def compileCommand (model : Model Value Child W) : Command → Instruction Value Child W
  | .bind name expr _ => .evaluate name (model.evaluate expr)
  | .await name expr _ => .construct name (fun frame => makeTask model frame expr)

/-- Finite state-table expansion, with every source instruction assigned a
    deterministic tag. Tables and match suffice to implement its dispatch;
    reification as typed G forms is still required before source admission. -/
@[expose] public def asyncExpand (model : Model Value Child W) (f : AsyncFn) : Program Value Child W :=
  { code := f.body.map (compileCommand model), finish := model.evaluate f.result }

/-- An invalid wait tag is refused. A running tag is meaningful only under
    tagValid; preservation is established by the simulation relation. -/
@[expose] public def machineStep (model : Model Value Child W) (p : Program Value Child W) :
    State Value Child → W → Event Value × State Value Child × W × Nat
  | .running tag frame, world =>
    match p.code.drop tag with
    | [] =>
      let (value, world', cost) := p.finish frame world
      (.ready value frame.marks, .completed value (clear frame), world', cost + 1)
    | .evaluate name code :: _ =>
      let (value, world', cost) := code frame world
      (.next, .running (tag + 1) (save frame name value), world', cost + 1)
    | .construct _ code :: _ =>
      let (child, world', cost) := code frame world
      (.next, .waiting tag frame child, world', cost + 1)
  | .waiting tag frame child, world =>
    match p.code.drop tag with
    | .construct name _ :: _ =>
      let (result, child', world', cost) := pollTask model child world
      match result with
      | .pending => (.pending, .waiting tag frame child', world', cost + 1)
      | .ready value => (.next, .running (tag + 1) (save frame name value), world', cost + 1)
    | _ => (.refused, .waiting tag frame child, world, 0)
  | .completed value frame, world => (.refused, .completed value frame, world, 0)
  | .cancelled, world => (.refused, .cancelled, world, 0)

/-- Poll closure stops at the first externally observable result. -/
public inductive MachinePoll (model : Model Value Child W) (p : Program Value Child W) :
    State Value Child → W → Event Value → State Value Child → W → Nat → Prop where
  | stop (h : machineStep model p source before = (event, target, after, cost))
      (terminal : event ≠ .next) : MachinePoll model p source before event target after cost
  | next (h : machineStep model p source before = (.next, middle, between, cost))
      (rest : MachinePoll model p middle between event target after remaining) :
      MachinePoll model p source before event target after (cost + remaining)

/-- The ownership receipt leaves the world unchanged; cleanup is explicit. -/
@[expose] public def machineCancel (state : State Value Child) (world : W) :
    List Nat × State Value Child × W := (state.marks, .cancelled, world)

/-- Exact finite code-table elimination: there is one ordinary code entry per
    source command, and no async Command in the target instruction type. -/
public theorem asyncExpand_length (model : Model Value Child W) (f : AsyncFn) :
    (asyncExpand model f).code.length = f.body.length := by
  simp only [asyncExpand, List.length_map]

/-- The final running tag is the ordinary return segment. -/
public theorem asyncExpand_end (model : Model Value Child W) (f : AsyncFn) :
    (asyncExpand model f).code.drop f.body.length = [] := by
  simp only [asyncExpand, ← List.length_map (compileCommand model) (as := f.body),
    List.drop_length]

public theorem machine_poll_after_ready (model : Model Value Child W)
    (p : Program Value Child W) (value : Value) (frame : Frame Value) (world : W) :
    machineStep model p (.completed value frame) world =
      (.refused, .completed value frame, world, 0) := rfl

public theorem machine_cancel_empty (s : State Value Child) (world : W) :
    (machineCancel s world).2.1.marks = [] := rfl

public theorem machine_cancel_twice (s : State Value Child) (world : W) :
    (machineCancel (machineCancel s world).2.1 (machineCancel s world).2.2).1 = [] := rfl

end Gabbro.Grammatik.Async
