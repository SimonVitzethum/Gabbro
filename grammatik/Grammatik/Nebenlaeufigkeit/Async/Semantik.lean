module

public import Grammatik.Nebenlaeufigkeit.Async.Syntax

namespace Gabbro.Grammatik.Async
open Parser

public inductive Poll (Value : Type) where
  | ready (value : Value)
  | pending

/-- Interpretation of ordinary expressions and external child futures.
    This is a specification parameter, NOT a hardware assumption. Connecting
    it to ordinary G evaluation and proving its contracts is a user/compiler
    obligation. Costs include all work performed by the respective operation.
    Child handles carry no authority outside their enclosing Frame.marks. -/
public structure Model (Value Child : Type) where
  evaluate : SExpr → Frame Value → Value × Nat
  newChild : String → List Value → Child
  pollChild : Child → Poll Value × Child × Nat
  pair : Value → Value → Value

/-- A saved assignment moves the authority list unchanged. Local values alone
    confer no permissions, so copying a local cannot duplicate a mark. -/
@[expose] public def save (frame : Frame Value) (name : String) (value : Value) : Frame Value :=
  { frame with values := (name, value) :: frame.values }

/-- After returning ownership, a completed record has no residual authority. -/
@[expose] public def clear (frame : Frame Value) : Frame Value := { values := [], marks := [] }

@[expose] public def evalArguments (model : Model Value Child) (frame : Frame Value) :
    List SExpr → List Value × Nat
  | [] => ([], 0)
  | e :: es =>
    let (v, c) := model.evaluate e frame
    let (vs, cs) := evalArguments model frame es
    (v :: vs, c + cs)

/-- Construction evaluates arguments but never polls a child. -/
@[expose] public def makeTask (model : Model Value Child) (frame : Frame Value) :
    FutureExpr → Task Value Child × Nat
  | .call name args =>
    let (values, cost) := evalArguments model frame args
    (.leaf (model.newChild name values), cost + 1)
  | .join left right =>
    let (l, lc) := makeTask model frame left
    let (r, rc) := makeTask model frame right
    (.join l r, lc + rc + 1)

/-- Both siblings get one poll in deterministic left-to-right order. A pending
    child may change its state; that updated state is ALWAYS saved. -/
@[expose] public def pollTask (model : Model Value Child) :
    Task Value Child → Poll Value × Task Value Child × Nat
  | .ready value => (.ready value, .ready value, 0)
  | .leaf child =>
    let (result, child', cost) := model.pollChild child
    match result with
    | .ready value => (.ready value, .ready value, cost)
    | .pending => (.pending, .leaf child', cost)
  | .join left right =>
    let (lp, l, lc) := pollTask model left
    let (rp, r, rc) := pollTask model right
    match lp, rp with
    | .ready a, .ready b =>
      let value := model.pair a b
      (.ready value, .ready value, lc + rc + 1)
    | _, _ => (.pending, .join l r, lc + rc + 1)

/-- Ready transfers its authority list to the caller exactly once. Pending is
    a wait observation, analogous to a flag stop; it is not a logic error. -/
public inductive Event (Value : Type) where
  | next
  | pending
  | ready (value : Value) (transferred : List Nat)
  | refused

/-- Residual source syntax is allowed ONLY in the direct-style specification.
    Generated state below contains an integer tag instead. -/
public inductive Direct (Value Child : Type) where
  | running (todo : List Command) (frame : Frame Value)
  | waiting (name : String) (rest : List Command)
      (frame : Frame Value) (child : Task Value Child)
  | completed (value : Value)
  | cancelled

/-- One direct-style small step, rather than a second Gabbro interpreter. -/
@[expose] public def directStep (model : Model Value Child) (f : AsyncFn) :
    Direct Value Child → Event Value × Direct Value Child × Nat
  | .running [] frame =>
    let (value, cost) := model.evaluate f.result frame
    (.ready value frame.marks, .completed value, cost + 1)
  | .running (.bind name expr _ :: rest) frame =>
    let (value, cost) := model.evaluate expr frame
    (.next, .running rest (save frame name value), cost + 1)
  | .running (.await name expr _ :: rest) frame =>
    let (child, cost) := makeTask model frame expr
    (.next, .waiting name rest frame child, cost + 1)
  | .waiting name rest frame child =>
    let (result, child', cost) := pollTask model child
    match result with
    | .pending => (.pending, .waiting name rest frame child', cost + 1)
    | .ready value => (.next, .running rest (save frame name value), cost + 1)
  | .completed value => (.refused, .completed value, 0)
  | .cancelled => (.refused, .cancelled, 0)

/-- A finite poll performs internal steps until Ready, Pending or refusal.
    There is no premise asserting that an executor polls again. -/
public inductive DirectPoll (model : Model Value Child) (f : AsyncFn) :
    Direct Value Child → Event Value → Direct Value Child → Nat → Prop where
  | stop (h : directStep model f source = (event, target, cost))
      (terminal : event ≠ .next) : DirectPoll model f source event target cost
  | next (h : directStep model f source = (.next, middle, cost))
      (rest : DirectPoll model f middle event target remaining) :
      DirectPoll model f source event target (cost + remaining)

/-- Cancellation hands all remaining permissions to the generated destructor;
    the destructor must discharge each, not silently forget the receipt. -/
@[expose] public def directCancel : Direct Value Child → List Nat × Direct Value Child
  | .running _ frame | .waiting _ _ frame _ => (frame.marks, .cancelled)
  | .completed _ | .cancelled => ([], .cancelled)

public theorem direct_poll_after_ready (model : Model Value Child) (f : AsyncFn) (v : Value) :
    directStep model f (.completed v) = (.refused, .completed v, 0) := rfl

public theorem ready_child_cached (model : Model Value Child) (v : Value) :
    pollTask model (.ready v) = (.ready v, .ready v, 0) := rfl

public theorem direct_cancel_twice (s : Direct Value Child) :
    (directCancel (directCancel s).2).1 = [] := by
  cases s <;> rfl

end Gabbro.Grammatik.Async
