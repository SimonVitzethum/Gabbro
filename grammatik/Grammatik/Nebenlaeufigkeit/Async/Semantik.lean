module

public import Grammatik.Nebenlaeufigkeit.Async.Syntax

namespace Gabbro.Grammatik.Async
open Parser

public inductive Poll (Value : Type) where
  | ready (value : Value)
  | pending

/-- Ordinary source operations over an explicit world. Although G.eval itself
    returns only a value, G's bind first records reads with World.lese. The
    world result retains that trace and permits ordinary effectful bindings;
    it is not permission to invent writes in an elaboration certificate.
    Child handles carry no authority outside their enclosing Frame.marks. -/
public structure Model (Value Child W : Type) where
  evaluate : SExpr → Frame Value → W → Value × W × Nat
  newChild : String → List Value → W → Child × W × Nat
  pollChild : Child → W → Poll Value × Child × W × Nat
  pair : Value → Value → Value

@[expose] public def save (frame : Frame Value) (name : String) (value : Value) : Frame Value :=
  { frame with values := (name, value) :: frame.values }

@[expose] public def clear (frame : Frame Value) : Frame Value := { values := [], marks := [] }

/-- Arguments execute left to right, passing each successor world onward. -/
@[expose] public def evalArguments (model : Model Value Child W) (frame : Frame Value) :
    List SExpr → W → List Value × W × Nat
  | [], world => ([], world, 0)
  | e :: es, world =>
    let (v, world', c) := model.evaluate e frame world
    let (vs, world'', cs) := evalArguments model frame es world'
    (v :: vs, world'', c + cs)

/-- Construction evaluates arguments but never polls a child. -/
@[expose] public def makeTask (model : Model Value Child W) (frame : Frame Value) :
    FutureExpr → W → Task Value Child × W × Nat
  | .call name args, world =>
    let (values, world', cost) := evalArguments model frame args world
    let (child, world'', childCost) := model.newChild name values world'
    (.leaf child, world'', cost + childCost + 1)
  | .join left right, world =>
    let (l, world', lc) := makeTask model frame left world
    let (r, world'', rc) := makeTask model frame right world'
    (.join l r, world'', lc + rc + 1)

/-- Left precedes right even if it suspends. Ready children are cached and
    have no further world effects; Pending saves the updated child storage. -/
@[expose] public def pollTask (model : Model Value Child W) :
    Task Value Child → W → Poll Value × Task Value Child × W × Nat
  | .ready value, world => (.ready value, .ready value, world, 0)
  | .leaf child, world =>
    let (result, child', world', cost) := model.pollChild child world
    match result with
    | .ready value => (.ready value, .ready value, world', cost)
    | .pending => (.pending, .leaf child', world', cost)
  | .join left right, world =>
    let (lp, l, world', lc) := pollTask model left world
    let (rp, r, world'', rc) := pollTask model right world'
    match lp, rp with
    | .ready a, .ready b =>
      let value := model.pair a b
      (.ready value, .ready value, world'', lc + rc + 1)
    | _, _ => (.pending, .join l r, world'', lc + rc + 1)

public inductive Event (Value : Type) where
  | next
  | pending
  | ready (value : Value) (transferred : List Nat)
  | refused

public inductive Direct (Value Child : Type) where
  | running (todo : List Command) (frame : Frame Value)
  | waiting (name : String) (rest : List Command)
      (frame : Frame Value) (child : Task Value Child)
  | completed (value : Value)
  | cancelled

/-- One direct-style specification step, including its world transition. -/
@[expose] public def directStep (model : Model Value Child W) (f : AsyncFn) :
    Direct Value Child → W → Event Value × Direct Value Child × W × Nat
  | .running [] frame, world =>
    let (value, world', cost) := model.evaluate f.result frame world
    (.ready value frame.marks, .completed value, world', cost + 1)
  | .running (.bind name expr _ :: rest) frame, world =>
    let (value, world', cost) := model.evaluate expr frame world
    (.next, .running rest (save frame name value), world', cost + 1)
  | .running (.await name expr _ :: rest) frame, world =>
    let (child, world', cost) := makeTask model frame expr world
    (.next, .waiting name rest frame child, world', cost + 1)
  | .waiting name rest frame child, world =>
    let (result, child', world', cost) := pollTask model child world
    match result with
    | .pending => (.pending, .waiting name rest frame child', world', cost + 1)
    | .ready value => (.next, .running rest (save frame name value), world', cost + 1)
  | .completed value, world => (.refused, .completed value, world, 0)
  | .cancelled, world => (.refused, .cancelled, world, 0)

public inductive DirectPoll (model : Model Value Child W) (f : AsyncFn) :
    Direct Value Child → W → Event Value → Direct Value Child → W → Nat → Prop where
  | stop (h : directStep model f source before = (event, target, after, cost))
      (terminal : event ≠ .next) : DirectPoll model f source before event target after cost
  | next (h : directStep model f source before = (.next, middle, between, cost))
      (rest : DirectPoll model f middle between event target after remaining) :
      DirectPoll model f source before event target after (cost + remaining)

/-- Ownership transfer itself leaves the world unchanged. Effectful cleanup
    is cancelWith, whose destructor explicitly returns the successor world. -/
@[expose] public def directCancel : Direct Value Child → W → List Nat × Direct Value Child × W
  | .running _ frame, world | .waiting _ _ frame _, world => (frame.marks, .cancelled, world)
  | .completed _, world | .cancelled, world => ([], .cancelled, world)

public theorem direct_poll_after_ready (model : Model Value Child W) (f : AsyncFn)
    (v : Value) (world : W) :
    directStep model f (.completed v) world = (.refused, .completed v, world, 0) := rfl

public theorem ready_child_cached (model : Model Value Child W) (v : Value) (world : W) :
    pollTask model (.ready v) world = (.ready v, .ready v, world, 0) := rfl

public theorem direct_cancel_twice (s : Direct Value Child) (world : W) :
    (directCancel (directCancel s world).2.1 (directCancel s world).2.2).1 = [] := by
  cases s <;> rfl

end Gabbro.Grammatik.Async
