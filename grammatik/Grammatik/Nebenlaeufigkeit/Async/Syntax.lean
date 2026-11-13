module

public import Grammatik.Parser.Expr.Typ

namespace Gabbro.Grammatik.Async
open Parser

/-! Async is an outer language layer. No constructor is added to G. These
    trees are not accepted by the source parser or the ordinary elaborator yet.
    The first core is finite, straight-line code with nested child joins;
    control flow spanning a suspension requires a subsequent extension. -/

/-- An async call constructs a child without running its body. `join` owns
    both children; its result is a pair in left-to-right source order. -/
public inductive FutureExpr where
  | call (name : String) (arguments : List SExpr)
  | join (left right : FutureExpr)

/-- The suspension interface supplied by liveness and resource analysis.
    Names and marks denote declarations, not machine addresses. -/
public structure Boundary where
  live : List String
  saved : List String
  heldLocks : List String
  owned : List Nat
  moved : List Nat

/-- `.await` exists only in this body grammar. SExpr has no async node.
    A bind is one ordinary expression evaluation; its actual language cost
    must be supplied by the existing expression/call certificate. -/
public inductive Command where
  | bind (name : String) (value : SExpr) (costBound : Nat)
  | await (name : String) (future : FutureExpr) (boundary : Boundary)

/-- Surface `async fn name(params) -> resultType { body; return result; }`.
    The nominal identity is the declaration name, independent of result type.
    `fields` describes owned storage, never a pointer into a caller's stack. -/
public structure AsyncFn where
  name : String
  params : List (String × STyp)
  resultType : STyp
  fields : List (String × STyp)
  body : List Command
  result : SExpr
  returnCostBound : Nat

/-- All permissions live in the owned record. Local values do not grant a
    second permission. The segment's ordinary checker must enforce this. -/
public structure Frame (Value : Type) where
  values : List (String × Value)
  marks : List Nat

/-- Child state is stored by value. Join caches completed children: a Ready
    child is never polled again, even while its sibling remains Pending. -/
public inductive Task (Value Child : Type) where
  | leaf (child : Child)
  | join (left right : Task Value Child)
  | ready (value : Value)

/-- This is the whole runtime payload: a finite tag, saved values and child
    state. There is no source continuation, closure or stack address in it. -/
public inductive State (Value Child : Type) where
  | running (tag : Nat) (frame : Frame Value)
  | waiting (tag : Nat) (frame : Frame Value) (child : Task Value Child)
  | completed (value : Value) (frame : Frame Value)
  | cancelled

/-- `Future<T>` is nominal in its originating declaration. The T parameter
    is represented by Value in this parametric specification; Stage 2 must
    instantiate it with the declaration's typed canonical value domain. -/
public structure Future (declaration : String) (Value Child : Type) where
  state : State Value Child

/-- Constructing an async call only saves its arguments and permissions.
    It neither evaluates an expression nor polls a child. -/
@[expose] public def create (f : AsyncFn) (arguments : Frame Value) : Future f.name Value Child :=
  ⟨.running 0 arguments⟩

public theorem create_is_lazy (f : AsyncFn) (arguments : Frame Value) :
    (create (Child := Child) f arguments).state = .running 0 arguments := rfl

/-- State storage contains exactly this one authority list. -/
@[expose] public def State.marks : State Value Child → List Nat
  | .running _ frame | .waiting _ frame _ | .completed _ frame => frame.marks
  | .cancelled => []

/-- A finite bound for the tag, checked separately from record contents. -/
public def State.tagValid (f : AsyncFn) : State Value Child → Prop
  | .running tag _ => tag ≤ f.body.length
  | .waiting tag _ _ => tag < f.body.length
  | .completed _ _ | .cancelled => True

end Gabbro.Grammatik.Async
