module

public import Grammatik.Nebenlaeufigkeit.Async.Regeln
public import Grammatik.Kern.Syntax.Syntax.Teil2
import Lean.Elab.Tactic.Omega

namespace Gabbro.Grammatik.Async

/-- Input of typed reification, after ordinary name/type resolution. A fresh
    injective name supply is required for each originating declaration. The
    front end still owes that resolution; this is not an admission check. -/
public structure TypeResolution where
  recordName : List Nat → Nat
  namesUnique : ∀ a b, recordName a = recordName b → a = b
  ordinary : Parser.STyp → Ty
  childState : String → Ty
  childResult : String → Ty

/-- A local has an explicit uninitialised case. Generating a frame never
    invents an inhabitant of an arbitrary source type. Permissions are NOT
    integers in this record: they remain in the canonical resource index Λ. -/
@[expose] public def frameType (types : TypeResolution) (f : AsyncFn) : Ty :=
  .prod (types.recordName [0])
    ((f.params ++ f.fields).map fun field => .sum [none, some (types.ordinary field.2)])

/-- A join's result has both component types, in source order. Paths identify
    nested joins statically; no recursive or dynamically typed runtime node
    is needed. Different declarations need disjoint name supplies at linking. -/
@[expose] public def taskResultType (types : TypeResolution) (path : List Nat) : FutureExpr → Ty
  | .call name _ => types.childResult name
  | .join left right => .prod (types.recordName (3 :: path))
      [taskResultType types (0 :: path) left, taskResultType types (1 :: path) right]

/-- Each child has an active/ready sum. A partial join stores both updated
    children, including the cached Ready side, by value. Its shape is bounded
    by the source FutureExpr, unlike the unrestricted semantic Task type. -/
@[expose] public def taskStorageType (types : TypeResolution) (path : List Nat) : FutureExpr → Ty
  | .call name _ => .sum [some (types.childState name), some (types.childResult name)]
  | .join left right => .sum [some (.prod (types.recordName (4 :: path))
      [taskStorageType types (0 :: path) left, taskStorageType types (1 :: path) right]),
      some (taskResultType types path (.join left right))]

/-- Names here describe code positions, never saved continuations. -/
public inductive Phase where
  | cancelled
  | completed
  | running (tag : Nat)
  | waiting (tag : Nat) (future : FutureExpr)

@[expose] public def commandPhases (tag : Nat) : List Command → List Phase
  | [] => [.running tag]
  | .bind _ _ _ :: rest => .running tag :: commandPhases (tag + 1) rest
  | .await _ future _ :: rest =>
      .running tag :: .waiting tag future :: commandPhases (tag + 1) rest

@[expose] public def phases (f : AsyncFn) : List Phase :=
  .cancelled :: .completed :: commandPhases 0 f.body

/-- Every case carries a typed product, including the empty Cancelled case.
    A completed state retains the result but no frame or child storage. -/
@[expose] public def phaseType (types : TypeResolution) (f : AsyncFn) : Phase → Ty
  | .cancelled => .prod (types.recordName [6]) []
  | .completed => .prod (types.recordName [5]) [types.ordinary f.resultType]
  | .running _ => frameType types f
  | .waiting tag future => .prod (types.recordName [2, tag])
      [frameType types f, taskStorageType types [tag] future]

@[expose] public def stateCases (types : TypeResolution) (f : AsyncFn) : List (Option Ty) :=
  (phases f).map fun phase => some (phaseType types f phase)

/-- A nominal record around the closed phase sum, built ONLY from existing
    Ty forms. Finite case selection makes out-of-range tags unrepresentable. -/
@[expose] public def stateType (types : TypeResolution) (f : AsyncFn) : Ty :=
  .prod (types.recordName [1]) [.sum (stateCases types f)]

/-- Construct a state using the chosen phase's exact payload schema. This
    single constructor serves running, waiting, completed and cancelled
    transitions without runtime casts or a dynamically typed frame. -/
@[expose] public def stateExpr (types : TypeResolution) (f : AsyncFn)
    {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (phase : Fin (stateCases types f).length)
    (payload : NutzlastExpr D Γ Λ ((stateCases types f).get phase)) :
    Expr D Γ Λ (stateType types f) :=
  .prod (types.recordName [1])
    (.cons (.case (stateCases types f) phase payload) .nil)

@[expose] public def awaitCount : List Command → Nat
  | [] => 0
  | .bind _ _ _ :: rest => awaitCount rest
  | .await _ _ _ :: rest => awaitCount rest + 1

public theorem commandPhases_length (tag : Nat) (body : List Command) :
    (commandPhases tag body).length = body.length + awaitCount body + 1 := by
  induction body generalizing tag with
  | nil => rfl
  | cons command rest ih =>
    cases command <;> simp only [commandPhases, List.length_cons, awaitCount, ih] <;> omega

public theorem stateCases_length (types : TypeResolution) (f : AsyncFn) :
    (stateCases types f).length = f.body.length + awaitCount f.body + 3 := by
  simp only [stateCases, List.length_map, phases, List.length_cons, commandPhases_length]

/-- Cancellation has a real zero-field payload; it cannot retain a child or
    a value that a later destructor would need. Cleanup must precede it. -/
@[expose] public def cancelledIndex (types : TypeResolution) (f : AsyncFn) :
    Fin (stateCases types f).length :=
  ⟨0, (by simp only [stateCases, phases, List.map_cons, List.length_cons]; omega)⟩

@[expose] public def cancelledExpr (types : TypeResolution) (f : AsyncFn)
    {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} : Expr D Γ Λ (stateType types f) :=
  stateExpr types f (cancelledIndex types f) (.val (.prod (types.recordName [6]) .nil))

@[expose] public def cancelledValue (types : TypeResolution) (f : AsyncFn) (D : Deklaration) :
    Wert D (stateType types f) := (⟨cancelledIndex types f, ()⟩, ())

/-- The dispatch discriminant is a record projection, never a stack address. -/
@[expose] public def stateDiscriminant (types : TypeResolution) (f : AsyncFn)
    {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (state : Expr D Γ Λ (stateType types f)) : Expr D Γ Λ (.sum (stateCases types f)) :=
  .prodGet state .head

end Gabbro.Grammatik.Async
