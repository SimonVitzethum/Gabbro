module

public import Grammatik.Nebenlaeufigkeit.Async.Segment.Restoration

namespace Gabbro.Grammatik.Async.Segment

/-- The semantic carrier retains each ordinary value's type. A join is a
    structural pair until its declaration-specific nominal product is known.
    Invalid denotes failed resolution, never an accepted source value. -/
public inductive Value (D : Deklaration) where
  | typed (type : Ty) (value : Wert D type)
  | pair (left right : Value D)
  | invalid

/-- Materialise a join at its declared nominal type. Typed ordinary values
    require exact type equality; there is no numerical or capability cast. -/
@[expose] public def valueAt (D : Deklaration) : (type : Ty) → Value D → Option (Wert D type)
  | type, Value.typed actual value =>
      if same : actual = type then some (same ▸ value) else none
  | Ty.prod _ [leftType, rightType], Value.pair left right => do
      let left ← valueAt D leftType left
      let right ← valueAt D rightType right
      pure (left, right, ())
  | _, _ => none

public theorem valueAt_typed (D : Deklaration) (type : Ty) (value : Wert D type) :
    valueAt D type (Value.typed type value) = some value := by
  simp only [valueAt, dif_pos rfl]

/-- A child has its originating declaration and its exact by-value storage.
    Invalid is outside the representation invariant. -/
public inductive Child (D : Deklaration) (types : TypeResolution) where
  | active (name : String) (storage : Wert D (types.childState name))
  | invalid

/-- Decode exactly the declared arguments, including their length. -/
@[expose] public def argumentsEnv (D : Deklaration) : (types : List Ty) →
    List (Value D) → Option (Env D types)
  | [], [] => some Env.nil
  | type :: types, value :: values => do
      let value ← valueAt D type value
      let rest ← argumentsEnv D types values
      pure (Env.cons value rest)
  | _, _ => none

/-- Resolution names become ordinary de Bruijn variables. Lookup uses the
    latest semantic binding, matching save; every requested local must be
    initialised and have its exact declared type. -/
@[expose] public def localsEnv (D : Deklaration) : (locals : List (String × Ty)) →
    Frame (Value D) → Option (Env D (locals.map Prod.snd))
  | [], _ => some Env.nil
  | (name, type) :: locals, frame => do
      let value ← frame.values.lookup name
      let value ← valueAt D type value
      let rest ← localsEnv D locals frame
      pure (Env.cons value rest)

public theorem argumentsEnv_bool_zeuge (D : Deklaration) :
    argumentsEnv D [Ty.bool] [Value.typed Ty.bool true] =
      some (Env.cons (τ := Ty.bool) true Env.nil) := rfl

@[expose] public def boolFrame (D : Deklaration) : Frame (Value D) :=
  ⟨[("saved", Value.typed Ty.bool true)], [7]⟩

public theorem localsEnv_bool_zeuge (D : Deklaration) :
    localsEnv D [("saved", Ty.bool)] (boolFrame D) =
      some (Env.cons (τ := Ty.bool) true Env.nil) := rfl

end Gabbro.Grammatik.Async.Segment
