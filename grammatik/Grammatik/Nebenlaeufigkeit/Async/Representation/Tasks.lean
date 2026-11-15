module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.Slots
public import Grammatik.Nebenlaeufigkeit.Async.Segment.Answers

namespace Gabbro.Grammatik.Async.Representation
open Segment

variable {D : Deklaration}

/-- Active and cached-Ready cases follow the canonical taskStorageType.
    A join is bounded by its source tree, including a cached Ready sibling. -/
@[expose] public def encodeTask (D : Deklaration) (types : TypeResolution) :
    (path : List Nat) → (future : FutureExpr) → Task (Value D) (Child D types) →
      Option (Wert D (taskStorageType types path future))
  | _, FutureExpr.call name _, Task.leaf (Child.active actual storage) =>
      if same : actual = name then
        some (readyAnswer D (types.childState name) (types.childResult name) (same ▸ storage))
      else none
  | _, FutureExpr.call name _, Task.ready value => do
      let value ← valueAt D (types.childResult name) value
      pure (pendingAnswer D (types.childState name) (types.childResult name) value)
  | path, FutureExpr.join left right, Task.join l r => do
      let l ← encodeTask D types (0 :: path) left l
      let r ← encodeTask D types (1 :: path) right r
      pure (readyAnswer D
        (Ty.prod (types.recordName (4 :: path))
          [taskStorageType types (0 :: path) left, taskStorageType types (1 :: path) right])
        (taskResultType types path (FutureExpr.join left right)) (l, r, ()))
  | path, FutureExpr.join left right, Task.ready value => do
      let value ← valueAt D (taskResultType types path (FutureExpr.join left right)) value
      pure (pendingAnswer D
        (Ty.prod (types.recordName (4 :: path))
          [taskStorageType types (0 :: path) left, taskStorageType types (1 :: path) right])
        (taskResultType types path (FutureExpr.join left right)) value)
  | _, _, _ => none

public inductive TaskRep (D : Deklaration) (types : TypeResolution) :
    (path : List Nat) → (future : FutureExpr) → Task (Value D) (Child D types) →
      Wert D (taskStorageType types path future) → Prop where
  | callActive (path : List Nat) (name : String) (args : List Parser.SExpr)
      (storage : Wert D (types.childState name)) :
      TaskRep D types path (FutureExpr.call name args) (Task.leaf (Child.active name storage))
        (readyAnswer D (types.childState name) (types.childResult name) storage)
  | callReady (path : List Nat) (name : String) (args : List Parser.SExpr)
      (typed : valueAt D (types.childResult name) value = some result) :
      TaskRep D types path (FutureExpr.call name args) (Task.ready value)
        (pendingAnswer D (types.childState name) (types.childResult name) result)
  | joinActive (leftRep : TaskRep D types (0 :: path) left l leftValue)
      (rightRep : TaskRep D types (1 :: path) right r rightValue) :
      TaskRep D types path (FutureExpr.join left right) (Task.join l r)
        (readyAnswer D
          (Ty.prod (types.recordName (4 :: path))
            [taskStorageType types (0 :: path) left, taskStorageType types (1 :: path) right])
          (taskResultType types path (FutureExpr.join left right)) (leftValue, rightValue, ()))
  | joinReady (typed : valueAt D (taskResultType types path (FutureExpr.join left right)) value =
      some result) :
      TaskRep D types path (FutureExpr.join left right) (Task.ready value)
        (pendingAnswer D
          (Ty.prod (types.recordName (4 :: path))
            [taskStorageType types (0 :: path) left, taskStorageType types (1 :: path) right])
          (taskResultType types path (FutureExpr.join left right)) result)

public theorem taskRep_encoded (types : TypeResolution) (path : List Nat)
    (future : FutureExpr) (task : Task (Value D) (Child D types))
    (value : Wert D (taskStorageType types path future))
    (represented : TaskRep D types path future task value) :
    encodeTask D types path future task = some value := by
  induction represented <;>
    simp only [encodeTask, dif_pos rfl, *, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def] <;> rfl

end Gabbro.Grammatik.Async.Representation
