module

public import Grammatik.Nebenlaeufigkeit.Async.Segment.Values

namespace Gabbro.Grammatik.Async.Representation
open Segment

variable {D : Deklaration} {types : TypeResolution}

/-- Dead locals have the absent tag. A live local must exist and materialise
    at its declaration's exact ordinary type; failure is explicit. -/
@[expose] public def encodeSlots (D : Deklaration) (types : TypeResolution)
    (live : List String) (frame : Frame (Value D)) :
    (fields : List (String × Parser.STyp)) →
      Option (ProdVal D.Fn D.passt
        (fields.map fun field => Ty.sum [none, some (types.ordinary field.2)]))
  | [] => some ()
  | (name, sourceType) :: fields => do
      let slot ← if name ∈ live then do
          let value ← frame.values.lookup name
          let value ← valueAt D (types.ordinary sourceType) value
          pure (presentValue D (types.ordinary sourceType) value)
        else some (absentValue D (types.ordinary sourceType))
      let rest ← encodeSlots D types live frame fields
      pure (slot, rest)

/-- Structural frame agreement, independent of the encoder's computation. -/
public inductive SlotsRep (D : Deklaration) (types : TypeResolution)
    (live : List String) (frame : Frame (Value D)) :
    (fields : List (String × Parser.STyp)) →
    ProdVal D.Fn D.passt
      (fields.map fun field => Ty.sum [none, some (types.ordinary field.2)]) → Prop where
  | nil : SlotsRep D types live frame [] ()
  | dead (unused : name ∉ live) (tail : SlotsRep D types live frame fields rest) :
      SlotsRep D types live frame ((name, sourceType) :: fields)
        (absentValue D (types.ordinary sourceType), rest)
  | live (used : name ∈ live) (found : frame.values.lookup name = some value)
      (typed : valueAt D (types.ordinary sourceType) value = some ordinary)
      (tail : SlotsRep D types live frame fields rest) :
      SlotsRep D types live frame ((name, sourceType) :: fields)
        (presentValue D (types.ordinary sourceType) ordinary, rest)

public theorem slotsRep_encoded (types : TypeResolution) (live : List String)
    (frame : Frame (Value D)) (fields : List (String × Parser.STyp))
    (slots : ProdVal D.Fn D.passt
      (fields.map fun field => Ty.sum [none, some (types.ordinary field.2)]))
    (represented : SlotsRep D types live frame fields slots) :
    encodeSlots D types live frame fields = some slots := by
  induction represented <;>
    simp only [encodeSlots, *, ite_true, ite_false, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def] <;> rfl

/-- Only source values live AFTER construction are needed while waiting.
    The awaited destination itself is not initialised until Ready. -/
@[expose] public def liveAt (f : AsyncFn) : Phase → List String
  | Phase.running tag => liveBefore f.result (f.body.drop tag)
  | Phase.waiting tag _ =>
      match f.body.drop tag with
      | Command.await name _ _ :: rest => without name (liveBefore f.result rest)
      | _ => []
  | Phase.cancelled | Phase.completed => []

@[expose] public def encodeFrame (D : Deklaration) (types : TypeResolution)
    (f : AsyncFn) (phase : Phase) (frame : Frame (Value D)) :
    Option (Wert D (frameType types f)) :=
  encodeSlots D types (liveAt f phase) frame (f.params ++ f.fields)

/-- This includes live-name coverage, which a tuple computation alone cannot
    check: a missing declaration is not an uninitialised optional field. -/
public structure FrameRep (D : Deklaration) (types : TypeResolution) (f : AsyncFn)
    (phase : Phase) (frame : Frame (Value D)) (value : Wert D (frameType types f)) : Prop where
  slots : SlotsRep D types (liveAt f phase) frame (f.params ++ f.fields) value
  declared : ∀ name ∈ liveAt f phase, name ∈ fieldNames f
  unique : (fieldNames f).Nodup

public theorem frameRep_encoded (types : TypeResolution) (f : AsyncFn)
    (phase : Phase) (frame : Frame (Value D)) (value : Wert D (frameType types f))
    (represented : FrameRep D types f phase frame value) :
    encodeFrame D types f phase frame = some value :=
  slotsRep_encoded types (liveAt f phase) frame (f.params ++ f.fields) value represented.slots

/-- Authority is the ordinary resource inventory, separate from by-value
    storage. The injective declaration numbering cannot alias two owners. -/
public structure Inventory (D : Deklaration) where
  number : D.Marke → Nat
  injective : ∀ a b, number a = number b → a = b
  owned : Phase → List (D.Marke × Nat)
  unique : ∀ phase, ((owned phase).map Prod.fst).Nodup
  resources : Phase → List (Res D)
  exact : ∀ phase, resources phase = savedResources (owned phase)

@[expose] public def MarksRep (inventory : Inventory D) (phase : Phase)
    (state : State (Value D) (Child D types)) : Prop :=
  state.marks = (inventory.owned phase).map (fun owner => inventory.number owner.1)

public theorem inventory_no_locks (inventory : Inventory D) (phase : Phase) (lock : D.Lock) :
    Res.held lock ∉ inventory.resources phase := by
  rw [inventory.exact phase]
  exact savedResources_no_locks (inventory.owned phase) lock

public theorem inventory_unique (inventory : Inventory D) (phase : Phase) :
    (inventory.resources phase).Nodup := by
  rw [inventory.exact phase]
  exact savedResources_unique (inventory.owned phase) (inventory.unique phase)

end Gabbro.Grammatik.Async.Representation
