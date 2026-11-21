module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.State
import Lean.Elab.Tactic.Omega

namespace Gabbro.Grammatik.Async.Representation
open Segment

variable {D : Deklaration} {types : TypeResolution}

/-- Creation receives correctly typed, initialised arguments and exactly
    its declared authority. Liveness must also be covered by real slots. -/
public structure InitialFrame (D : Deklaration) (types : TypeResolution) (f : AsyncFn)
    (inventory : Inventory D) (frame : Frame (Value D)) : Prop where
  parameters : ∀ name sourceType, (name, sourceType) ∈ f.params →
    ∃ value ordinary, frame.values.lookup name = some value ∧
      valueAt D (types.ordinary sourceType) value = some ordinary
  live : ∃ value, FrameRep D types f (Phase.running 0) frame value
  marks : MarksRep inventory (Phase.running 0)
    (State.running (Child := Child D types) 0 frame)

/-- Creation is already represented by the generated record type. The
    running arm has exactly the initial slots and owned inventory. -/
public theorem initial_inv (f : AsyncFn) (inventory : Inventory D) (frame : Frame (Value D))
    (initial : InitialFrame D types f inventory frame) :
    ∃ value, Inv f types inventory
      (Gabbro.Grammatik.Async.create (Child := Child D types) f frame).state value := by
  obtain ⟨payload, slots⟩ := initial.live
  have runningFirst : ∃ rest, commandPhases 0 f.body = .running 0 :: rest := by
    cases body : f.body with
    | nil => exact ⟨[], rfl⟩
    | cons first rest => cases first <;> exact ⟨_, rfl⟩
  obtain ⟨rest, first⟩ := runningFirst
  have represented : ∃ value,
      PhaseListRep D types f inventory (phases f) (.running 0 frame) value := by
    unfold phases
    rw [first]
    exact ⟨_, .later _ _ _ _ rfl (.later _ _ _ _ rfl
      (.first _ _ _ _ (.running 0 frame payload slots) initial.marks))⟩
  obtain ⟨value, represented⟩ := represented
  exact ⟨(value, ()), represented⟩

/-- Actual semantic reachability from a typed creation. The step constructor
    does NOT assume target typing or Inv: those are preservation obligations,
    not conditions that may remove inconvenient executions from reachability. -/
public inductive Reachable (model : Model (Value D) (Child D types) (World D))
    (f : AsyncFn) (inventory : Inventory D) :
    State (Value D) (Child D types) → World D → Prop where
  | create (frame : Frame (Value D)) (world : World D)
      (initial : InitialFrame D types f inventory frame) :
      Reachable model f inventory (Gabbro.Grammatik.Async.create f frame).state world
  | step (reachable : Reachable model f inventory source before)
      (transition : machineStep model (asyncExpand model f) source before =
        (event, target, after, cost)) : Reachable model f inventory target after

public theorem reachable_storageValid (model : Model (Value D) (Child D types) (World D))
    (f : AsyncFn) (inventory : Inventory D)
    (source : State (Value D) (Child D types)) (world : World D)
    (reachable : Reachable model f inventory source world) : StorageValid f source := by
  induction reachable with
  | create frame _ _ => exact storageValid_create f frame
  | step _ transition ih => exact storageValid_step model f ih transition

/-- Once the poll builders preserve the concrete representation, encoding
    is total on actual semantic reachability. Creation needs no step premise. -/
public theorem reachable_encoded (model : Model (Value D) (Child D types) (World D))
    (f : AsyncFn) (inventory : Inventory D)
    (preserved : ∀ {source target before after event cost} {value},
      Inv f types inventory source value →
      machineStep model (asyncExpand model f) source before = (event, target, after, cost) →
      ∃ next, Inv f types inventory target next)
    {source : State (Value D) (Child D types)} {world : World D}
    (reachable : Reachable model f inventory source world) :
    ∃ value, Inv f types inventory source value ∧ encode D types f source = some value := by
  have representation : ∃ value, Inv f types inventory source value := by
    induction reachable with
    | create frame _ initial => exact initial_inv f inventory frame initial
    | step _ transition ih =>
      obtain ⟨value, previous⟩ := ih
      exact preserved previous transition
  obtain ⟨value, represented⟩ := representation
  exact ⟨value, represented, inv_encoded f types inventory source value represented⟩

/-- An out-of-range running phase cannot occur, independently of the still
    separate frame/child typing preservation proof. -/
public theorem reachable_running_bound (model : Model (Value D) (Child D types) (World D))
    (f : AsyncFn) (inventory : Inventory D) (tag : Nat) (frame : Frame (Value D))
    (world : World D) (reachable : Reachable model f inventory (State.running tag frame) world) :
    tag ≤ f.body.length :=
  reachable_storageValid model f inventory (State.running tag frame) world reachable

/-- A reachable wait refers to a real await, not merely an in-range bind. -/
public theorem reachable_waiting_command (model : Model (Value D) (Child D types) (World D))
    (f : AsyncFn) (inventory : Inventory D) (tag : Nat) (frame : Frame (Value D))
    (task : Task (Value D) (Child D types)) (world : World D)
    (reachable : Reachable model f inventory (State.waiting tag frame task) world) :
    ∃ name future boundary rest, f.body.drop tag = Command.await name future boundary :: rest :=
  reachable_storageValid model f inventory (State.waiting tag frame task) world reachable

public theorem reachable_waiting_bound (model : Model (Value D) (Child D types) (World D))
    (f : AsyncFn) (inventory : Inventory D) (tag : Nat) (frame : Frame (Value D))
    (task : Task (Value D) (Child D types)) (world : World D)
    (reachable : Reachable model f inventory (State.waiting tag frame task) world) :
    tag < f.body.length := by
  obtain ⟨name, future, boundary, rest, command⟩ :=
    reachable_waiting_command model f inventory tag frame task world reachable
  have size := congrArg List.length command
  simp only [List.length_drop, List.length_cons] at size
  omega

end Gabbro.Grammatik.Async.Representation
