module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.Fixture

namespace Gabbro.Grammatik.Async.Representation.Fixture
open Segment

public theorem liveAt_waiting_zeuge :
    liveAt fixture (Phase.waiting 2 future) = ["live", "first"] := rfl

public theorem taskRep_partial_join_zeuge :
    TaskRep declaration types [2] future partialJoin taskValue :=
  TaskRep.joinActive
    (TaskRep.callReady [0, 2] "fast" [Parser.SExpr.variable "live"]
      (valueAt_typed declaration scalarType ten))
    (TaskRep.callActive [1, 2] "slow" [Parser.SExpr.variable "live"] (zero, twenty, ()))

public theorem encodeTask_partial_join_zeuge :
    encodeTask declaration types [2] future partialJoin = some taskValue :=
  taskRep_encoded types [2] future partialJoin taskValue taskRep_partial_join_zeuge

public theorem frameRep_waiting_zeuge :
    FrameRep declaration types fixture (Phase.waiting 2 future) frame frameValue where
  slots := by
    change SlotsRep declaration types ["live", "first"] frame
      (fixture.params ++ fixture.fields) frameValue
    refine SlotsRep.live ?_ rfl (valueAt_typed declaration scalarType ten) ?_
    · simp only [List.mem_cons, String.reduceEq, List.not_mem_nil, or_false, true_or]
    refine SlotsRep.live ?_ rfl (valueAt_typed declaration scalarType eleven) ?_
    · simp only [List.mem_cons, String.reduceEq, List.not_mem_nil, or_false, false_or]
    refine SlotsRep.dead ?_ SlotsRep.nil
    simp only [List.mem_cons, String.reduceEq, List.not_mem_nil, or_false, not_false_eq_true]
  declared := by
    intro name member
    rw [liveAt_waiting_zeuge] at member
    change name ∈ ["live", "first", "joined"]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same
    · cases same
      exact List.mem_cons_self
    · cases same
      exact List.mem_cons_of_mem "live" List.mem_cons_self
  unique := (asyncCheck_sound fixture fixture_checked).1

public theorem encodeFrame_waiting_zeuge :
    encodeFrame declaration types fixture (Phase.waiting 2 future) frame = some frameValue :=
  frameRep_encoded types fixture (Phase.waiting 2 future) frame frameValue frameRep_waiting_zeuge

public theorem phaseRep_waiting_zeuge :
    PhaseRep declaration types fixture (Phase.waiting 2 future) waiting
      (frameValue, taskValue, ()) :=
  PhaseRep.waiting 2 future frame partialJoin frameValue taskValue
    frameRep_waiting_zeuge taskRep_partial_join_zeuge

public theorem marksRep_waiting_zeuge : MarksRep inventory (Phase.waiting 2 future) waiting := rfl

@[expose] public def waitingPrefix : List Phase := [Phase.cancelled, Phase.completed,
  Phase.running 0, Phase.running 1,
  Phase.waiting 1 (FutureExpr.call "first" [Parser.SExpr.variable "live"]), Phase.running 2]

@[expose] public def waitingSuffix : List Phase := [Phase.waiting 2 future, Phase.running 3]

@[expose] public def waitingValue : Wert declaration (stateType types fixture) :=
  (prefixValue declaration types fixture waitingSuffix
    (firstPhaseValue declaration types fixture (Phase.waiting 2 future) [Phase.running 3]
      (frameValue, taskValue, ())) waitingPrefix, ())

public theorem inv_waiting_zeuge : Inv fixture types inventory waiting waitingValue := by
  have suffix : PhaseListRep declaration types fixture inventory waitingSuffix waiting
      (firstPhaseValue declaration types fixture (Phase.waiting 2 future) [Phase.running 3]
        (frameValue, taskValue, ())) :=
    PhaseListRep.first (Phase.waiting 2 future) [Phase.running 3] waiting
      (frameValue, taskValue, ()) phaseRep_waiting_zeuge marksRep_waiting_zeuge
  apply phaseListRep_prefix types fixture inventory waiting waitingSuffix _ suffix waitingPrefix
  intro phase member
  simp only [waitingPrefix, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same | same <;> cases same <;> rfl

public theorem inv_encoded_zeuge : encode declaration types fixture waiting = some waitingValue :=
  inv_encoded fixture types inventory waiting waitingValue inv_waiting_zeuge

public theorem cancelled_inv_zeuge :
    Inv fixture types inventory State.cancelled (cancelledValue types fixture declaration) :=
  cancelled_inv types fixture inventory rfl

public theorem cancelled_encoded_zeuge :
    encode declaration types fixture State.cancelled = some (cancelledValue types fixture declaration) := rfl

public theorem inventory_no_locks_zeuge :
    Res.held () ∉ inventory.resources (Phase.waiting 2 future) :=
  inventory_no_locks inventory (Phase.waiting 2 future) ()

public theorem inventory_unique_zeuge : (inventory.resources (Phase.waiting 2 future)).Nodup :=
  inventory_unique inventory (Phase.waiting 2 future)

public theorem frameRep_start_zeuge :
    FrameRep declaration types fixture (Phase.running 0) startFrame startFrameValue where
  slots := by
    change SlotsRep declaration types [] startFrame (fixture.params ++ fixture.fields) startFrameValue
    exact SlotsRep.dead (by intro member; cases member)
      (SlotsRep.dead (by intro member; cases member)
        (SlotsRep.dead (by intro member; cases member) SlotsRep.nil))
  declared := by
    change ∀ name ∈ ([] : List String), name ∈ fieldNames fixture
    intro name member
    cases member
  unique := (asyncCheck_sound fixture fixture_checked).1

public theorem initialFrame_zeuge : InitialFrame declaration types fixture inventory startFrame where
  parameters := by
    intro name sourceType member
    change (name, sourceType) ∈ ([] : List (String × Parser.STyp)) at member
    cases member
  live := ⟨startFrameValue, frameRep_start_zeuge⟩
  marks := rfl

public theorem inv_start_zeuge :
    Inv fixture types inventory
      (State.running 0 startFrame) startValue := by
  have suffix : PhaseListRep declaration types fixture inventory (commandPhases 0 fixture.body)
      (State.running 0 startFrame)
      (firstPhaseValue declaration types fixture (Phase.running 0)
        (commandPhases 1 fixture.body.tail) startFrameValue) :=
    PhaseListRep.first (Phase.running 0) (commandPhases 1 fixture.body.tail)
      (State.running 0 startFrame) startFrameValue
      (PhaseRep.running 0 startFrame startFrameValue frameRep_start_zeuge) rfl
  apply phaseListRep_prefix types fixture inventory (State.running 0 startFrame)
    (commandPhases 0 fixture.body) _ suffix [Phase.cancelled, Phase.completed]
  intro phase member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same <;> cases same <;> rfl

public theorem encode_start_zeuge :
    encode declaration types fixture (State.running 0 startFrame) = some startValue :=
  inv_encoded fixture types inventory (State.running 0 startFrame) startValue inv_start_zeuge

public theorem reachable_create_zeuge
    (model : Model (Value declaration) (Child declaration types) (World declaration)) :
    Reachable model fixture inventory (Gabbro.Grammatik.Async.create fixture startFrame).state world :=
  Reachable.create startFrame world initialFrame_zeuge

public theorem reachable_running_bound_zeuge
    (model : Model (Value declaration) (Child declaration types) (World declaration)) :
    0 ≤ fixture.body.length :=
  reachable_running_bound model fixture inventory 0 startFrame world (reachable_create_zeuge model)

end Gabbro.Grammatik.Async.Representation.Fixture
