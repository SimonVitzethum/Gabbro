module

public import Grammatik.Nebenlaeufigkeit.Async.Regeln

namespace Gabbro.Grammatik.Async
open Parser

/-! A closed specification fixture, not a source execution path. Join produces
    a genuine product value, rather than combining or discarding its outputs. -/

public inductive FixtureValue where
  | scalar (value : Nat)
  | pair (left right : FixtureValue)

@[expose] public def scalarValue : FixtureValue → Nat
  | FixtureValue.scalar n => n
  | .pair _ _ => 0

@[expose] public def fixtureValue (frame : Frame FixtureValue) (world : Nat) : SExpr → FixtureValue
  | .lit n => FixtureValue.scalar n
  | .variable name => (frame.values.lookup name).getD (FixtureValue.scalar 0)
  | .built _ [] => FixtureValue.scalar world
  | .bin _ a b => FixtureValue.scalar (scalarValue (fixtureValue frame world a) + scalarValue (fixtureValue frame world b))
  | .field value field =>
    match fixtureValue frame world value with
    | .pair left right => if field == "left" then left else right
    | FixtureValue.scalar _ => FixtureValue.scalar 0
  | _ => FixtureValue.scalar 0

/-- A countdown child suspends once when its countdown is one. -/
@[expose] public def fixtureModel : Model FixtureValue (Nat × FixtureValue) Nat where
  evaluate expr frame world := (fixtureValue frame world expr, world, 1)
  newChild name args world :=
    let value := scalarValue (args.getD 0 (FixtureValue.scalar 0))
    let child := if name == "first" then (1, FixtureValue.scalar (value + 1))
      else if name == "fast" then (0, FixtureValue.scalar value)
      else (1, FixtureValue.scalar (value * 2))
    (child, world, 0)
  pollChild child world := match child with
    | (0, value) => (.ready value, (0, value), world + 1, 1)
    | (n + 1, value) => (.pending, (n, value), world + 1, 1)
  pair := FixtureValue.pair

@[expose] public def fixtureBoundary (names : List String) : Boundary :=
  { live := names
    saved := names
    heldLocks := []
    owned := [7]
    moved := [7] }

/-- `live` survives both awaits; `first` also survives the second. The second
    await joins a child ready immediately with one that first suspends. -/
@[expose] public def fixture : AsyncFn where
  name := "two_awaits"
  params := []
  resultType := .atom "u64"
  fields := [("live", .atom "u64"), ("first", .atom "u64"),
    ("joined", .raw "struct { left: u64, right: u64 }")]
  body := [
    .bind "live" (.built "$world" []) 1,
    .await "first" (.call "first" [.variable "live"]) (fixtureBoundary ["live"]),
    .await "joined" (.join (.call "fast" [.variable "live"])
      (.call "slow" [.variable "live"])) (fixtureBoundary ["live", "first"])]
  result := .bin "+"
    (.bin "+" (.bin "+" (.variable "live") (.variable "first"))
      (.bin "+" (.field (.variable "joined") "left") (.field (.variable "joined") "right")))
    (.built "$world" [])
  returnCostBound := 1

@[expose] public def fixtureFrame : Frame FixtureValue := ⟨[], [7]⟩
@[expose] public def liveFrame : Frame FixtureValue := save fixtureFrame "live" (FixtureValue.scalar 10)
@[expose] public def firstFrame : Frame FixtureValue := save liveFrame "first" (FixtureValue.scalar 11)
@[expose] public def joinedFrame : Frame FixtureValue :=
  save firstFrame "joined" (.pair (FixtureValue.scalar 10) (FixtureValue.scalar 20))

@[expose] public def fixtureStart : State FixtureValue (Nat × FixtureValue) := (create fixture fixtureFrame).state

@[expose] public def firstPending : State FixtureValue (Nat × FixtureValue) :=
  .waiting 1 liveFrame (.leaf (0, FixtureValue.scalar 11))

@[expose] public def joinPending : State FixtureValue (Nat × FixtureValue) :=
  .waiting 2 firstFrame (.join (.ready (FixtureValue.scalar 10)) (.leaf (0, FixtureValue.scalar 20)))

@[expose] public def fixtureDone : State FixtureValue (Nat × FixtureValue) :=
  .completed (FixtureValue.scalar 66) (clear joinedFrame)

/-- The first poll really suspends, after the local has been saved. -/
public theorem fixture_poll_one :
    MachinePoll fixtureModel (asyncExpand fixtureModel fixture)
      fixtureStart 10 .pending firstPending 11 7 := by
  apply MachinePoll.next (middle := .running 1 liveFrame) (between := 10) (cost := 2) (remaining := 5) rfl
  apply MachinePoll.next (middle := .waiting 1 liveFrame (.leaf (1, FixtureValue.scalar 11)))
    (between := 10) (cost := 3) (remaining := 2) rfl
  exact .stop rfl (by intro h; cases h)

/-- The second suspension retains the completed left child of the join. -/
public theorem fixture_poll_two :
    MachinePoll fixtureModel (asyncExpand fixtureModel fixture)
      firstPending 11 .pending joinPending 14 12 := by
  apply MachinePoll.next (middle := .running 2 firstFrame) (between := 12) (cost := 2) (remaining := 10) rfl
  apply MachinePoll.next
    (middle := .waiting 2 firstFrame (.join (.leaf (0, FixtureValue.scalar 10)) (.leaf (1, FixtureValue.scalar 20))))
    (between := 12) (cost := 6) (remaining := 4) rfl
  exact .stop rfl (by intro h; cases h)

/-- Both awaits complete; return transfers mark 7 and leaves no authority. -/
public theorem fixture_poll_three :
    MachinePoll fixtureModel (asyncExpand fixtureModel fixture)
      joinPending 14 (.ready (FixtureValue.scalar 66) [7]) fixtureDone 15 5 := by
  apply MachinePoll.next (middle := .running 3 joinedFrame) (between := 15) (cost := 3) (remaining := 2) rfl
  exact .stop rfl (by intro h; cases h)

@[expose] public def fixtureEvents : List (Event FixtureValue × Nat) :=
  [(.pending, 7), (.pending, 12), (.ready (FixtureValue.scalar 66) [7], 5)]

public theorem fixture_trace :
    MachineTrace fixtureModel (asyncExpand fixtureModel fixture)
      fixtureStart 10 fixtureEvents fixtureDone 15 :=
  .cons fixture_poll_one (.cons fixture_poll_two (.cons fixture_poll_three .nil))

/-- The witness uses the same generic theorem as every other finite trace. -/
public theorem fixture_refines :
    DirectTrace fixtureModel fixture (decode fixture fixtureStart) 10
      fixtureEvents (decode fixture fixtureDone) 15 :=
  async_elimination fixtureModel fixture fixture_trace

public theorem fixture_cancel_pending :
    machineCancel firstPending 11 = ([7], .cancelled, 11) := rfl

public theorem fixture_no_double_transfer : machineCancel fixtureDone 15 = ([], .cancelled, 15) := rfl

public theorem fixture_join_cached :
    pollTask fixtureModel (.join (.ready (FixtureValue.scalar 10)) (.leaf (0, FixtureValue.scalar 20))) 14 =
      (.ready (.pair (FixtureValue.scalar 10) (FixtureValue.scalar 20)),
        .ready (.pair (FixtureValue.scalar 10) (FixtureValue.scalar 20)), 15, 2) := rfl

public theorem fixture_checked : AsyncOk fixture := by unfold AsyncOk; decide

@[expose] public def changedBoundaries (change : Boundary → Boundary) : AsyncFn :=
  { fixture with body := fixture.body.map fun
      | .await name expr boundary => .await name expr (change boundary)
      | command => command }

public theorem fixture_refuses_lock :
    asyncCheck (changedBoundaries (fun b => { b with heldLocks := ["L"] })) = false := by
  decide

public theorem fixture_refuses_unsaved_local :
    asyncCheck (changedBoundaries (fun b => { b with saved := [] })) = false := by
  decide

public theorem fixture_refuses_copied_marks :
    asyncCheck (changedBoundaries (fun b => { b with moved := b.owned ++ b.owned })) = false := by
  decide

public theorem fixture_refuses_omitted_marks :
    asyncCheck (changedBoundaries (fun b => { b with moved := [] })) = false := by
  decide

public theorem fixture_refuses_duplicate_ownership :
    asyncCheck (changedBoundaries (fun b => { b with owned := [7, 7], moved := [7, 7] })) = false := by
  decide

public theorem fixture_completed_poll_refused :
    machineStep fixtureModel (asyncExpand fixtureModel fixture) fixtureDone 15 =
      (.refused, fixtureDone, 15, 0) := rfl

public theorem fixture_pending_storage_valid : StorageValid fixture joinPending :=
  storageValid_poll fixtureModel fixture
    (storageValid_poll fixtureModel fixture (storageValid_create fixture fixtureFrame)
      fixture_poll_one) fixture_poll_two

/-- The return observes the world after the last child poll. -/
public theorem world_read_after_child_zeuge :
    fixtureModel.evaluate fixture.result joinedFrame 15 = (FixtureValue.scalar 66, 15, 1) := rfl

public theorem ready_child_cached_zeuge :
    pollTask fixtureModel (.ready (FixtureValue.scalar 10)) 14 =
      (.ready (FixtureValue.scalar 10), .ready (FixtureValue.scalar 10), 14, 0) := rfl

@[expose] public def orderedModel : Model FixtureValue (Nat × FixtureValue) Nat :=
  { fixtureModel with
    pollChild := fun child world => (.ready (FixtureValue.scalar world), child, world + 1, 1) }

public theorem join_world_order_zeuge :
    pollTask orderedModel (.join (.leaf (0, FixtureValue.scalar 99)) (.leaf (0, FixtureValue.scalar 99))) 4 =
      (.ready (.pair (FixtureValue.scalar 4) (FixtureValue.scalar 5)),
        .ready (.pair (FixtureValue.scalar 4) (FixtureValue.scalar 5)), 6, 3) := rfl

/-- A reachable, nonterminal set for the final poll's uniform cost duty. -/
public inductive FixtureCostStates : Direct FixtureValue (Nat × FixtureValue) → Nat → Prop where
  | waiting : FixtureCostStates (decode fixture joinPending) 14
  | returning : FixtureCostStates (.running [] joinedFrame) 15

public theorem fixture_cost_duty_zeuge :
    PollCostDuty fixtureModel fixture FixtureCostStates 3 where
  costBound := (by
    intro source before event target after cost initial step
    cases initial with
    | waiting =>
      change (Event.next, Direct.running [] joinedFrame, 15, 3) = (event, target, after, cost) at step
      cases step
      exact Nat.le_refl 3
    | returning =>
      change (Event.ready (FixtureValue.scalar 66) [7], Direct.completed (FixtureValue.scalar 66), 15, 2) =
        (event, target, after, cost) at step
      cases step
      exact Nat.le_succ 2)
  internalClosed := (by
    intro source before target after cost initial step
    cases initial with
    | waiting =>
      change (Event.next, Direct.running [] joinedFrame, 15, 3) = (Event.next, target, after, cost) at step
      cases step
      exact .returning
    | returning =>
      change (Event.ready (FixtureValue.scalar 66) [7], Direct.completed (FixtureValue.scalar 66), 15, 2) =
        (Event.next, target, after, cost) at step
      cases step)

public theorem poll_cost_bounded_zeuge :
    5 ≤ (segmentWork (decode fixture joinPending) + 1) * 3 :=
  poll_cost_bounded fixtureModel fixture FixtureCostStates 3 fixture_cost_duty_zeuge
    .waiting (poll_refines fixtureModel fixture fixture_poll_three)

public theorem direct_poll_exists_zeuge :
    ∃ event target world cost,
      DirectPoll fixtureModel fixture (decode fixture joinPending) 14 event target world cost :=
  direct_poll_exists fixtureModel fixture (decode fixture joinPending) 14

public theorem async_elimination_zeuge :
    DirectTrace fixtureModel fixture (decode fixture fixtureStart) 10
      fixtureEvents (decode fixture fixtureDone) 15 := fixture_refines

public theorem poll_refines_with_unused_asyncOk_zeuge :
    DirectPoll fixtureModel fixture (decode fixture joinPending) 14
      (.ready (FixtureValue.scalar 66) [7]) (decode fixture fixtureDone) 15 5 :=
  poll_refines_with_unused_asyncOk fixtureModel fixture fixture_checked fixture_poll_three

public theorem cancellation_refines_zeuge :
    directCancel (decode fixture joinPending) 14 =
      ((machineCancel joinPending 14).1, decode fixture (machineCancel joinPending 14).2.1,
        (machineCancel joinPending 14).2.2) :=
  cancellation_refines fixture joinPending 14 fixture_pending_storage_valid

@[expose] public def effectModel : Model FixtureValue (Nat × FixtureValue) Nat :=
  { fixtureModel with
    evaluate := fun _ _ world => (FixtureValue.scalar world, world + 1, 1)
    newChild := fun _ _ world => ((0, FixtureValue.scalar world), world + 1, 1) }

public theorem arguments_world_order_zeuge :
    evalArguments effectModel fixtureFrame [.lit 0, .lit 0] 4 =
      ([FixtureValue.scalar 4, FixtureValue.scalar 5], 6, 2) := rfl

public theorem construction_world_order_zeuge :
    makeTask effectModel fixtureFrame (.join (.call "fast" []) (.call "slow" [])) 4 =
      (.join (.leaf (0, FixtureValue.scalar 4)) (.leaf (0, FixtureValue.scalar 5)), 6, 5) := rfl

public theorem internal_decreases_zeuge :
    segmentWork (.running (Value := FixtureValue) (Child := Nat × FixtureValue) [] joinedFrame) <
      segmentWork (decode fixture joinPending) :=
  internal_decreases fixtureModel fixture
    (show directStep fixtureModel fixture (decode fixture joinPending) 14 =
      (Event.next, .running [] joinedFrame, 15, 3) from rfl)

public theorem step_refines_zeuge :
    directStep fixtureModel fixture (decode fixture joinPending) 14 =
      (Event.next, decode fixture (.running 3 joinedFrame), 15, 3) :=
  step_refines fixtureModel fixture
    (show machineStep fixtureModel (asyncExpand fixtureModel fixture) joinPending 14 =
      (Event.next, .running 3 joinedFrame, 15, 3) from rfl)

public theorem storageValid_step_zeuge :
    StorageValid fixture (.running (Value := FixtureValue) (Child := Nat × FixtureValue) 3 joinedFrame) :=
  storageValid_step fixtureModel fixture fixture_pending_storage_valid
    (show machineStep fixtureModel (asyncExpand fixtureModel fixture) joinPending 14 =
      (Event.next, .running 3 joinedFrame, 15, 3) from rfl)

public theorem storageValid_poll_zeuge : StorageValid fixture fixtureDone :=
  storageValid_poll fixtureModel fixture fixture_pending_storage_valid fixture_poll_three

public theorem directPoll_marks_append_zeuge :
    directMarks (decode fixture fixtureDone) ++ eventMarks (Event.ready (FixtureValue.scalar 66) [7]) =
      directMarks (decode fixture joinPending) :=
  directPoll_marks_append fixtureModel fixture (poll_refines fixtureModel fixture fixture_poll_three)

end Gabbro.Grammatik.Async
