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
  | .scalar n => n
  | .pair _ _ => 0

@[expose] public def fixtureValue (frame : Frame FixtureValue) : SExpr → FixtureValue
  | .lit n => .scalar n
  | .variable name => (frame.values.lookup name).getD (.scalar 0)
  | .bin _ a b => .scalar (scalarValue (fixtureValue frame a) + scalarValue (fixtureValue frame b))
  | .field value field =>
    match fixtureValue frame value with
    | .pair left right => if field == "left" then left else right
    | .scalar _ => .scalar 0
  | _ => .scalar 0

/-- A countdown child suspends once when its countdown is one. -/
@[expose] public def fixtureModel : Model FixtureValue (Nat × FixtureValue) where
  evaluate expr frame := (fixtureValue frame expr, 1)
  newChild name args :=
    let value := scalarValue (args.getD 0 (.scalar 0))
    if name == "first" then (1, .scalar (value + 1))
    else if name == "fast" then (0, .scalar value)
    else (1, .scalar (value * 2))
  pollChild child := match child with
    | (0, value) => (.ready value, (0, value), 1)
    | (n + 1, value) => (.pending, (n, value), 1)
  pair := FixtureValue.pair

@[expose] public def fixtureBoundary (names : List String) : Boundary :=
  { live := names, saved := names, heldLocks := [], owned := [7], moved := [7] }

/-- `live` survives both awaits; `first` also survives the second. The second
    await joins a child ready immediately with one that first suspends. -/
@[expose] public def fixture : AsyncFn where
  name := "two_awaits"
  params := []
  resultType := .atom "u64"
  fields := [("live", .atom "u64"), ("first", .atom "u64"),
    ("joined", .raw "struct { left: u64, right: u64 }")]
  body := [
    .bind "live" (.lit 10) 1,
    .await "first" (.call "first" [.variable "live"]) (fixtureBoundary ["live"]),
    .await "joined" (.join (.call "fast" [.variable "live"])
      (.call "slow" [.variable "live"])) (fixtureBoundary ["live", "first"])]
  result := .bin "+" (.bin "+" (.variable "live") (.variable "first"))
    (.bin "+" (.field (.variable "joined") "left") (.field (.variable "joined") "right"))
  returnCostBound := 1

@[expose] public def fixtureFrame : Frame FixtureValue := ⟨[], [7]⟩
@[expose] public def liveFrame : Frame FixtureValue := save fixtureFrame "live" (.scalar 10)
@[expose] public def firstFrame : Frame FixtureValue := save liveFrame "first" (.scalar 11)
@[expose] public def joinedFrame : Frame FixtureValue :=
  save firstFrame "joined" (.pair (.scalar 10) (.scalar 20))

@[expose] public def fixtureStart : State FixtureValue (Nat × FixtureValue) := (create fixture fixtureFrame).state

@[expose] public def firstPending : State FixtureValue (Nat × FixtureValue) :=
  .waiting 1 liveFrame (.leaf (0, .scalar 11))

@[expose] public def joinPending : State FixtureValue (Nat × FixtureValue) :=
  .waiting 2 firstFrame (.join (.ready (.scalar 10)) (.leaf (0, .scalar 20)))

@[expose] public def fixtureDone : State FixtureValue (Nat × FixtureValue) :=
  .completed (.scalar 51) (clear joinedFrame)

/-- The first poll really suspends, after the local has been saved. -/
public theorem fixture_poll_one :
    MachinePoll fixtureModel (asyncExpand fixtureModel fixture)
      fixtureStart .pending firstPending 7 := by
  apply MachinePoll.next (middle := .running 1 liveFrame) (cost := 2) (remaining := 5) rfl
  apply MachinePoll.next (middle := .waiting 1 liveFrame (.leaf (1, .scalar 11)))
    (cost := 3) (remaining := 2) rfl
  exact .stop rfl (by intro h; cases h)

/-- The second suspension retains the completed left child of the join. -/
public theorem fixture_poll_two :
    MachinePoll fixtureModel (asyncExpand fixtureModel fixture)
      firstPending .pending joinPending 12 := by
  apply MachinePoll.next (middle := .running 2 firstFrame) (cost := 2) (remaining := 10) rfl
  apply MachinePoll.next
    (middle := .waiting 2 firstFrame (.join (.leaf (0, .scalar 10)) (.leaf (1, .scalar 20))))
    (cost := 6) (remaining := 4) rfl
  exact .stop rfl (by intro h; cases h)

/-- Both awaits complete; return transfers mark 7 and leaves no authority. -/
public theorem fixture_poll_three :
    MachinePoll fixtureModel (asyncExpand fixtureModel fixture)
      joinPending (.ready (.scalar 51) [7]) fixtureDone 5 := by
  apply MachinePoll.next (middle := .running 3 joinedFrame) (cost := 3) (remaining := 2) rfl
  exact .stop rfl (by intro h; cases h)

@[expose] public def fixtureEvents : List (Event FixtureValue × Nat) :=
  [(.pending, 7), (.pending, 12), (.ready (.scalar 51) [7], 5)]

public theorem fixture_trace :
    MachineTrace fixtureModel (asyncExpand fixtureModel fixture)
      fixtureStart fixtureEvents fixtureDone :=
  .cons fixture_poll_one (.cons fixture_poll_two (.cons fixture_poll_three .nil))

/-- The witness uses the same generic theorem as every other finite trace. -/
public theorem fixture_refines :
    DirectTrace fixtureModel fixture (decode fixture fixtureStart)
      fixtureEvents (decode fixture fixtureDone) :=
  async_elimination fixtureModel fixture fixture_trace

public theorem fixture_cancel_pending :
    machineCancel firstPending = ([7], .cancelled) := rfl

public theorem fixture_no_double_transfer : machineCancel fixtureDone = ([], .cancelled) := rfl

public theorem fixture_join_cached :
    pollTask fixtureModel (.join (.ready (.scalar 10)) (.leaf (0, .scalar 20))) =
      (.ready (.pair (.scalar 10) (.scalar 20)),
        .ready (.pair (.scalar 10) (.scalar 20)), 2) := rfl

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
    machineStep fixtureModel (asyncExpand fixtureModel fixture) fixtureDone =
      (.refused, fixtureDone, 0) := rfl

public theorem fixture_pending_storage_valid : StorageValid fixture joinPending :=
  storageValid_poll fixtureModel fixture
    (storageValid_poll fixtureModel fixture (storageValid_create fixture fixtureFrame)
      fixture_poll_one) fixture_poll_two

end Gabbro.Grammatik.Async
