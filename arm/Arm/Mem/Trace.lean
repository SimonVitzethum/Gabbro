/-
  File:      Arm/Mem/Trace.lean
  Subject:   One core's run as an event list with dependency edges, built by
             running a sequential `Eff` tree against supplied read values.
  Sail:      the memory effects this replays are `__ReadMem` (effect {rmem})
             and `__WriteMem` (effect {wmv}) of
             sail-arm/arm-v9.4-a/src/mem.sail lines 44-57; the events they
             become are the concurrency interface of
             sail/lib/concurrency_interface/read_write.sail; barriers follow
             the `Barrier` union of
             sail-arm/arm-v9.4-a/src/interface.sail lines 166-189.
-/
import Arm.Mem.Event
import Arm.Isa.Monad

namespace Arm

/-- One core's sequential run: its events in program order plus the
    dependency edges its instructions reported (read to later event). -/
structure Trace where
  core : CoreId
  evs  : List Ev
  addr : Rel
  data : Rel
  ctrl : Rel
  deriving Repr

/-- Program order inside one trace: every earlier event before every later one. -/
def Trace.po (t : Trace) : Rel :=
  let ids := t.evs.map (·.id)
  (List.range ids.length).flatMap fun i =>
    (List.range ids.length).filterMap fun j =>
      if i < j then some (ids[i]!, ids[j]!) else none

/-- Run one sequential `Eff` tree on `core`, replaying its Sail memory
    effects as events: `rdMem` becomes a read of the supplied value
    (`sup` answers the n-th read), `wrMem` a write, `bar` a barrier.
    Register/system reads answer zero (no event); `raise` ends the run.
    Fuel bounds the run; `next` is the first fresh event id, `nr` counts
    consumed reads. -/
def runEff : Nat → Eff Unit → CoreId → Nat → Nat → (Nat → Nat) → Option (List Ev × Nat × Nat)
  | 0, _, _, _, _, _ => none
  | f + 1, e, core, next, nr, sup =>
    match e with
    | .ret _ => some ([], next, nr)
    | .rdX _ k => runEff f (k 0) core next nr sup
    | .wrX _ _ k => runEff f k core next nr sup
    | .rdV _ k => runEff f (k 0) core next nr sup
    | .wrV _ _ k => runEff f k core next nr sup
    | .rdPC k => runEff f (k 0) core next nr sup
    | .wrPC _ k => runEff f k core next nr sup
    | .rdNZCV k => runEff f (k 0) core next nr sup
    | .wrNZCV _ k => runEff f k core next nr sup
    | .rdSys _ k => runEff f (k 0) core next nr sup
    | .wrSys _ _ k => runEff f k core next nr sup
    | .rdMem a k =>
      let v := sup nr
      match runEff f (k v) core (next + 1) (nr + 1) sup with
      | none => none
      | some (evs, nx, nrr) =>
        some ({ id := next, core, kind := .read a, val := v } :: evs, nx, nrr)
    | .wrMem a v k =>
      match runEff f k core (next + 1) nr sup with
      | none => none
      | some (evs, nx, nrr) =>
        some ({ id := next, core, kind := .write a, val := v } :: evs, nx, nrr)
    | .bar b k =>
      match runEff f k core (next + 1) nr sup with
      | none => none
      | some (evs, nx, nrr) =>
        some ({ id := next, core, kind := .barrier b, val := 0 } :: evs, nx, nrr)
    | .raise _ => some ([], next, nr)

/-- Build one core's run from an `Eff` tree: `fuel` bounds the run, `next`
    is the first fresh event id, `sup` answers the n-th read.
    Dependency edges start empty; attach them with `Trace.withDeps`. -/
def Trace.ofEff (p : Eff Unit) (core next : Nat) (sup : Nat → Nat) (fuel : Nat) : Option Trace :=
  match runEff fuel p core next 0 sup with
  | none => none
  | some (evs, _, _) => some { core, evs, addr := [], data := [], ctrl := [] }

/-- Attach caller-reported dependency edges to a run. The edges are checked
    by `Exec.wf`, not here: each must start at a read and end po-later. -/
def Trace.withDeps (t : Trace) (a d c : Rel) : Trace :=
  { t with addr := a, data := d, ctrl := c }

end Arm

/-
CUTS: `runEff` replays memory effects as events; register/system reads answer
zero without an event (their values are core-local, invisible to the memory
model). Intra-instruction dependency synthesis (which read feeds which later
access) is NOT done here: `ofEff` leaves edges empty and `withDeps` attaches
caller-reported ones. `Exec.ofTraces` lives in `Arm/Mem/Exec.lean`.
-/
