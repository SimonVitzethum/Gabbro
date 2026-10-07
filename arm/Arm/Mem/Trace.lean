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

end Arm

/-
CUTS: skeleton only. `runEff` (Eff tree against read supply), `Trace.ofEff`
and dependency smart constructors are NOT yet defined; `Exec.ofTraces` lives
in `Arm/Mem/Exec.lean` (agent 06 owns both files).
-/
