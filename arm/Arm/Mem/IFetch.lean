/-
  File:      Arm/Mem/IFetch.lean
  Subject:   Minimal instruction-fetch ordering for self-modifying and freshly
             loaded code: fetch events, DC CVAU / DSB / IC IVAU / ISB events,
             and the architectural maintenance recipe as a decidable predicate.
  Model:     the Arm ARM cache-maintenance recipe (write code; DC CVAU;
             DSB; IC IVAU; DSB; ISB) and ISB context synchronisation, from the
             agent's knowledge of the published architecture, NOT a measured
             copy (no Arm ARM text on this machine). Extends the frozen
             `Event.lean` vocabulary WITHOUT editing it: own event wrapper
             over the shared `Rel`.
-/
import Arm.Mem.Event

namespace Arm

/-- One step of the instruction-side story: a code write, one maintenance
    operation, or an instruction fetch. `dsb`/`isb` carry no address. -/
inductive IMntKind where
  | writeCode
  | dcCvau
  | dsb
  | icIvau
  | isb
  | fetch
  deriving DecidableEq, Repr

/-- One instruction-side event. `addr` is the code address (0 for barriers). -/
structure IFEv where
  id   : Nat
  core : CoreId
  kind : IMntKind
  addr : Addr
  deriving DecidableEq, Repr

/-- A candidate instruction-side execution: events plus program order, which
    is `po` per core, TRANSITIVELY closed (same convention as `Exec`). -/
structure IFExec where
  evs : List IFEv
  po  : Rel
  deriving Repr

/-- The kind of the event with `id`, if present. -/
def kindOf (x : IFExec) (i : Nat) : Option IMntKind :=
  (x.evs.find? fun e => e.id == i).map fun e => e.kind

end Arm

/-
CUTS: skeleton; recipe predicate and fixtures follow.
-/
