/-
  File:      Arm/Mem/Atomics.lean
  Subject:   Exclusive monitors, LSE atomics, and the atomicity part of the Arm memory model.
  Sail:      sail-arm/arm-v9.4-a/src/instrs64.sail (exclusive_single:29364, rcw_cas:40042,
             rcws_swp:40802), v8_base.sail (CreateAccDescExLDST:11917, CreateAccDescRCW:11993,
             MemAtomic:28334, SetExclusiveMonitors:29053, ExclusiveMonitorsPass:29075),
             interface.sail:74 (exclusive -> AV_exclusive, atomicop -> AV_atomic_rmw),
             stubs.sail:124 (ClearExclusiveByAddress is a no-op stub: clearing is multicore
             business, added here), impdefs.sail:857-861 (monitors pass, status 0b0).
  Arm ARM:   B2.3 atomic-ordered-before (`aob` below); exclusives-clearing rule (a store by
             another observer to the monitored granule clears the reservation).
-/
import Arm.Mem.Event

namespace Arm

/-- Exclusive instructions: plain or acquire load-exclusive, plain or release store-exclusive.
    Sail: `CreateAccDescExLDST` (v8_base.sail:11917) sets acqsc on loads, relsc on stores. -/
inductive ExclKind where
  | ldxr | ldaxr | stxr | stlxr
  deriving DecidableEq, Repr

/-- Ordering annotation of one LSE atomic: the A and R bits are independent.
    Sail: `CreateAccDescRCW` (v8_base.sail:11993) copies them to acqsc/relsc. -/
structure AtomicAnn where
  acq : Bool
  rel : Bool
  deriving DecidableEq, Repr

/-- The LSE operations. Sail: `MemAtomicOp_*` enum (v8_base.sail:1627),
    executed by `MemAtomic` (v8_base.sail:28334) and `MemAtomicRCW` (v8_base.sail:28581). -/
inductive AtomicOp where
  | cas | swp | add | clr | eor | set | smax | smin | umax | umin
  deriving DecidableEq, Repr

end Arm

/-
CUTS: skeleton only; monitor machine, aob and witnesses follow.
-/
