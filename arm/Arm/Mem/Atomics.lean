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

/-- Ordering of the load half of an exclusive: LDAXR acquires.
    Sail: `CreateAccDescExLDST` (v8_base.sail:11917): acqsc on loads iff acqrel. -/
def exclReadOrd : ExclKind → AccOrd
  | .ldxr => .plain
  | .ldaxr => .acquire
  | .stxr => .plain
  | .stlxr => .plain

/-- Ordering of the store half of an exclusive: STLXR releases.
    Sail: `CreateAccDescExLDST` (v8_base.sail:11917): relsc on stores iff acqrel. -/
def exclWriteOrd : ExclKind → AccOrd
  | .ldxr => .plain
  | .ldaxr => .plain
  | .stxr => .plain
  | .stlxr => .release

/-- The load access of an exclusive (LDXR/LDAXR). `excl` is true: Sail marks
    `accdesc.exclusive`, which `AccessDescriptor_to_Access_kind`
    (interface.sail:80) maps to `AV_exclusive`. -/
def exclReadAcc (k : ExclKind) (addr : Addr) (size : Nat) : Access :=
  { addr := addr, size := size, ord := exclReadOrd k, excl := true }

/-- The store access of an exclusive (STXR/STLXR). -/
def exclWriteAcc (k : ExclKind) (addr : Addr) (size : Nat) : Access :=
  { addr := addr, size := size, ord := exclWriteOrd k, excl := true }

/-- The read half of an LSE atomic carries acquire iff the A bit is set;
    the write half carries release iff the R bit is set. Sail:
    `CreateAccDescRCW` (v8_base.sail:11993) copies A to acqsc and R to relsc,
    and `AccessDescriptor_to_Access_kind` (interface.sail:85-86) maps either
    to `AS_rel_or_acq`. -/
def atomicReadAcc (ann : AtomicAnn) (addr : Addr) (size : Nat) : Access :=
  { addr := addr, size := size, ord := if ann.acq then .acquire else .plain,
    excl := false }

/-- The write half of an LSE atomic. `excl` stays false: Sail sets `atomicop`,
    not `exclusive`, so the kind is `AV_atomic_rmw` (interface.sail:81). -/
def atomicWriteAcc (ann : AtomicAnn) (addr : Addr) (size : Nat) : Access :=
  { addr := addr, size := size, ord := if ann.rel then .release else .plain,
    excl := false }

/-- Mask a Nat value to `size` bytes, as the register-memory transfer does. -/
def mask (size v : Nat) : Nat := v % 2 ^ (8 * size)

/-- Signed reading of a `size`-byte value, for SMAX/SMIN. -/
def toSigned (size v : Nat) : Int :=
  let m := mask size v
  if m < 2 ^ (8 * size - 1) then Int.ofNat m else Int.ofNat m - Int.ofNat (2 ^ (8 * size))

/-- The new value an LSE atomic writes: old memory value and register operand
    in, new value out. Sail: the `MemAtomicOp_*` match in `MemAtomic`
    (v8_base.sail:28374-28406). CAS is decided by `casCmp` below: on mismatch
    Sail sets `cmpfail` and skips the write (v8_base.sail:28415). -/
def atomicFun (op : AtomicOp) (size old operand : Nat) : Nat :=
  match op with
  | .cas => mask size operand
  | .swp => mask size operand
  | .add => mask size (old + operand)
  | .clr => mask size (Nat.xor old (Nat.land old operand))
  | .eor => mask size (Nat.xor old operand)
  | .set => mask size (Nat.lor old operand)
  | .smax => if toSigned size old >= toSigned size operand then mask size old else mask size operand
  | .smin => if toSigned size old <= toSigned size operand then mask size old else mask size operand
  | .umax => if mask size old >= mask size operand then mask size old else mask size operand
  | .umin => if mask size old <= mask size operand then mask size old else mask size operand

/-- CAS compares the masked expected value against the masked old value.
    Sail: `cmpfail = cmpoperand != oldvalue` (v8_base.sail:28403). -/
def casCmp (size expected old : Nat) : Bool :=
  mask size expected == mask size old

end Arm

/-
CUTS: access constructors and ALU done; monitor machine, aob and witnesses follow.
-/
