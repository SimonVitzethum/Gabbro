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

/-- Byte ranges `[s1, s1+n1)` and `[s2, s2+n2)` overlap. A store to an
    overlapping range clears another observer's reservation: Sail clears by
    address on every shareable store (`AArch64_MemSingle_set__1`,
    v8_base.sail:28087, via `ClearExclusiveByAddress`). -/
def overlap (a1 : Addr) (n1 : Nat) (a2 : Addr) (n2 : Nat) : Bool :=
  let s1 := a1.toNat
  let s2 := a2.toNat
  s1 < s2 + n2 && s2 < s1 + n1

/-- The exclusive-monitor state: each core holds at most one reservation
    `(address, size)`; shareable reservations are also recorded globally.
    Sail: `AArch64_SetExclusiveMonitors` (v8_base.sail:29053) marks local and,
    unless non-shareable, global; the `Mark*` bodies are no-op stubs
    (stubs.sail:273-277), so the multicore behaviour is defined here. -/
structure ExclState where
  perCore : List (CoreId × Addr × Nat)
  shared : List (CoreId × Addr × Nat)
  deriving Repr

/-- The empty monitor state: no reservation anywhere. -/
def exclInit : ExclState := { perCore := [], shared := [] }

/-- Look up one core's reservation. -/
def monGet (m : List (CoreId × Addr × Nat)) (c : CoreId) : Option (Addr × Nat) :=
  match m.find? fun p => p.1 == c with
  | none => none
  | some (_, a, n) => some (a, n)

/-- Replace one core's reservation (used with `none` to clear it). -/
def monSet (m : List (CoreId × Addr × Nat)) (c : CoreId)
    (r : Option (Addr × Nat)) : List (CoreId × Addr × Nat) :=
  let rest := m.filter fun p => p.1 != c
  match r with
  | none => rest
  | some (a, n) => (c, a, n) :: rest

/-- LDXR/LDAXR: set this core's local monitor, and the global one for
    shareable memory. Sail: `AArch64_SetExclusiveMonitors` (v8_base.sail:29053). -/
def ldxStep (s : ExclState) (c : CoreId) (a : Addr) (n : Nat)
    (shareable : Bool) : ExclState :=
  { perCore := monSet s.perCore c (some (a, n)),
    shared := if shareable then monSet s.shared c (some (a, n)) else s.shared }

/-- A store by core `c` clears every OTHER core's reservation whose range
    overlaps the stored range. The storing core's own monitor is untouched:
    Sail's store path calls `ClearExclusiveByAddress` (others) but not
    `ClearExclusiveLocal` (v8_base.sail:28087). -/
def storeStep (s : ExclState) (c : CoreId) (a : Addr) (n : Nat) : ExclState :=
  { perCore := s.perCore.filter fun p => p.1 == c || !overlap p.2.1 p.2.2 a n,
    shared := s.shared.filter fun p => p.1 == c || !overlap p.2.1 p.2.2 a n }

/-- STXR/STLXR pass check: the local monitor must still hold this address,
    and for shareable memory the global monitor too. Sail:
    `AArch64_ExclusiveMonitorsPass` (v8_base.sail:29075). -/
def stxPass (s : ExclState) (c : CoreId) (a : Addr) (n : Nat)
    (shareable : Bool) : Bool :=
  match monGet s.perCore c with
  | none => false
  | some (a0, n0) =>
    overlap a0 n0 a n &&
      (!shareable ||
        match monGet s.shared c with
        | none => false
        | some (g0, m0) => overlap g0 m0 a n)

/-- The allowed status results of STXR/STLXR: `0` success, `1` failure.
    Failure is ALWAYS allowed: a store-exclusive MAY fail spuriously, so the
    FREE behaviour is modelled by offering both outcomes whenever the monitor
    is set. Success writes `ExclusiveMonitorsStatus()`, which is `0b0`
    (impdefs.sail:861); Sail defaults the status to `0b1`
    (instrs64.sail:29364). -/
def stxOutcomes (s : ExclState) (c : CoreId) (a : Addr) (n : Nat)
    (shareable : Bool) : List Nat :=
  if stxPass s c a n shareable then [0, 1] else [1]

/-- STXR/STLXR clears this core's local monitor whether it passes or not.
    Sail: `ClearExclusiveLocal(ProcessorID())` runs unconditionally
    (v8_base.sail:29091). -/
def stxStep (s : ExclState) (c : CoreId) : ExclState :=
  { perCore := monSet s.perCore c none, shared := s.shared }

/-- A read event carrying acquire ordering (LDAXR, an LSE atomic with the A
    bit). `Access.ord` is the frozen vocabulary; acquire maps from Sail's
    `acqsc` via `AccessDescriptor_to_Access_kind` (interface.sail:85-86). -/
def isAcqRead (e : Ev) : Bool :=
  match e.kind with
  | .read a => decide (a.ord = .acquire)
  | _ => false

/-- The core of event `i`, if present. -/
def coreOf? (x : Exec) (i : Nat) : Option CoreId :=
  match x.ev? i with
  | none => none
  | some e => some e.core

/-- Two event ids are on the same core; a missing event counts as same-core so
    that malformed executions never produce a spurious external edge. -/
def sameCore (x : Exec) (i j : Nat) : Bool :=
  match x.ev? i, x.ev? j with
  | some e, some f => e.core == f.core
  | _, _ => true

/-- Reads-from inverted then coherence: `(r, w')` with `r` reading from a write
    coherence-before `w'`. Built from the frozen `Rel.comp`. -/
def frOf (x : Exec) : Rel := x.rf.inv.comp x.co

/-- External from-reads: the read and the later write are on different cores. -/
def freOf (x : Exec) : Rel :=
  (frOf x).filter fun p => !sameCore x p.1 p.2

/-- External coherence: coherence edges across cores. -/
def coeOf (x : Exec) : Rel :=
  x.co.filter fun p => !sameCore x p.1 p.2

/-- The atomicity violations: `rmw` pairs `(r, w)` with a foreign write `w'`
    in between, i.e. `(r, w)` in `fre;coe`. An `rmw` pair and an intervening
    foreign write are incompatible. -/
def atomicViolations (x : Exec) : Rel :=
  ((freOf x).comp (coeOf x)).filter fun p => x.rmw.any (· == p)

/-- The atomicity axiom statement, as a Bool over a candidate execution:
    no `rmw` pair admits an intervening foreign write. -/
def atomicityHolds (x : Exec) : Bool :=
  atomicViolations x == []

/-- The writes that are the store half of an `rmw` pair. -/
def rmwWrites (x : Exec) : List Nat := x.rmw.map (·.2)

/-- Whether event `i` is an acquire read. -/
def isAcqReadId (x : Exec) (i : Nat) : Bool :=
  match x.ev? i with
  | none => false
  | some e => isAcqRead e

/-- `aob`, atomic-ordered-before (Arm ARM B2.3), as `Exec -> Rel` for agent 07's
    `OrderingParts.aob`: every `rmw` pair, plus the acquire read forwarded from
    the write of an `rmw` pair (`[range(rmw)];rfi`-style edge into an acquire). -/
def aob (x : Exec) : Rel :=
  x.rmw ++ (x.rf.filter fun p => (rmwWrites x).any (· == p.1) && isAcqReadId x p.2)

end Arm

/-
CUTS: aob and atomicity defined; theorems and spin-lock witness follow.
-/
