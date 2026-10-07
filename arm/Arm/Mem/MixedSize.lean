/-
  File:      Arm/Mem/MixedSize.lean
  Subject:   Byte-level view of a candidate execution and single-copy
             atomicity: every read/write event splits into per-byte events
             (little endian), whole `rf`/`co` induce per-byte `rf`/`co`, and
             an aligned 1/2/4/8-byte access is single-copy-atomic when all
             its bytes come from ONE write (no tearing).
  Model:     Arm single-copy atomicity (aligned accesses of 1, 2, 4, 8
             bytes observed whole; larger or unaligned accesses may tear;
             overlapping different-size accesses interact per byte), from the
             agent's knowledge of the published architecture, NOT a measured
             copy. Extends frozen `Event.lean` WITHOUT editing it.
             (Gabbro's `tearing.rs` is about emitted-C sequences, a different
             level, and is not needed here.)
-/
import Arm.Mem.Event

namespace Arm

/-- Byte identity inside the byte view: parent event id times 16 plus the
    byte index (accesses are at most 16 bytes, so this is injective). -/
def byteId (parent idx : Nat) : Nat := parent * 16 + idx

/-- Address plus a byte offset. -/
def addrPlus (a : Addr) (i : Nat) : Addr := a + BitVec.ofNat 64 i

/-- The (address, index) pairs one event touches: reads and writes touch
    their `size` bytes, barriers touch none. -/
def byteAddrs : Ev → List (Addr × Nat)
  | { kind := .read a, .. } => (List.range a.size).map fun i => (addrPlus a.addr i, i)
  | { kind := .write a, .. } => (List.range a.size).map fun i => (addrPlus a.addr i, i)
  | { kind := .barrier _, .. } => []

/-- Per-byte reads-from induced by whole `rf`: for each whole pair, every
    read byte covered by the write yields a byte pair at the same address. -/
def rfB (x : Exec) : Rel :=
  x.rf.flatMap fun p =>
    match x.ev? p.1, x.ev? p.2 with
    | some w, some r =>
      (byteAddrs r).flatMap fun ri =>
        match (byteAddrs w).find? (fun wj => wj.1 == ri.1) with
        | some wj => [(byteId w.id wj.2, byteId r.id ri.2)]
        | none => []
    | _, _ => []

/-- Per-byte coherence induced by whole `co`, same construction. -/
def coB (x : Exec) : Rel :=
  x.co.flatMap fun p =>
    match x.ev? p.1, x.ev? p.2 with
    | some w, some r =>
      (byteAddrs r).flatMap fun ri =>
        match (byteAddrs w).find? (fun wj => wj.1 == ri.1) with
        | some wj => [(byteId w.id wj.2, byteId r.id ri.2)]
        | none => []
    | _, _ => []

end Arm

/-
CUTS: skeleton; single-copy predicate and fixtures follow.
-/
