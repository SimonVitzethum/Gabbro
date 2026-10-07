/-
  File:      Arm/Isa/Interp.lean
  Subject:   Concrete test interpreter for the `Eff` effect tree: a `Machine`
             record (GPRs, SP, PC, NZCV, SIMD regs, sysregs, byte memory) and
             `run`. Association lists keep every test vector decidable.
  Sail:      sail-arm/arm-v9.4-a/src/interface.sail (register/memory accessors),
             sail-arm/arm-v9.4-a/src/mem.sail:85 (`_Mem_read` byte transport).
-/
import Arm.Isa.Monad

namespace Arm

/-- Concrete test machine. `x` holds X0-X30 (index 31 reads as zero, writes
    are discarded: XZR); `mem` maps byte addresses to bytes, absent reads 0. -/
-- Sail: interface.sail (register file), mem.sail:85 (byte-addressed memory).
structure Machine where
  x : List (BitVec 64)
  sp : BitVec 64
  pc : BitVec 64
  nzcv : BitVec 4
  v : List (BitVec 128)
  sys : List (String × BitVec 64)
  mem : List (Nat × Nat)

/-- Replace element `n` (no-op past the end). -/
def setNth {α : Type} : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | y :: xs, k + 1, v => y :: setNth xs k v

/-- Read X `n` (31 is XZR); short register files read as zero. -/
-- Sail: interface.sail (`X_read`: 31 is the zero register).
def getX (m : Machine) (n : Nat) : BitVec 64 :=
  if n == 31 then BitVec.ofNat 64 0
  else match m.x[n]? with | some b => b | none => BitVec.ofNat 64 0

/-- Write X `d` (31 is XZR: discarded). -/
-- Sail: interface.sail (`X_set`: 31 writes nowhere).
def setX (m : Machine) (n : Nat) (v : BitVec 64) : Machine :=
  if n == 31 then m else { m with x := setNth m.x n v }

end Arm

/-
CUTS: skeleton only. V registers, sysregs, memory and `run` are open.
-/
