/-
  File:      Arm/Isa/Interp.lean
  Subject:   Concrete test interpreter for the `Eff` effect tree: a `Machine`
             record (GPRs, SP, PC, NZCV, SIMD regs, sysregs, byte memory) and
             `run`. Association lists keep every test vector decidable.
  Sail:      sail-arm/arm-v9.4-a/src/interface.sail (register/memory accessors),
             sail-arm/arm-v9.4-a/src/mem.sail:85 (`_Mem_read` byte transport).
-/
import Arm.Isa.Monad
import Arm.Isa.IntCore

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

/-- Read V `n`; short files read as zero. -/
-- Sail: interface.sail (`V_read`).
def getV (m : Machine) (n : Nat) : BitVec 128 :=
  match m.v[n]? with | some b => b | none => BitVec.ofNat 128 0

/-- Write V `n`. -/
-- Sail: interface.sail (`V_set`).
def setV (m : Machine) (n : Nat) (v : BitVec 128) : Machine :=
  { m with v := setNth m.v n v }

/-- Read a named system register; `"SP"` is the stack pointer, others default
    to zero. -/
-- Sail: interface.sail (system accessors; `SP_read` for the stack pointer).
def getSys (m : Machine) (s : String) : BitVec 64 :=
  if s == "SP" then m.sp
  else match m.sys.find? (fun p => p.1 == s) with
    | some (_, v) => v
    | none => BitVec.ofNat 64 0

/-- Write a named system register; `"SP"` is the stack pointer. -/
-- Sail: interface.sail (`SP_set` for the stack pointer).
def setSys (m : Machine) (s : String) (v : BitVec 64) : Machine :=
  if s == "SP" then { m with sp := v }
  else { m with sys := (s, v) :: m.sys.filter (fun p => p.1 != s) }

/-- Read one byte (absent addresses read as zero). -/
-- Sail: mem.sail:85 (`_Mem_read` byte transport).
def ldByte (m : Machine) (a : Nat) : Nat :=
  match m.mem.find? (fun p => p.1 == a % Int.pow2 64) with
  | some (_, b) => b % 256
  | none => 0

/-- Write one byte (addresses wrap at 2^64). -/
-- Sail: mem.sail (`_Mem_set` byte transport).
def stByte (m : Machine) (a v : Nat) : Machine :=
  { m with mem := (a % Int.pow2 64, v % 256) ::
    m.mem.filter (fun p => p.1 != a % Int.pow2 64) }

/-- Little-endian load of `acc.size` bytes (1, 2, 4, 8, 16). -/
-- Sail: mem.sail:85; byte composition is little-endian (SCTLR.EE = 0).
def loadLE (m : Machine) (acc : Access) : Nat := go acc.size
where go : Nat → Nat
  | 0 => 0
  | (k+1) => ldByte m ((acc.addr.toNat + k) % Int.pow2 64) * 256 ^ k + go k

/-- Little-endian store of `acc.size` bytes (1, 2, 4, 8, 16). -/
-- Sail: mem.sail (`_Mem_set`); byte composition is little-endian.
def storeLE (m : Machine) (acc : Access) (v : Nat) : Machine := go acc.size m
where go : Nat → Machine → Machine
  | 0, s => s
  | (k+1), s =>
    go k (stByte s ((acc.addr.toNat + k) % Int.pow2 64) ((v / 256 ^ k) % 256))

end Arm

/-
CUTS: skeleton only. V registers, sysregs, memory and `run` are open.
-/
