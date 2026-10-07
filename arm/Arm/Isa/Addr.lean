/-
  File:      Arm/Isa/Addr.lean
  Subject:   Address computation for AArch64 loads and stores: alignment test
             and wrapping signed-offset addition. Sequential model.
-/
import Arm.Isa.Monad

namespace Arm

/-- `IsAligned(address, size)`: the alignment test every `Mem_read`/`Mem_set`
    path applies before the fault check.
    -- Sail: v8_base.sail:28178 (`Mem_read__2`). -/
def isAligned (addr : Addr) (nbytes : Nat) : Bool :=
  nbytes != 0 && addr.toNat % nbytes == 0

/-- Wrapping address-plus-signed-offset: the `address + offset` of every
    execute clause (offsets arrive sign- or zero-extended to 64 bits).
    -- Sail: instrs64.sail:39785 (unsigned immediate; same shape everywhere). -/
def addOff (base : Addr) (off : Int) : Addr :=
  BitVec.ofNat 64 (Int.toNat (((base.toNat : Int) + off).emod (2 ^ 64)))

/-- Example base address used by the checks below. -/
def addrEx1 : Addr := BitVec.ofNat 64 4096

theorem addrEx1_aligned4 : isAligned addrEx1 4 = true := by decide

theorem addrEx1_misaligned3 : isAligned addrEx1 3 = false := by decide

theorem addrEx1_addOff : addOff addrEx1 8 = BitVec.ofNat 64 4104 := by decide

/-- The register-offset extend types of the load/store register-offset form.
    This mirrors Sail `ExtendType`; the option-bits-to-type table is the
    decoder's (`DecodeRegExtend`).
    -- Sail: v8_base.sail:35744 (`DecodeRegExtend`). -/
inductive ExtendKind where
  | uxtb | uxth | uxtw | uxtx | sxtb | sxth | sxtw | sxtx
  deriving DecidableEq, Repr

/-- `(len, isSigned)` of each extend type: the `len`/`is_unsigned` assigned
    by the match arms of `ExtendReg`.
    -- Sail: v8_base.sail:35780 (`ExtendReg`, arms at 35785-35813). -/
def extendKindParams : ExtendKind → Nat × Bool
  | .uxtb => (8, false)
  | .uxth => (16, false)
  | .uxtw => (32, false)
  | .uxtx => (64, false)
  | .sxtb => (8, true)
  | .sxth => (16, true)
  | .sxtw => (32, true)
  | .sxtx => (64, true)

/-- `ExtendReg(reg, exttype, shift, 64)`: take the low `len` bits of the
    offset register (clamped to `64 - shift`), shift them left by `shift`,
    then sign- or zero-extend to 64 bits. The caller reads the register;
    this is the pure computation on its value.
    -- Sail: v8_base.sail:35780 (`ExtendReg`). -/
def extendReg (val : BitVec 64) (k : ExtendKind) (shift : Nat) : Addr :=
  let (len, isSigned) := extendKindParams k
  let lenC := Nat.min len (64 - shift)
  let x := val.toNat % 2 ^ lenC
  let y := x * 2 ^ shift
  let w := lenC + shift
  let e :=
    if isSigned && w < 64 && 2 ^ (w - 1) ≤ y then y + (2 ^ 64 - 2 ^ w) else y
  BitVec.ofNat 64 e

theorem extendReg_uxtx_id :
    extendReg (BitVec.ofNat 64 4660) .uxtx 0 = BitVec.ofNat 64 4660 := by decide

theorem extendReg_sxtw_sign :
    extendReg (BitVec.ofNat 64 4294967295) .sxtw 0
      = BitVec.ofNat 64 18446744073709551615 := by decide

theorem extendReg_uxth_shift :
    extendReg (BitVec.ofNat 64 43981) .uxth 2 = BitVec.ofNat 64 175924 := by decide

/-- Planted wrong case: a signed 32-to-64 extension is not zero extension. -/
theorem extendReg_sxtw_notZero :
    extendReg (BitVec.ofNat 64 4294967295) .sxtw 0
      ≠ BitVec.ofNat 64 4294967295 := by decide

/-- Register 31 is the stack pointer: `rdX 31`/`wrX 31` read and write SP.
    This is the `if n == 31 then SP_read() else X_read(n, 64)` found in every
    load/store execute clause.
    -- Sail: instrs64.sail:39785 (and every other execute clause). -/
def rdBase (n : Nat) : Eff Addr := .rdX n .ret

/-- Writeback target: `if n == 31 then SP_set() else X_set(n, 64)`.
    -- Sail: instrs64.sail:32821 (post-index writeback). -/
def wrBase (n : Nat) (v : Addr) : Eff Unit := .wrX n v (.ret ())

/-- `CheckSPAlignment()`: trap unless SP is 16-byte aligned. Sail gates this
    on the SCTLR SA/SA0 bits; the sequential model always enforces it (the
    SCTLR gating belongs to the system agent; see CUTS).
    -- Sail: v8_base.sail:22782 (`CheckSPAlignment`). -/
def checkSP : Eff Unit :=
  .rdX 31 fun sp => if sp.toNat % 16 == 0 then .ret () else .raise (.alignment sp)

/-- Whether an access faults when misaligned. Plain non-exclusive accesses
    proceed bytewise (Sail `AArch64_UnalignedAccessFaults` answers false for
    them); ordered (acquire/release) and exclusive accesses fault. The
    SCTLR.A gating of the plain case and the LSE2 16-byte-quantity rule for
    the ordered/exclusive case are system/hardware configuration owned by
    the system agent (see CUTS).
    -- Sail: v8_base.sail:22799 (`AArch64_UnalignedAccessFaults`). -/
def needsAlign : AccOrd → Bool → Bool
  | .plain, false => false
  | _, _ => true

/-- Translation-fault oracle: `fault addr nbytes` says whether the access
    faults in translation. The page tables and the `AArch64_TranslateAddress`
    walk belong to the system agent; the sequential instruction model
    consumes only the verdict and raises the abort.
    -- Sail: mem.sail/interface.sail (accessors reach the memory interface). -/
structure MemCfg where
  fault : Addr → Nat → Bool

/-- One checked read: translation fault first, then the alignment fault,
    then the plain little-endian `Mem_read` event the multicore model
    consumes. Sizes 1, 2, 4, 8 (and 16 for pairs) come from the caller.
    -- Sail: v8_base.sail:28178 (`Mem_read__2`: aligned test, then abort). -/
def memReadEff (cfg : MemCfg) (addr : Addr) (nbytes : Nat)
    (ord : AccOrd) (excl : Bool) : Eff Nat :=
  if cfg.fault addr nbytes then .raise (.dataAbort addr)
  else if needsAlign ord excl && !isAligned addr nbytes then
    .raise (.alignment addr)
  else .rdMem ⟨addr, nbytes, ord, excl⟩ .ret

/-- One checked write: the mirror image with `Mem_set`.
    -- Sail: v8_base.sail:28260 (`Mem_set__2`: aligned test, then abort). -/
def memWriteEff (cfg : MemCfg) (addr : Addr) (nbytes : Nat)
    (ord : AccOrd) (excl : Bool) (val : Nat) : Eff Unit :=
  if cfg.fault addr nbytes then .raise (.dataAbort addr)
  else if needsAlign ord excl && !isAligned addr nbytes then
    .raise (.alignment addr)
  else .wrMem ⟨addr, nbytes, ord, excl⟩ val (.ret ())

theorem needsAlign_plain : needsAlign .plain false = false := by decide

theorem needsAlign_acquire : needsAlign .acquire false = true := by decide

theorem needsAlign_excl : needsAlign .plain true = true := by decide

/-- Tiny sequential fixture: GPRs (31 is SP), PC, V regs as 128-bit Nats,
    NZCV, and byte memory as `Nat → Nat` keyed by the address value.
    Memory values are masked to bytes on every access. -/
structure Regs where
  gpr : Nat → BitVec 64
  pc : BitVec 64
  vpr : Nat → Nat
  nzcv : BitVec 4

structure State where
  regs : Regs
  mem : Nat → Nat

/-- Little-endian byte assembly: the value a `Mem_read` of `n` bytes at
    `base` returns. Sail assembles bytes little-endian for the
    non-big-endian case (`Mem_read__2`: `BigEndianReverse` only under
    `BigEndian`; GPR accesses are little-endian).
    -- Sail: v8_base.sail:28178 (`Mem_read__2`). -/
def loadNat (mem : Nat → Nat) (base : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => mem (base % 2 ^ 64) % 256 + 256 * loadNat mem (base + 1) n

/-- Point update of a `Nat`-indexed table. -/
def upd {α : Type} (f : Nat → α) (k : Nat) (v : α) : Nat → α :=
  fun i => if i == k then v else f i

/-- Little-endian byte scatter: the memory a `Mem_set` of `n` bytes at
    `base` leaves behind.
    -- Sail: v8_base.sail:28260 (`Mem_set__2`). -/
def storeNat (mem : Nat → Nat) (base : Nat) (val : Nat) (n : Nat) : Nat → Nat :=
  match n with
  | 0 => mem
  | m + 1 =>
    storeNat (upd mem (base % 2 ^ 64) (val % 256)) (base + 1) (val / 256) m

/-- Run one `Eff` program on the fixture with bounded fuel. `rdMem`/`wrMem`
    go through the little-endian byte memory; `raise` (data abort,
    alignment, undefined) is `none`. Named system registers and barriers
    are out of scope for the load/store lane: `rdSys`/`wrSys` refuse
    (`none`), barriers step over. -/
def runEff : Nat → Eff α → State → Option (α × State)
  | 0, _, _ => none
  | fuel + 1, .ret a, s => some (a, s)
  | fuel + 1, .rdX n k, s => runEff fuel (k (s.regs.gpr n)) s
  | fuel + 1, .wrX n v k, s =>
    runEff fuel k { s with regs := { s.regs with gpr := upd s.regs.gpr n v } }
  | fuel + 1, .rdV n k, s =>
    runEff fuel (k (BitVec.ofNat 128 (s.regs.vpr n))) s
  | fuel + 1, .wrV n v k, s =>
    runEff fuel k { s with regs := { s.regs with vpr := upd s.regs.vpr n v.toNat } }
  | fuel + 1, .rdPC k, s => runEff fuel (k s.regs.pc) s
  | fuel + 1, .wrPC v k, s =>
    runEff fuel k { s with regs := { s.regs with pc := v } }
  | fuel + 1, .rdNZCV k, s => runEff fuel (k s.regs.nzcv) s
  | fuel + 1, .wrNZCV v k, s =>
    runEff fuel k { s with regs := { s.regs with nzcv := v } }
  | fuel + 1, .rdMem a k, s =>
    runEff fuel (k (loadNat s.mem a.addr.toNat a.size)) s
  | fuel + 1, .wrMem a v k, s =>
    runEff fuel k { s with mem := storeNat s.mem a.addr.toNat v a.size }
  | fuel + 1, .bar _ k, s => runEff fuel k s
  | _, _, _ => none

/-- All-zero machine: every register and every byte reads 0. -/
def s0 : State :=
  { regs :=
      { gpr := fun _ => BitVec.ofNat 64 0
        pc := BitVec.ofNat 64 0
        vpr := fun _ => 0
        nzcv := BitVec.ofNat 4 0 }
    mem := fun _ => 0 }

/-- No translation fault anywhere. -/
def cfgNoFault : MemCfg := ⟨fun _ _ => false⟩

/-- Every access faults in translation. -/
def cfgFault : MemCfg := ⟨fun _ _ => true⟩

end Arm

/-
CUTS: the alignment test, offset addition and register extension are
present with ground examples. SP handling, the memory accessors with their
fault behaviour and every instruction semantic are still missing (all listed
in REPORT-12.md).
-/

#print axioms Arm.addrEx1_aligned4
#print axioms Arm.extendReg_sxtw_sign
