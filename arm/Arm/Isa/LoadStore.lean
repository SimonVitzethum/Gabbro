/-
  File:      Arm/Isa/LoadStore.lean
  Subject:   Execute-level semantics of the AArch64 load and store
             instructions, from decoded fields to `Eff Unit`.
             Agent 15 writes the decoder; this file is the `execute` side.
-/
import Arm.Isa.Addr

namespace Arm

/-- `X_set(t, regsize) = SignExtend/ZeroExtend(data, regsize)`: extend a
    `datasize`-bit memory value to the destination register. A 32-bit
    destination (`regsize = 32`) zero-fills the top half, as `X_set(t, 32)`
    does. Pure Nat arithmetic; the result is the full 64-bit register value.
    -- Sail: instrs64.sail:32821 (post-index execute, `MemOp_LOAD` arm). -/
def extVal (v datasize regsize : Nat) (isSigned : Bool) : BitVec 64 :=
  let x := v % 2 ^ datasize
  let y :=
    if isSigned && datasize < regsize && 2 ^ (datasize - 1) ≤ x then
      x + (2 ^ regsize - 2 ^ datasize)
    else x
  BitVec.ofNat 64 (y % 2 ^ regsize)

theorem extVal_sign8 :
    extVal 255 8 64 true = BitVec.ofNat 64 18446744073709551615 := by decide

theorem extVal_zero8 :
    extVal 255 8 64 false = BitVec.ofNat 64 255 := by decide

theorem extVal_w32 :
    extVal 1 8 32 false = BitVec.ofNat 64 1 := by decide

/-- Single-copy general-register load/store with an immediate offset, from
    decoded fields to `Eff Unit`:
    - `datasize`: access width in bits (8/16/32/64: LDRB/LDRH/LDR/STR and
      the signed forms LDRSB/LDRSH/LDRSW);
    - `regsize`: destination/source register width in bits (32/64);
    - `off`: the offset already scaled and sign-extended to 64 bits;
    - `postindex`/`wback`: unsigned/unscaled (`false`/`false`), pre-index
      (`false`/`true`), post-index (`true`/`true`).
    The access is plain (`AccOrd.plain`, not exclusive); the multicore model
    consumes exactly the `rdMem`/`wrMem` event this emits.
    -- Sail: instrs64.sail:39785 (unsigned), :32821 (post-index),
       :37495 (unscaled LDUR/STUR and pre-index). -/
def ldStSingle (cfg : MemCfg) (isLoad : Bool) (datasize regsize : Nat)
    (n : Nat) (off : Int) (postindex wback : Bool)
    (isSigned : Bool) (t : Nat) : Eff Unit := do
  if n == 31 then checkSP else pure ()
  let base ← rdBase n
  let addr := if postindex then base else addOff base off
  if isLoad then
    let v ← memReadEff cfg addr (datasize / 8) .plain false
    wrBase t (extVal v datasize regsize isSigned)
  else
    let rv ← rdBase t
    memWriteEff cfg addr (datasize / 8) .plain false (rv.toNat % 2 ^ datasize)
  if wback then
    wrBase n (if postindex then addOff base off else addr)
  else pure ()

/-- GPR table of the fixture: X0 holds `0xAABBCCDD`, X1 holds base 64. -/
def gprLS : Nat → BitVec 64 :=
  upd (upd s0.regs.gpr 0 (BitVec.ofNat 64 2864434397)) 1 (BitVec.ofNat 64 64)

/-- Fixture: X0 holds `0xAABBCCDD`, X1 holds base address 64. -/
def sLS : State := { s0 with regs := { s0.regs with gpr := gprLS } }

/-- `STR W0, [X1]` then `LDR W2, [X1]`: the word round-trips. -/
def exStrLdrW : Eff (BitVec 64) := do
  ldStSingle cfgNoFault false 32 32 1 0 false false false 0
  ldStSingle cfgNoFault true 32 32 1 0 false false false 2
  rdBase 2

theorem exStrLdrW_ok :
    (runEff 60 exStrLdrW sLS).map Prod.fst
      = some (BitVec.ofNat 64 2864434397) := by decide

/-- `STR B0, [X1]` then `LDRSB X3, [X1]`: byte `0xDD` sign-extends. -/
def exLdrsb : Eff (BitVec 64) := do
  ldStSingle cfgNoFault false 8 32 1 0 false false false 0
  ldStSingle cfgNoFault true 8 64 1 0 false false true 3
  rdBase 3

theorem exLdrsb_ok :
    (runEff 60 exLdrsb sLS).map Prod.fst
      = some (BitVec.ofNat 64 18446744073709551581) := by decide

/-- Planted wrong case: `LDRSB` does not zero-extend (`0xDD` is 221). -/
theorem exLdrsb_notZero :
    (runEff 60 exLdrsb sLS).map Prod.fst ≠ some (BitVec.ofNat 64 221) := by decide

/-- `STR X0, [X1, #8]!`: pre-index writes the base back (64 becomes 72). -/
def exPreIdx : Eff (BitVec 64) := do
  ldStSingle cfgNoFault false 64 64 1 8 false true false 0
  rdBase 1

theorem exPreIdx_ok :
    (runEff 60 exPreIdx sLS).map Prod.fst = some (BitVec.ofNat 64 72) := by decide

/-- `STR X0, [X1], #8` then `LDR X2, [X1, #-8]`: the store lands at the
    un-incremented base and the later load finds it there. -/
def exPostIdx : Eff (BitVec 64) := do
  ldStSingle cfgNoFault false 64 64 1 8 true true false 0
  ldStSingle cfgNoFault true 64 64 1 (-8) false false false 2
  rdBase 2

theorem exPostIdx_ok :
    (runEff 60 exPostIdx sLS).map Prod.fst
      = some (BitVec.ofNat 64 2864434397) := by decide

/-- Register-offset form: `address = base + ExtendReg(m, ext, shift, 64)`,
    no writeback. The option-bits-to-extend-type table is the decoder's
    (`DecodeRegExtend`); this is the `execute` side.
    -- Sail: instrs64.sail:35210. -/
def ldStReg (cfg : MemCfg) (isLoad : Bool) (datasize regsize : Nat)
    (n : Nat) (m : Nat) (k : ExtendKind) (shift : Nat)
    (isSigned : Bool) (t : Nat) : Eff Unit := do
  if n == 31 then checkSP else pure ()
  let base ← rdBase n
  let off ← rdBase m
  let addr := addOff base (Int.ofNat (extendReg off k shift).toNat)
  if isLoad then
    let v ← memReadEff cfg addr (datasize / 8) .plain false
    wrBase t (extVal v datasize regsize isSigned)
  else
    let rv ← rdBase t
    memWriteEff cfg addr (datasize / 8) .plain false (rv.toNat % 2 ^ datasize)

/-- Fixture: as `sLS`, plus X5 holds offset register value 16. -/
def gprLSR : Nat → BitVec 64 := upd gprLS 5 (BitVec.ofNat 64 16)

def sLSR : State := { s0 with regs := { s0.regs with gpr := gprLSR } }

/-- `STR X0, [X1, X5, LSL #3]` then the matching load: 64 + 16*8 = 192. -/
def exRegOff : Eff (BitVec 64) := do
  ldStReg cfgNoFault false 64 64 1 5 .uxtx 3 false 0
  ldStReg cfgNoFault true 64 64 1 5 .uxtx 3 false 2
  rdBase 2

theorem exRegOff_ok :
    (runEff 60 exRegOff sLSR).map Prod.fst
      = some (BitVec.ofNat 64 2864434397) := by decide

/-- The shifted store leaves the unshifted address alone: loading from
    `[X1]` after the `[X1, X5, LSL #3]` store reads zero. -/
def exRegOff_miss : Eff (BitVec 64) := do
  ldStReg cfgNoFault false 64 64 1 5 .uxtx 3 false 0
  ldStSingle cfgNoFault true 64 64 1 0 false false false 2
  rdBase 2

theorem exRegOff_miss_ok :
    (runEff 60 exRegOff_miss sLSR).map Prod.fst
      = some (BitVec.ofNat 64 0) := by decide

/-- Fixture: as `sLS`, plus X5 holds `0xFFFFFFFF`. -/
def gprLSRs : Nat → BitVec 64 := upd gprLS 5 (BitVec.ofNat 64 4294967295)

def sLSRs : State := { s0 with regs := { s0.regs with gpr := gprLSRs } }

/-- `SXTW` sign-extends the offset: 64 + sext(`0xFFFFFFFF`) wraps to 63. -/
def exRegSxtw : Eff (BitVec 64) := do
  ldStReg cfgNoFault false 8 32 1 5 .sxtw 0 false 0
  ldStReg cfgNoFault true 8 64 1 5 .sxtw 0 true 2
  rdBase 2

theorem exRegSxtw_ok :
    (runEff 60 exRegSxtw sLSRs).map Prod.fst
      = some (BitVec.ofNat 64 18446744073709551581) := by decide

/-- PC-relative literal load (`LDR Wt/Xt, [PC, #off]`, `LDRSW`): address is
    PC plus the already sign-extended `imm19 @ 00` offset; size 4 or 8
    bytes; the 4-byte form sign-extends only for `LDRSW`. Prefetch (`PRFM`)
    is a pure hint with no semantic effect and is not modelled (CUTS).
    -- Sail: instrs64.sail:32630. -/
def ldrLiteral (cfg : MemCfg) (sizeBytes regsize : Nat) (off : Int)
    (isSigned : Bool) (t : Nat) : Eff Unit := do
  let pc ← .rdPC .ret
  let addr := addOff pc off
  let v ← memReadEff cfg addr sizeBytes .plain false
  wrBase t (extVal v (sizeBytes * 8) regsize isSigned)

/-- Fixture: PC is 4096 and address 4104 holds `0xAABBCCDD`. -/
def memLit : Nat → Nat := storeNat s0.mem 4104 2864434397 4

def sLit : State :=
  { regs := { s0.regs with pc := BitVec.ofNat 64 4096 }, mem := memLit }

/-- `LDR W2, [PC, #8]`: the word at PC+8 loads zero-extended. -/
def exLit : Eff (BitVec 64) := do
  ldrLiteral cfgNoFault 4 32 8 false 2
  rdBase 2

theorem exLit_ok :
    (runEff 60 exLit sLit).map Prod.fst
      = some (BitVec.ofNat 64 2864434397) := by decide

/-- `LDRSW X2, [PC, #8]`: `0xAABBCCDD` has its top bit set, so it
    sign-extends; it is not the zero-extended word. -/
def exLitSw : Eff (BitVec 64) := do
  ldrLiteral cfgNoFault 4 64 8 true 2
  rdBase 2

theorem exLitSw_ok :
    (runEff 60 exLitSw sLit).map Prod.fst
      = some (BitVec.ofNat 64 18446744072279018717) := by decide

theorem exLitSw_notZero :
    (runEff 60 exLitSw sLit).map Prod.fst
      ≠ some (BitVec.ofNat 64 2864434397) := by decide

end Arm

/-
CUTS: only the value-extension helper is present. All instruction semantics
(single, pair, ordered, exclusive, literal) are still missing; they are
listed in REPORT-12.md.
-/

#print axioms Arm.extVal_sign8
