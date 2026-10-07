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

end Arm

/-
CUTS: only the value-extension helper is present. All instruction semantics
(single, pair, ordered, exclusive, literal) are still missing; they are
listed in REPORT-12.md.
-/

#print axioms Arm.extVal_sign8
