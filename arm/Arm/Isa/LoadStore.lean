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

end Arm

/-
CUTS: only the value-extension helper is present. All instruction semantics
(single, pair, ordered, exclusive, literal) are still missing; they are
listed in REPORT-12.md.
-/

#print axioms Arm.extVal_sign8
