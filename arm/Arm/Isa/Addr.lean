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

end Arm

/-
CUTS: only the alignment test and offset addition are present. Register
extension, SP handling, the memory accessors with their fault behaviour and
every instruction semantic are still missing (all listed in REPORT-12.md).
-/

#print axioms Arm.addrEx1_aligned4
