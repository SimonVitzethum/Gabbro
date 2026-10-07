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

end Arm

/-
CUTS: the alignment test, offset addition and register extension are
present with ground examples. SP handling, the memory accessors with their
fault behaviour and every instruction semantic are still missing (all listed
in REPORT-12.md).
-/

#print axioms Arm.addrEx1_aligned4
#print axioms Arm.extendReg_sxtw_sign
