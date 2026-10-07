/-
  File:      Arm/Isa/IntCore.lean
  Subject:   Shared Nat-level helpers for the integer data-processing semantics:
             widths, masks, truncation and the register/flag interface over `Eff`.
             All values are natural numbers below `2 ^ w`; `BitVec` appears only
             at the `Eff` boundary (`BitVec.ofNat` / `BitVec.toNat`).
  Sail:      sail-arm/arm-v9.4-a/src/builtins.sail (UInt/SInt/ZeroExtend view).
-/
import Arm.Isa.Monad

namespace Arm.Int

/-- Two to the power `w`: the modulus of a `w`-bit register field. -/
def pow2 (w : Nat) : Nat := 2 ^ w

/-- All-ones mask of width `w`: `2 ^ w - 1`. -/
def mask (w : Nat) : Nat := pow2 w - 1

/-- Truncate `v` into `w` bits (Sail slicing `result[w-1..0]`). -/
def trunc (w v : Nat) : Nat := v % pow2 w

/-- Read the low `w` bits of X register `n` (w = 32 or 64). -/
def rdXn (n w : Nat) : Eff Nat :=
  Eff.rdX n fun v => Eff.ret ((v.toNat) % pow2 w)

/-- Write `v` (already truncated) to X register `d`, zeroing the upper half. -/
def wrXn (d w v : Nat) : Eff Unit :=
  Eff.wrX d (BitVec.ofNat 64 (v % pow2 w)) (Eff.ret ())

/-- Signed reading of a `w`-bit value (Sail `SInt`). -/
-- Sail: builtins.sail `SInt` (two's complement against `UInt`).
def sintOf (w x : Nat) : Int :=
  if pow2 (w - 1) ≤ x then (x : Int) - (pow2 w : Int) else (x : Int)

/-- Sail `AddWithCarry`: unsigned sum, truncated result and the NZCV flags. -/
-- Sail: v8_base.sail:13337 (`AddWithCarry (x, y, carry_in)`).
-- `x`, `y` are below `2 ^ w`; `c` is the carry-in. Returns
-- `(result, N, Z, C, V)` with `C` = carry out and `V` = signed overflow.
def addWithCarry (w x y : Nat) (c : Bool) : Nat × Bool × Bool × Bool × Bool :=
  let cin : Nat := if c then 1 else 0
  let s := x + y + cin
  let r := s % pow2 w
  let n := decide (pow2 (w - 1) ≤ r)
  let z := decide (r = 0)
  let cout := decide (pow2 w ≤ s)
  let ss := sintOf w x + sintOf w y + (if c then 1 else 0)
  let v := decide (sintOf w r ≠ ss)
  (r, n, z, cout, v)

/-- 200 + 100 wraps to 44 with carry out, no signed overflow. -/
-- Sail: v8_base.sail:13337, checked against the definition by hand.
theorem addWithCarry_ex1 : addWithCarry 8 200 100 false = (44, false, false, true, false) := by
  decide

/-- 127 + 1 overflows the signed 8-bit range: N and V set, no carry. -/
-- Sail: v8_base.sail:13337.
theorem addWithCarry_ex2 : addWithCarry 8 127 1 false = (128, true, false, false, true) := by
  decide

/-- SUB shape 5 - 3 as `AddWithCarry(5, ~3, 1)`: result 2, carry set. -/
-- Sail: instrs64.sail:434 (`execute ... add_sub_shiftedreg`, sub path).
theorem addWithCarry_sub : addWithCarry 8 5 252 true = (2, false, false, true, false) := by
  decide

/-- Planted wrong case: the carry out of 200 + 100 is set, not clear. -/
theorem addWithCarry_wrong : addWithCarry 8 200 100 false ≠ (44, false, false, false, false) := by
  decide

/-- Pack four flag bools into the NZCV number (N=8, Z=4, C=2, V=1). -/
-- Sail: v8_base.sail `PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V` order.
def nzcvOf (n z c v : Bool) : Nat :=
  (if n then 8 else 0) + (if z then 4 else 0) + (if c then 2 else 0) + (if v then 1 else 0)

/-- Write packed NZCV flags. -/
def wrNZCVn (nzcv : Nat) : Eff Unit :=
  Eff.wrNZCV (BitVec.ofNat 4 (nzcv % 16)) (Eff.ret ())

/-- Read packed NZCV flags as four bools. -/
def rdNZCVn : Eff (Bool × (Bool × (Bool × Bool))) :=
  Eff.rdNZCV fun v =>
    let m := v.toNat % 16
    Eff.ret ((m / 8) % 2 == 1, ((m / 4) % 2 == 1, ((m / 2) % 2 == 1, m % 2 == 1)))

/-- Sail `ConditionHolds`: does `cond` hold under packed `nzcv`? -/
-- Sail: v8_base.sail:8954. Bit 0 inverts the row except for `0b1111` (AL);
-- `0b1110` has bit 0 clear, so like AL it always holds (NV behaves as AL).
def condHolds (nzcv cond : Nat) : Bool :=
  let n := (nzcv / 8) % 2 == 1
  let z := (nzcv / 4) % 2 == 1
  let c := (nzcv / 2) % 2 == 1
  let v := nzcv % 2 == 1
  let row : Bool :=
    match (cond / 2) % 8 with
    | 0 => z
    | 1 => c
    | 2 => n
    | 3 => v
    | 4 => c && !z
    | 5 => n == v
    | 6 => (n == v) && !z
    | _ => true
  if cond % 2 == 1 && cond % 16 != 15 then !row else row

/-- EQ holds when Z is set. -/
-- Sail: v8_base.sail:8954.
theorem condHolds_eq : condHolds 4 0 = true := by decide

/-- EQ fails when Z is clear. -/
-- Sail: v8_base.sail:8954.
theorem condHolds_eq_off : condHolds 0 0 = false := by decide

/-- NV (0b1110) behaves as AL: it always holds, even with no flag set. -/
-- Sail: v8_base.sail:8954 (bit 0 of `0b1110` is clear, so no inversion).
theorem condHolds_nv : condHolds 0 14 = true := by decide

/-- AL (0b1111) always holds, even with no flag set. -/
-- Sail: v8_base.sail:8954.
theorem condHolds_al : condHolds 0 15 = true := by decide

/-- Planted wrong case: EQ with Z clear is not true. -/
theorem condHolds_wrong : condHolds 0 0 ≠ true := by decide

/-- Shift kinds (Sail `ShiftType`). -/
-- Sail: v8_base.sail `DecodeShift` (00 LSL, 01 LSR, 10 ASR, 11 ROR).
inductive ShiftTy where
  | lsl | lsr | asr | ror
  deriving DecidableEq, Repr

/-- Decode the 2-bit shift field; `0b11` (ROR) is refused here. -/
-- Sail: instrs64.sail `decode_add_addsub_shift` (`if shift == 0b11 then Undefined`)
-- and v8_base.sail `DecodeShift`. The ROR-typed shifts keep their own decoder.
def decodeShiftNoRor (s : Nat) : Option ShiftTy :=
  match s with
  | 0 => some .lsl
  | 1 => some .lsr
  | 2 => some .asr
  | _ => none

/-- Decode any 2-bit shift field (Sail `DecodeShift`, total). -/
-- Sail: v8_base.sail `DecodeShift`.
def decodeShift (s : Nat) : ShiftTy :=
  match s % 4 with
  | 0 => .lsl
  | 1 => .lsr
  | 2 => .asr
  | _ => .ror

/-- Logical shift left, truncated to `w` bits (Sail `LSL`). -/
-- Sail: builtins.sail `LSL_C`/`sail_shiftleft`.
def shlW (w v a : Nat) : Nat := (v * pow2 a) % pow2 w

/-- Logical shift right (Sail `LSR`). -/
-- Sail: builtins.sail `LSR_C`/`sail_shiftright`.
def shrW (v a : Nat) : Nat := v / pow2 a

/-- Arithmetic shift right with sign fill (Sail `ASR`). -/
-- Sail: builtins.sail `ASR_C`/`sail_arith_shiftright`.
def asrW (w v a : Nat) : Nat :=
  let k := if a < w then a else w
  let low := v / pow2 a
  let fill := if pow2 (w - 1) ≤ v % pow2 w then pow2 w - pow2 (w - k) else 0
  low + fill

/-- Rotate right (Sail `ROR`: no-op for shift 0, else `LSR | LSL`). -/
-- Sail: builtins.sail `ROR`.
def rorW (w v a : Nat) : Nat :=
  if w = 0 then 0
  else
    let m := a % w
    (v / pow2 m + v * pow2 (w - m)) % pow2 w

/-- Sail `ShiftReg`: shift `v` (already `w` bits) by `a` with kind `st`. -/
-- Sail: v8_base.sail:35851 (`ShiftReg (reg, shiftype, amount, N)`).
def shiftReg (w v : Nat) (st : ShiftTy) (a : Nat) : Nat :=
  match st with
  | .lsl => shlW w v a
  | .lsr => shrW v a
  | .asr => asrW w v a
  | .ror => rorW w v a

/-- `LSL #2` of 1 in 32 bits is 4. -/
-- Sail: builtins.sail `sail_shiftleft`.
theorem shiftReg_lsl : shiftReg 32 1 .lsl 2 = 4 := by decide

/-- `LSR #1` of 3 is 1. -/
-- Sail: builtins.sail `sail_shiftright`.
theorem shiftReg_lsr : shiftReg 32 3 .lsr 1 = 1 := by decide

/-- `ASR #1` of `0x80000000` keeps the sign: `0xC0000000`. -/
-- Sail: builtins.sail `sail_arith_shiftright`.
theorem shiftReg_asr : shiftReg 32 0x80000000 .asr 1 = 0xC0000000 := by decide

/-- `ROR #8` of `0x12345678` is `0x78123456`. -/
-- Sail: builtins.sail `ROR`.
theorem shiftReg_ror : shiftReg 32 0x12345678 .ror 8 = 0x78123456 := by decide

/-- Planted wrong case: `LSL #2` of 1 is not 8. -/
theorem shiftReg_wrong : shiftReg 32 1 .lsl 2 ≠ 8 := by decide

end Arm.Int

/-
CUTS: skeleton only. No helper proved yet; `addWithCarry`, shifts, extend,
`DecodeBitMasks` and all instruction semantics are open.
-/
