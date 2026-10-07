/-
  File:      Arm/Isa/Integer.lean
  Subject:   Execute-level semantics of AArch64 integer data-processing:
             ADD/ADDS/SUB/SUBS (immediate, shifted register, extended register),
             ADC/SBC (+ADCS/SBCS), AND/ORR/EOR/ANDS (immediate, register),
             MOVZ/MOVN/MOVK and ADR/ADRP. Decoded fields in, `Eff Unit` out;
             the decoder itself is agent 15's. Pure cores are proved by `decide`
             on decode-derived examples; `Eff` wrappers are thin read-compute-write
             plumbing over the same cores.
  Sail:      sail-arm/arm-v9.4-a/src/instrs64.sail (`execute` clauses),
             sail-arm/arm-v9.4-a/src/v8_base.sail (shared pseudocode).
-/
import Arm.Isa.IntCore
import Arm.Isa.IntMasks

namespace Arm.Int

/-- Shared core of every add/subtract execute: optional inversion of `o2`
    plus `AddWithCarry` with an explicit carry-in. -/
-- Sail: instrs64.sail:434,589,751 (carry_in = sub ? 1 : 0) and
-- instrs64.sail:194 (carry_in = PSTATE.C, passed by the caller).
def addSubFlags (w o1 o2 : Nat) (sub : Bool) (cin : Bool) :
    Nat × Bool × Bool × Bool × Bool :=
  let y := if sub then pow2 w - 1 - o2 % pow2 w else o2 % pow2 w
  addWithCarry w (o1 % pow2 w) y cin

/-- ADD shape: no inversion, carry-in clear. -/
-- Sail: instrs64.sail:589.
theorem addSubFlags_add : addSubFlags 64 10 5 false false = (15, false, false, false, false) := by
  decide

/-- ADDS overflow: `0x7FFFFFFFFFFFFFFF + 1` sets N and V. -/
-- Sail: instrs64.sail:589.
theorem addSubFlags_adds :
    addSubFlags 64 0x7FFFFFFFFFFFFFFF 1 false false =
      (0x8000000000000000, true, false, false, true) := by
  decide

/-- SUBS shape: `5 - 3` gives 2 with carry set (no borrow). -/
-- Sail: instrs64.sail:434 (shifted-register sub path).
theorem addSubFlags_subs : addSubFlags 32 5 3 true true = (2, false, false, true, false) := by
  decide

/-- ADC shape: `0xFFF..F + 0 + C` wraps to zero with Z and C set. -/
-- Sail: instrs64.sail:194.
theorem addSubFlags_adc :
    addSubFlags 64 0xFFFFFFFFFFFFFFFF 0 false true = (0, false, true, true, false) := by
  decide

/-- SBC shape: `5 - 3` with C set gives 2, carry set. -/
-- Sail: instrs64.sail:194.
theorem addSubFlags_sbc : addSubFlags 64 5 3 true true = (2, false, false, true, false) := by
  decide

/-- Planted wrong case: `10 + 5` is not 14. -/
theorem addSubFlags_wrong : addSubFlags 64 10 5 false false ≠ (14, false, false, false, false) := by
  decide

/-- Read X `n`, or SP when `n = 31` (add/sub immediate and extended forms). -/
-- Sail: instrs64.sail:589,751 (`if n == 31 then SP_read() ...`).
def rdSPorX (n w : Nat) : Eff Nat :=
  if n == 31 then Eff.rdSys "SP" fun v => Eff.ret (v.toNat % pow2 w)
  else rdXn n w

/-- Write X `d`, or SP when `d = 31` without flag update. -/
-- Sail: instrs64.sail:589,751 (`if d == 31 & !setflags then SP_set() ...`).
-- A flag-setting write to 31, or any non-SP form, goes to X (`wrX 31` is XZR).
def wrSPorX (d w v : Nat) (setflags : Bool) : Eff Unit :=
  if d == 31 && !setflags then
    Eff.wrSys "SP" (BitVec.ofNat 64 (v % pow2 w)) (Eff.ret ())
  else wrXn d w v

/-- ADD/ADDS/SUB/SUBS (immediate): `imm` is the decode-built 12-bit value. -/
-- Sail: instrs64.sail:589 (`execute ... add_sub_immediate`).
def execAddSubImm (d n w imm : Nat) (sub setflags : Bool) : Eff Unit := do
  let o1 ← rdSPorX n w
  let (r, nn, z, c, v) := addSubFlags w o1 imm sub sub
  if setflags then do
    let _ ← wrNZCVn (nzcvOf nn z c v)
    wrSPorX d w r true
  else wrSPorX d w r false

/-- ADD/ADDS/SUB/SUBS (shifted register). -/
-- Sail: instrs64.sail:434 (`execute ... add_sub_shiftedreg`).
def execAddSubShift (d n m w : Nat) (st : ShiftTy) (amt : Nat) (sub setflags : Bool) :
    Eff Unit := do
  let o1 ← rdXn n w
  let mraw ← rdXn m w
  let (r, nn, z, c, v) := addSubFlags w o1 (shiftReg w mraw st amt) sub sub
  if setflags then do
    let _ ← wrNZCVn (nzcvOf nn z c v)
    wrXn d w r
  else wrXn d w r

/-- ADD/ADDS/SUB/SUBS (extended register). -/
-- Sail: instrs64.sail:751 (`execute ... add_sub_extendedreg`).
def execAddSubExt (d n m w : Nat) (e : ExtTy) (shift : Nat) (sub setflags : Bool) :
    Eff Unit := do
  let o1 ← rdSPorX n w
  let mraw ← rdXn m w
  let (r, nn, z, c, v) := addSubFlags w o1 (extendReg mraw e shift w) sub sub
  if setflags then do
    let _ ← wrNZCVn (nzcvOf nn z c v)
    wrSPorX d w r true
  else wrSPorX d w r false

/-- ADC/SBC/ADCS/SBCS: carry-in is the live C flag. -/
-- Sail: instrs64.sail:194 (`execute ... add_sub_carry`).
def execAdcSbc (d n m w : Nat) (sub setflags : Bool) : Eff Unit := do
  let o1 ← rdXn n w
  let o2 ← rdXn m w
  let (_, (_, (c0, _))) ← rdNZCVn
  let (r, nn, z, c, v) := addSubFlags w o1 o2 sub c0
  if setflags then do
    let _ ← wrNZCVn (nzcvOf nn z c v)
    wrXn d w r
  else wrXn d w r

/-- Logical ops (Sail `LogicalOp`); `invert` selects the BIC/ORN/BICS shape. -/
-- Sail: instrs64.sail:1391,1757 (`LogicalOp_AND/ORR/EOR`, `invert` from N).
inductive LogicOp where
  | and | orr | eor
  deriving DecidableEq, Repr

/-- Shared core of every logical execute. -/
-- Sail: instrs64.sail:1391 (`execute ... logical_immediate`) and
-- instrs64.sail:1757 (`execute ... logical_shiftedreg`).
def logicPure (w a b : Nat) (invert : Bool) (op : LogicOp) : Nat :=
  let x := a % pow2 w
  let y := if invert then pow2 w - 1 - b % pow2 w else b % pow2 w
  match op with
  | .and => x.land y
  | .orr => x.lor y
  | .eor => x.xor y

/-- NZCV of a logical result: N from the top bit, Z from zero, C and V clear. -/
-- Sail: instrs64.sail:1391 (`(... @ IsZeroBit(result)) @ 0b00`).
def logicNZCV (w r : Nat) : Bool × Bool × Bool × Bool :=
  (decide (pow2 (w - 1) ≤ r % pow2 w), decide (r % pow2 w = 0), false, false)

/-- AND of `0xFF` with mask `0xF` is `0xF`. -/
-- Sail: instrs64.sail:1391.
theorem logicPure_and : logicPure 64 0xFF 0xF false .and = 0xF := by decide

/-- ORN shape (`invert`): `0 | ~0xFF` in 32 bits. -/
-- Sail: instrs64.sail:1757.
theorem logicPure_orn : logicPure 32 0 0xFF true .orr = 0xFFFFFF00 := by decide

/-- EOR of a value with itself is zero. -/
-- Sail: instrs64.sail:1391.
theorem logicPure_eor : logicPure 32 0x12345678 0x12345678 false .eor = 0 := by decide

/-- ANDS writing zero sets Z only. -/
-- Sail: instrs64.sail:1391.
theorem logicNZCV_zero : logicNZCV 32 0 = (false, true, false, false) := by decide

/-- ANDS writing a negative value sets N only. -/
-- Sail: instrs64.sail:1391.
theorem logicNZCV_neg : logicNZCV 32 0x80000000 = (true, false, false, false) := by
  decide

/-- Planted wrong case: `0xFF AND 0xF` is not `0xFF`. -/
theorem logicPure_wrong : logicPure 64 0xFF 0xF false .and ≠ 0xFF := by decide

/-- AND/ORR/EOR/ANDS (immediate): `mask` is the decode-built bitmask. -/
-- Sail: instrs64.sail:1391. Reads X (even `n = 31`); writes SP-or-X.
def execLogicalImm (d n w mask : Nat) (invert : Bool) (op : LogicOp) (setflags : Bool) :
    Eff Unit := do
  let o1 ← rdXn n w
  let r := logicPure w o1 mask invert op
  if setflags then do
    let (nn, z, _, _) := logicNZCV w r
    let _ ← wrNZCVn (nzcvOf nn z false false)
    wrSPorX d w r true
  else wrSPorX d w r false

/-- AND/ORR/EOR/ANDS (shifted register, with BIC/ORN/BICS via `invert`). -/
-- Sail: instrs64.sail:1757. Reads and writes X throughout.
def execLogicalShift (d n m w : Nat) (invert : Bool) (op : LogicOp) (setflags : Bool)
    (st : ShiftTy) (amt : Nat) : Eff Unit := do
  let o1 ← rdXn n w
  let mraw ← rdXn m w
  let r := logicPure w o1 (shiftReg w mraw st amt) invert op
  if setflags then do
    let (nn, z, _, _) := logicNZCV w r
    let _ ← wrNZCVn (nzcvOf nn z false false)
    wrXn d w r
  else wrXn d w r

/-- LSLV/LSRV/ASRV/RORV: shift `Xn` by `Xm mod w`. -/
-- Sail: instrs64.sail:2194 (`execute ... shift_variable`).
def execShiftVar (d n m w : Nat) (st : ShiftTy) : Eff Unit := do
  let v ← rdXn n w
  let s ← rdXn m w
  wrXn d w (shiftReg w v st (s % w))

/-- LSLV shape: `1 LSL (65 mod 64 = 1)` is 2. -/
-- Sail: instrs64.sail:2194.
theorem shiftVar_lslv : shiftReg 64 1 .lsl (65 % 64) = 2 := by decide

/-- RORV shape: `ROR #8` of `0x12345678`. -/
-- Sail: instrs64.sail:2194.
theorem shiftVar_rorv : shiftReg 32 0x12345678 .ror (8 % 32) = 0x78123456 := by
  decide

/-- Planted wrong case: the masked amount matters, `65 mod 64` is not 65. -/
theorem shiftVar_wrong : shiftReg 64 1 .lsl (65 % 64) ≠ 1 := by decide

/-- Movewide ops (Sail `MoveWideOp`): N = NOT, Z = zero, K = keep. -/
-- Sail: instrs64.sail:38723 (`MoveWideOp_N/Z/K`; opc `01` is UNDEFINED at decode).
inductive MovKind where
  | n | z | k
  deriving DecidableEq, Repr

/-- Shared core of MOVZ/MOVN/MOVK: place `imm` at `pos`, keep or clear the rest. -/
-- Sail: instrs64.sail:38723 (`execute ... insert_movewide`).
def movWidePure (w old imm : Nat) (mk : MovKind) (pos : Nat) : Nat :=
  let base := match mk with | .k => old % pow2 w | _ => 0
  let cleared := base - base / pow2 pos % pow2 16 * pow2 pos
  let r := cleared + (imm % pow2 16) * pow2 pos
  match mk with | .n => pow2 w - 1 - r | _ => r

/-- `MOVZ W0, #0x1234, LSL #16` writes `0x12340000`. -/
-- Sail: instrs64.sail:38723.
theorem movWidePure_z : movWidePure 32 0 0x1234 .z 16 = 0x12340000 := by decide

/-- `MOVN X0, #0xFFFF` writes `0xFFFFFFFFFFFF0000`. -/
-- Sail: instrs64.sail:38723.
theorem movWidePure_n : movWidePure 64 0 0xFFFF .n 0 = 0xFFFFFFFFFFFF0000 := by
  decide

/-- `MOVK` keeps the other three halfwords. -/
-- Sail: instrs64.sail:38723.
theorem movWidePure_k : movWidePure 32 0xAAAABBBB 0x1234 .k 0 = 0xAAAABBBB - 0xBBBB + 0x1234 := by
  decide

/-- Planted wrong case: MOVZ clears the upper halfword. -/
theorem movWidePure_wrong : movWidePure 32 0xFFFFFFFF 0x1234 .z 0 ≠ 0xFFFFFFFF := by
  decide

/-- MOVZ/MOVN/MOVK: `pos` is the decode-built `hw * 16`, `imm` the 16-bit field. -/
-- Sail: instrs64.sail:38723. Always writes X (even `d = 31`).
def execMovWide (d w imm : Nat) (mk : MovKind) (pos : Nat) : Eff Unit := do
  let old ← rdXn d w
  wrXn d w (movWidePure w old imm mk pos)

/-- ADR/ADRP core: `base` is PC (page-aligned for ADRP) plus the signed,
    decode-extended offset `imm` (already `mod 2 ^ 64`), wrapped to 64 bits. -/
-- Sail: instrs64.sail:1220 (`execute ... address_pc_rel`).
def adrPure (pc imm : Nat) (page : Bool) : Nat :=
  let base := if page then pc % pow2 64 - pc % pow2 64 % pow2 12 else pc % pow2 64
  (base + imm % pow2 64) % pow2 64

/-- `ADR X0, #8` at `0x1000` gives `0x1008`. -/
-- Sail: instrs64.sail:1220.
theorem adrPure_adr : adrPure 0x1000 8 false = 0x1008 := by decide

/-- `ADRP X0, #0x1000` at `0x1234` clears the page then adds. -/
-- Sail: instrs64.sail:1220.
theorem adrPure_adrp : adrPure 0x1234 0x1000 true = 0x2000 := by decide

/-- Planted wrong case: ADRP aligns the base first. -/
theorem adrPure_wrong : adrPure 0x1234 0x1000 true ≠ 0x2234 := by decide

/-- ADR/ADRP: `imm` is the decode-built (sign-extended, shifted) offset. -/
-- Sail: instrs64.sail:1220.
def execAdr (d : Nat) (imm : Nat) (page : Bool) : Eff Unit := do
  let pc ← Eff.rdPC fun v => Eff.ret v.toNat
  wrXn d 64 (adrPure pc imm page)

end Arm.Int

/-
CUTS: general-purpose execute (arithmetic, logical, variable shifts, movewide,
ADR/ADRP). Bitfield/extract, counts, multiply/divide and conditional families
live in `IntBit.lean`, `IntMul.lean`, `IntCond.lean` (open). The `Eff` wrappers
are unproved plumbing over `decide`-checked cores. SP is named `"SP"` in
`rdSys`/`wrSys`; `wrX 31` is the XZR discard and `rdX 31` reads zero.
-/

