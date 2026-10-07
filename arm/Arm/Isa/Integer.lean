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

end Arm.Int

/-
CUTS: arithmetic execute only (immediate, shifted, extended, carry).
Logical, movewide, ADR/ADRP and all later families are open.
The `Eff` wrappers are unproved plumbing over `decide`-checked cores.
-/
