/-
  File:      Arm/Isa/IntBit.lean
  Subject:   Execute-level semantics of bitfield moves (SBFM/UBFM/BFM), EXTR
             (also the ROR-immediate alias), CLZ/CLS, RBIT, REV and the
             CSSC-gated CNT/CTZ/ABS. Decoded fields in, `Eff Unit` out.
  Sail:      sail-arm/arm-v9.4-a/src/instrs64.sail (`execute` clauses).
-/
import Arm.Isa.IntCore
import Arm.Isa.IntMasks

namespace Arm.Int

/-- `a AND (NOT m)` inside `w` bits. -/
def andNotW (w a m : Nat) : Nat :=
  (a % pow2 w).xor ((a % pow2 w).land (m % pow2 w))

/-- `a OR b` inside `w` bits. -/
def orW (w a b : Nat) : Nat := (a % pow2 w).lor (b % pow2 w)

/-- Shared core of SBFM/UBFM/BFM. `extend` selects sign extension (S),
    `inzero` selects a zero base (U: UBFM and SBFM set it, BFM keeps Rd). -/
-- Sail: instrs64.sail:2917 (`execute ... bitfield`). `r`/`s` are the raw
-- field values, `wmask`/`tmask` the `DecodeBitMasks` pair.
def bitfieldPure (w dst src r s wmask tmask : Nat) (extend inzero : Bool) : Nat :=
  let d := if inzero then 0 else dst % pow2 w
  let x := src % pow2 w
  let wm := wmask % pow2 w
  let tm := tmask % pow2 w
  let bot := orW w (andNotW w d wm) ((rorW w x r).land wm)
  let top := if extend then (if (x / pow2 s) % 2 == 1 then pow2 w - 1 else 0) else d
  orW w (andNotW w top tm) (bot.land tm)

/-- UBFM extracting bits [7..2]: masks from `decodeBitMasks_rot` give `0x3F`. -/
-- Sail: instrs64.sail:2917.
theorem bitfieldPure_ubfm :
    bitfieldPure 32 0 0xFFFFFFFF 2 7 0xC000003F 0x3F false true = 0x3F := by
  decide

/-- SBFM as SXTB: `0xFF` sign-extends to `0xFFFFFFFF`. -/
-- Sail: instrs64.sail:2917.
theorem bitfieldPure_sbfm :
    bitfieldPure 32 0 0xFF 0 7 0xFF 0xFF true true = 0xFFFFFFFF := by
  decide

/-- BFM inserting a low byte keeps the destination elsewhere. -/
-- Sail: instrs64.sail:2917.
theorem bitfieldPure_bfm :
    bitfieldPure 32 0xFFFF0000 0xAB 0 7 0xFF 0xFF false false = 0xFFFF00AB := by
  decide

/-- Planted wrong case: UBFM extracts, it does not keep the whole word. -/
theorem bitfieldPure_wrong :
    bitfieldPure 32 0 0xFFFFFFFF 2 7 0xC000003F 0x3F false true ≠ 0xFFFFFFFF := by
  decide

/-- SBFM/UBFM/BFM: `opc == 0b11` is UNDEFINED at decode (agent 15), so the
    two bools below are already validated there. -/
-- Sail: instrs64.sail `decode_bfm...` (`0b00` SBFM, `0b01` BFM, `0b10` UBFM).
def execBitfield (d n w r s wmask tmask : Nat) (extend inzero : Bool) : Eff Unit := do
  let dst ← rdXn d w
  let src ← rdXn n w
  wrXn d w (bitfieldPure w dst src r s wmask tmask extend inzero)

/-- EXTR core: slice `w` bits at `lsb` out of `Xn:M` concatenated. -/
-- Sail: instrs64.sail:10728 (`execute ... extract_immediate`).
def extractPure (w n m lsb : Nat) : Nat :=
  (n % pow2 w * pow2 w + m % pow2 w) / pow2 lsb % pow2 w

/-- EXTR shifting the join of `0x12` and `0x34` by a byte. -/
-- Sail: instrs64.sail:10728.
theorem extractPure_ex : extractPure 64 0x12 0x34 8 = 0x1200000000000000 := by
  decide

/-- ROR-immediate alias: EXTR with `n = m` rotates. -/
-- Sail: instrs64.sail:10728 (ROR is an EXTR alias at decode).
theorem extractPure_ror : extractPure 32 0x12345678 0x12345678 8 = 0x78123456 := by
  decide

/-- Planted wrong case: extraction shifts, it does not concatenate raw. -/
theorem extractPure_wrong : extractPure 64 0x12 0x34 8 ≠ 0x1234 := by decide

/-- EXTR (and the ROR-immediate alias). -/
-- Sail: instrs64.sail:10728.
def execExtract (d n m w lsb : Nat) : Eff Unit := do
  let o1 ← rdXn n w
  let o2 ← rdXn m w
  wrXn d w (extractPure w o1 o2 lsb)

/-- CLZ/CLS. -/
-- Sail: instrs64.sail:6893 (`execute ... cnt`, `CountOp_CLZ/CLS`).
def execClzCls (d n w : Nat) (isCls : Bool) : Eff Unit := do
  let v ← rdXn n w
  wrXn d w (if isCls then clsW w v else clzW w v)

/-- RBIT. -/
-- Sail: instrs64.sail:40012 (`execute ... rbit`).
def execRbit (d n w : Nat) : Eff Unit := do
  let v ← rdXn n w
  wrXn d w (rbitW w v)

/-- REV/REV16/REV32/REV64: `cont` is the decode-built container size
    (16, 32 or 64); `opc == 0b00` is UNREACHABLE at decode (agent 15). -/
-- Sail: instrs64.sail:41052 (`execute ... rev`).
def execRev (d n w cont : Nat) : Eff Unit := do
  let v ← rdXn n w
  wrXn d w (revW w cont v)

/-- CTZ core: trailing-zero count via reversal (Sail's definition). -/
-- Sail: instrs64.sail:10179 (`CountLeadingZeroBits(BitReverse(operand1))`).
def ctzPure (w v : Nat) : Nat := clzW w (rbitW w (v % pow2 w))

/-- `CTZ(8)` is 3. -/
-- Sail: instrs64.sail:10179.
theorem ctzPure_ex : ctzPure 32 8 = 3 := by decide

/-- `CTZ(0)` is `w`. -/
-- Sail: instrs64.sail:10179.
theorem ctzPure_zero : ctzPure 32 0 = 32 := by decide

/-- Planted wrong case: `CTZ(8)` is not 8. -/
theorem ctzPure_wrong : ctzPure 32 8 ≠ 8 := by decide

/-- CNT (population count), CTZ and ABS are CSSC-gated at decode
    (`if !HaveCSSC() then Undefined`, agent 15); the executes below are total. -/
-- Sail: instrs64.sail:7771 (CNT), instrs64.sail:10179 (CTZ), instrs64.sail:41 (ABS).
def execCntPop (d n w : Nat) : Eff Unit := do
  let v ← rdXn n w
  wrXn d w (popW w v)

def execCtz (d n w : Nat) : Eff Unit := do
  let v ← rdXn n w
  wrXn d w (ctzPure w v)

def execAbs (d n w : Nat) : Eff Unit := do
  let v ← rdXn n w
  wrXn d w (absW w v)

end Arm.Int

/-
CUTS: bitfield/extract/count executes only. Multiply/divide and conditional
families are open (`IntMul.lean`, `IntCond.lean`). The CSSC feature gate and
the BFM `opc` / REV `opc` refusals are decode-side (agent 15). The `Eff`
wrappers are unproved plumbing over `decide`-checked cores.
-/
