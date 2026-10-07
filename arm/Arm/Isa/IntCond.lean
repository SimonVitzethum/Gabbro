/-
  File:      Arm/Isa/IntCond.lean
  Subject:   Execute-level semantics of CSEL/CSINC/CSINV/CSNEG and
             CCMP/CCMN (register and immediate). Only the selected register
             is read; NZCV is always written by the compares.
  Sail:      sail-arm/arm-v9.4-a/src/instrs64.sail (`execute` clauses).
-/
import Arm.Isa.IntCore
import Arm.Isa.Integer

namespace Arm.Int

/-- Conditional-select core. `(elseInc, elseInv)` picks the shape:
    CSEL (F,F), CSINC (T,F), CSINV (F,T), CSNEG (T,T). -/
-- Sail: instrs64.sail:10051 (`execute ... conditional_select`).
def condSelectPure (w n m : Nat) (holds elseInc elseInv : Bool) : Nat :=
  if holds then n % pow2 w
  else
    let y := if elseInv then pow2 w - 1 - m % pow2 w else m % pow2 w
    if elseInc then (y + 1) % pow2 w else y

/-- CSEL taken returns `Xn`. -/
-- Sail: instrs64.sail:10051.
theorem condSelectPure_csel : condSelectPure 64 10 20 true false false = 10 := by
  decide

/-- CSINC not taken returns `Xm + 1`. -/
-- Sail: instrs64.sail:10051.
theorem condSelectPure_csinc : condSelectPure 32 10 20 false true false = 21 := by
  decide

/-- CSINV not taken returns `~Xm` in 32 bits. -/
-- Sail: instrs64.sail:10051.
theorem condSelectPure_csinv : condSelectPure 32 10 20 false false true = 0xFFFFFFEB := by
  decide

/-- CSNEG not taken returns `-Xm` in 32 bits. -/
-- Sail: instrs64.sail:10051.
theorem condSelectPure_csneg : condSelectPure 32 10 20 false true true = 0xFFFFFFEC := by
  decide

/-- Planted wrong case: CSINC adds one, it does not return `Xm`. -/
theorem condSelectPure_wrong : condSelectPure 32 10 20 false true false ≠ 20 := by
  decide

/-- CSEL/CSINC/CSINV/CSNEG: only the selected register is read. -/
-- Sail: instrs64.sail:10051.
def execCondSelect (d m n w cond : Nat) (elseInc elseInv : Bool) : Eff Unit :=
  Eff.rdNZCV fun f => do
    let holds := condHolds (f.toNat % 16) cond
    if holds then do
      let v ← rdXn n w
      wrXn d w (condSelectPure w v 0 true elseInc elseInv)
    else do
      let v ← rdXn m w
      wrXn d w (condSelectPure w 0 v false elseInc elseInv)

/-- Conditional-compare core: `AddWithCarry` flags when taken, else the
    decode-supplied default flags `dflt`. -/
-- Sail: instrs64.sail:6628 (register) and instrs64.sail:6704 (immediate).
def condCmpPure (w o1 o2 : Nat) (sub holds : Bool) (dflt : Nat) : Nat :=
  if holds then
    let (_, n, z, c, v) := addSubFlags w o1 o2 sub sub
    nzcvOf n z c v
  else dflt % 16

/-- CCMP taken on `5 == 5`: Z and C set, packed as 6. -/
-- Sail: instrs64.sail:6628.
theorem condCmpPure_taken : condCmpPure 64 5 5 true true 0 = 6 := by decide

/-- CCMN taken on `3 + 4`: no flag set, packed as 0. -/
-- Sail: instrs64.sail:6628.
theorem condCmpPure_add : condCmpPure 64 3 4 false true 0 = 0 := by decide

/-- Not taken: the default flags pass through untouched. -/
-- Sail: instrs64.sail:6704.
theorem condCmpPure_skip : condCmpPure 64 5 5 true false 7 = 7 := by decide

/-- Planted wrong case: `5 == 5` sets flags, it does not keep zero. -/
theorem condCmpPure_wrong : condCmpPure 64 5 5 true true 0 ≠ 0 := by decide

/-- CCMP/CCMN (register): `Rm` is read only when the condition holds. -/
-- Sail: instrs64.sail:6628.
def execCondCmpReg (n m w cond dflt : Nat) (sub : Bool) : Eff Unit :=
  Eff.rdNZCV fun f => do
    if condHolds (f.toNat % 16) cond then do
      let o1 ← rdXn n w
      let o2 ← rdXn m w
      wrNZCVn (condCmpPure w o1 o2 sub true (dflt % 16))
    else wrNZCVn (dflt % 16)

/-- CCMP/CCMN (immediate): `imm` is the zero-extended 5-bit field. -/
-- Sail: instrs64.sail:6704.
def execCondCmpImm (n w imm cond dflt : Nat) (sub : Bool) : Eff Unit :=
  Eff.rdNZCV fun f => do
    if condHolds (f.toNat % 16) cond then do
      let o1 ← rdXn n w
      wrNZCVn (condCmpPure w o1 imm sub true (dflt % 16))
    else wrNZCVn (dflt % 16)

end Arm.Int

/-
CUTS: conditional executes only. All families of the agent-11 task are now
covered: arithmetic (Integer), bitfield/extract/counts (IntBit),
multiply/divide (IntMul), conditionals (this file), over IntCore + IntMasks.
The `Eff` wrappers are unproved plumbing over `decide`-checked cores; no
`Eff`-level test interpreter exists yet (bridge/decoder agents' business).
-/
