/-
  File:      Arm/Isa/IntMul.lean
  Subject:   Execute-level semantics of MUL/MADD/MSUB, the widening
             SMADDL/UMADDL/SMSUBL/UMSUBL, UDIV/SDIV and UMULH/SMULH.
             A zero divisor yields zero (as the source says); the SMULH/UMULH
             `Ra == 11111` gate is CONSTRAINED UNPREDICTABLE at decode
             (agent 15) since `Ra` never reaches the execute clause.
  Sail:      sail-arm/arm-v9.4-a/src/instrs64.sail (`execute` clauses).
-/
import Arm.Isa.IntCore

namespace Arm.Int

/-- MADD/MSUB core: `a + n * m` resp. `a - n * m`, truncated to `w` bits.
    MUL is MADD with `a = XZR`. -/
-- Sail: instrs64.sail:38462 (`execute ... mul_uniform_add_sub`).
def mulAddSubPure (w a n m : Nat) (sub : Bool) : Nat :=
  let p := (n % pow2 w) * (m % pow2 w)
  if sub then ((a % pow2 w) + pow2 w - p % pow2 w) % pow2 w
  else ((a % pow2 w) + p) % pow2 w

/-- `MADD X0, X1=3, X2=4, X3=5` gives 17. -/
-- Sail: instrs64.sail:38462.
theorem mulAddSubPure_madd : mulAddSubPure 64 5 3 4 false = 17 := by decide

/-- `MSUB X0, X1=3, X2=4, X3=5` gives `5 - 12` wrapped to 64 bits. -/
-- Sail: instrs64.sail:38462.
theorem mulAddSubPure_msub : mulAddSubPure 64 5 3 4 true = 0xFFFFFFFFFFFFFFF9 := by
  decide

/-- `MUL X0, X1=3, X2=4` (MADD with XZR) gives 12. -/
-- Sail: instrs64.sail:38462.
theorem mulAddSubPure_mul : mulAddSubPure 32 0 3 4 false = 12 := by decide

/-- Planted wrong case: `5 + 3 * 4` is not 32. -/
theorem mulAddSubPure_wrong : mulAddSubPure 64 5 3 4 false ≠ 32 := by decide

/-- MUL/MADD/MSUB. -/
-- Sail: instrs64.sail:38462.
def execMulAddSub (a d m n w : Nat) (sub : Bool) : Eff Unit := do
  let o1 ← rdXn n w
  let o2 ← rdXn m w
  let o3 ← rdXn a w
  wrXn d w (mulAddSubPure w o3 o1 o2 sub)

/-- Widening 32x32+64 core (SMADDL/UMADDL/SMSUBL/UMSUBL). -/
-- Sail: instrs64.sail:44954 (`execute ... mul_widening_32_64`).
def wideMulPure (a n m : Nat) (sub isUnsigned : Bool) : Nat :=
  let sn : Int := if isUnsigned then (n % pow2 32 : Int) else sintOf 32 (n % pow2 32)
  let sm : Int := if isUnsigned then (m % pow2 32 : Int) else sintOf 32 (m % pow2 32)
  let base : Int := (a % pow2 64 : Int)
  let r := if sub then base - sn * sm else base + sn * sm
  (r % (pow2 64 : Int)).toNat

/-- `SMADDL X0, W1=-1, W2=2, X3=10` gives 8. -/
-- Sail: instrs64.sail:44954.
theorem wideMulPure_s : wideMulPure 10 0xFFFFFFFF 2 false false = 8 := by decide

/-- `UMADDL` with the same fields stays unsigned: `4294967295 * 2 + 10`. -/
-- Sail: instrs64.sail:44954.
theorem wideMulPure_u : wideMulPure 10 0xFFFFFFFF 2 false true = 8589934600 := by
  decide

/-- Planted wrong case: signed and unsigned differ on `0xFFFFFFFF`. -/
theorem wideMulPure_wrong : wideMulPure 10 0xFFFFFFFF 2 false false ≠ 8589934600 := by
  decide

/-- SMADDL/UMADDL/SMSUBL/UMSUBL: destination is always 64 bits. -/
-- Sail: instrs64.sail:44954 (`X_set(d, 64)`).
def execWideMul (a d m n : Nat) (sub isUnsigned : Bool) : Eff Unit := do
  let o1 ← rdXn n 32
  let o2 ← rdXn m 32
  let o3 ← rdXn a 64
  wrXn d 64 (wideMulPure o3 o1 o2 sub isUnsigned)

/-- UDIV/SDIV core. A zero divisor yields zero (the source defines this, no
    trap); signed division truncates toward zero and wraps on overflow. -/
-- Sail: instrs64.sail:42722 (`execute ... div`).
def divPure (w n m : Nat) (isUnsigned : Bool) : Nat :=
  let d := m % pow2 w
  if d == 0 then 0
  else if isUnsigned then (n % pow2 w) / d
  else ((sintOf w (n % pow2 w)).tdiv (sintOf w d) % (pow2 w : Int)).toNat

/-- `UDIV 7 / 2` is 3. -/
-- Sail: instrs64.sail:42722.
theorem divPure_u : divPure 32 7 2 true = 3 := by decide

/-- `SDIV -7 / 2` truncates toward zero: `-3` as `0xFFFFFFFD`. -/
-- Sail: instrs64.sail:42722.
theorem divPure_s : divPure 32 0xFFFFFFF9 2 false = 0xFFFFFFFD := by decide

/-- Division by zero yields zero (defined behaviour, not a trap). -/
-- Sail: instrs64.sail:42722 (`if IsZero(operand2) then result = 0`).
theorem divPure_zero : divPure 32 7 0 true = 0 := by decide

/-- `SDIV INT_MIN / -1` wraps to INT_MIN. -/
-- Sail: instrs64.sail:42722 (slicing `result[datasize-1..0]`).
theorem divPure_ovf : divPure 32 0x80000000 0xFFFFFFFF false = 0x80000000 := by
  decide

/-- Planted wrong case: `UDIV 7 / 2` is not 4. -/
theorem divPure_wrong : divPure 32 7 2 true ≠ 4 := by decide

/-- UDIV/SDIV. -/
-- Sail: instrs64.sail:42722.
def execDiv (d m n w : Nat) (isUnsigned : Bool) : Eff Unit := do
  let o1 ← rdXn n w
  let o2 ← rdXn m w
  wrXn d w (divPure w o1 o2 isUnsigned)

/-- UMULH/SMULH core: bits `[2w-1..w]` of the full product. -/
-- Sail: instrs64.sail:46194 (`execute ... mul_widening_64_128hi`).
def mulHiPure (w n m : Nat) (isUnsigned : Bool) : Nat :=
  if isUnsigned then
    (n % pow2 w * (m % pow2 w)) / pow2 w % pow2 w
  else
    let p := sintOf w (n % pow2 w) * sintOf w (m % pow2 w)
    ((p % (pow2 (2 * w) : Int)) / (pow2 w : Int)).toNat

/-- `UMULH(2^63, 2)`: the full `2^64` product surfaces as high half 1. -/
-- Sail: instrs64.sail:46194.
theorem mulHiPure_u : mulHiPure 64 0x8000000000000000 2 true = 1 := by decide

/-- `SMULH(-1, -1)`: product 1, high half 0. -/
-- Sail: instrs64.sail:46194.
theorem mulHiPure_s : mulHiPure 64 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF false = 0 := by
  decide

/-- `SMULH(INT_MIN, 2)`: high half of `-2^64` is all ones. -/
-- Sail: instrs64.sail:46194.
theorem mulHiPure_sneg : mulHiPure 64 0x8000000000000000 2 false = 0xFFFFFFFFFFFFFFFF := by
  decide

/-- Planted wrong case: the high half is not the low half. -/
theorem mulHiPure_wrong : mulHiPure 64 0x8000000000000000 2 true ≠ 0 := by decide

/-- UMULH/SMULH: destination is always 64 bits. -/
-- Sail: instrs64.sail:46194 (`X_set(d, 64) = result[127..64]`).
def execMulHi (d m n w : Nat) (isUnsigned : Bool) : Eff Unit := do
  let o1 ← rdXn n w
  let o2 ← rdXn m w
  wrXn d 64 (mulHiPure w o1 o2 isUnsigned)

end Arm.Int

#print axioms Arm.Int.mulAddSubPure_msub
#print axioms Arm.Int.wideMulPure_s
#print axioms Arm.Int.divPure_s
#print axioms Arm.Int.mulHiPure_sneg

/-
CUTS: multiply/divide executes only. The conditional family is open
(`IntCond.lean`). Division by zero is defined (yields zero) per the source;
the SMULH/UMULH `Ra` gate is decode-side CONSTRAINED UNPREDICTABLE. The `Eff`
wrappers are unproved plumbing over `decide`-checked cores.
-/
