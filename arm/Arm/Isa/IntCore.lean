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

end Arm.Int

/-
CUTS: skeleton only. No helper proved yet; `addWithCarry`, shifts, extend,
`DecodeBitMasks` and all instruction semantics are open.
-/
