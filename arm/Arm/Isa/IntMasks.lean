/-
  File:      Arm/Isa/IntMasks.lean
  Subject:   Sail `DecodeBitMasks` over Nats: the immediate/mask decoder shared
             by logical-immediate and bitfield instructions. `none` is a refused
             (UNDEFINED) encoding, never a silent default.
  Sail:      sail-arm/arm-v9.4-a/src/v8_base.sail:30895.
-/
import Arm.Isa.IntCore

namespace Arm.Int

/-- Floor of log2 for `v > 0`; 0 at `v = 0` (Sail `HighestSetBit` is -1 there,
    and both are below 1, so both refuse in `decodeBitMasks`). -/
-- Sail: builtins.sail:152 (`HighestSetBit`: top-down bit search).
def hbitGo (v : Nat) : Nat → Nat → Nat
  | 0, best => best
  | (f+1), best =>
    let k := v - f
    hbitGo v f (if pow2 k ≤ v then k else best)

def hbit (v : Nat) : Nat := hbitGo v (v + 1) 0

/-- `hbit 127 = 6`. -/
-- Sail: builtins.sail:152.
theorem hbit_ex : hbit 127 = 6 := by decide

/-- `hbit 1 = 0`, below the valid length. -/
-- Sail: builtins.sail:152.
theorem hbit_one : hbit 1 = 0 := by decide

/-- Replicate an `esize`-bit chunk `reps` times (Sail `Replicate`). -/
-- Sail: prelude.sail:151 (`Replicate__1`).
def repGo (chunk esize : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | (k+1), acc => repGo chunk esize k (acc * pow2 esize + chunk)

def replicateChunk (chunk esize reps : Nat) : Nat := repGo chunk esize reps 0

/-- Four copies of `0xFF` make `0xFFFFFFFF`. -/
-- Sail: prelude.sail:151.
theorem replicateChunk_ex : replicateChunk 0xFF 8 4 = 0xFFFFFFFF := by decide

/-- Planted wrong case: three copies are not four. -/
theorem replicateChunk_wrong : replicateChunk 0xFF 8 3 ≠ 0xFFFFFFFF := by decide

/-- Sail `DecodeBitMasks(immN, imms, immr, immediate, M)`.
    `none` = UNDEFINED encoding (refused). Otherwise the `(wmask, tmask)` pair. -/
-- Sail: v8_base.sail:30895. `M` is 32 or 64.
def decodeBitMasks (immN imms immr : Nat) (immediate : Bool) (m : Nat) :
    Option (Nat × Nat) :=
  let v7 := (immN % 2) * 64 + (63 - imms % 64)
  let len := hbit v7
  if len < 1 then none
  else
    let esize := pow2 len
    if m < esize then none
    else
      let levels := esize - 1
      if immediate && (imms % 64).land levels == levels then none
      else
        let s := (imms % 64).land levels
        let r := (immr % 64).land levels
        let d := (s + esize - r) % esize
        let welem := pow2 (s + 1) - 1
        let telem := pow2 (d + 1) - 1
        let reps := m / esize
        some (replicateChunk (rorW esize welem r) esize reps,
              replicateChunk telem esize reps)

/-- `AND Xd, Xn, #1` mask: N=1, imms=0, immr=0 gives `(1, 1)`. -/
-- Sail: v8_base.sail:30895.
theorem decodeBitMasks_one : decodeBitMasks 1 0 0 true 64 = some (1, 1) := by
  decide

/-- 32-bit all-levels imms is UNDEFINED for an immediate. -/
-- Sail: v8_base.sail:30895 (`immediate & (imms & levels) == levels`).
theorem decodeBitMasks_reserved : decodeBitMasks 0 31 0 true 32 = none := by
  decide

/-- Same fields as a bitfield (non-immediate) give full masks. -/
-- Sail: v8_base.sail:30895.
theorem decodeBitMasks_bitfield :
    decodeBitMasks 0 31 0 false 32 = some (0xFFFFFFFF, 0xFFFFFFFF) := by
  decide

/-- Bitfield shape imms=7, immr=2: rotated `wmask`, small `tmask`. -/
-- Sail: v8_base.sail:30895.
theorem decodeBitMasks_rot :
    decodeBitMasks 0 7 2 false 32 = some (0xC000003F, 0x3F) := by
  decide

/-- Planted wrong case: the `#1` mask is not `(2, 1)`. -/
theorem decodeBitMasks_wrong : decodeBitMasks 1 0 0 true 64 ≠ some (2, 1) := by
  decide

end Arm.Int

#print axioms Arm.Int.decodeBitMasks_one
#print axioms Arm.Int.decodeBitMasks_reserved
#print axioms Arm.Int.decodeBitMasks_rot
#print axioms Arm.Int.hbit_ex

/-
CUTS: `DecodeBitMasks` only. Logical-immediate and bitfield execute functions
are open (in `Integer.lean`). `m < esize` refusal is unreachable from valid
decodes and kept as `none` for totality.
-/
