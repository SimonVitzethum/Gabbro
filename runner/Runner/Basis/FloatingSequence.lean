module
public import Runner.Basis.Res
@[expose] public section

namespace Runner

/-! Portable request composition for conversions that SSE2 does not implement
    with one instruction. The executable backend remains the assembly runner;
    these are its IR request trees, never a Lean execution fallback. -/

def FPFormat.scalarBits : FPFormat → W → W
  | .f32, value => fpLow32 value
  | .f64, value => value

def FPFormat.signBit : FPFormat → W
  | .f32 => 0x80000000
  | .f64 => 0x8000000000000000

def FPFormat.infinityBits : FPFormat → W
  | .f32 => 0x7F800000
  | .f64 => 0x7FF0000000000000

/-- The positive, exactly representable floating value 2^63. -/
def FPFormat.int64Limit : FPFormat → W
  | .f32 => 0x5F000000
  | .f64 => 0x43E0000000000000

/-- The positive, exactly representable floating value 2^64. -/
def FPFormat.uint64Limit : FPFormat → W
  | .f32 => 0x5F800000
  | .f64 => 0x43F0000000000000

def fpMagnitude (format : FPFormat) (value : W) : W :=
  format.scalarBits value &&& ~~~format.signBit

def fpNegative (format : FPFormat) (value : W) : Bool :=
  (format.scalarBits value &&& format.signBit) != 0

def fpNaN (format : FPFormat) (value : W) : Bool :=
  format.infinityBits.ult (fpMagnitude format value)

def fpFiniteWord : FPFormat → W → W
  | .f32, value => flagWord ((UInt32.ofBitVec (value.setWidth 32) &&& 0x7F800000) != 0x7F800000)
  | .f64, value => flagWord ((UInt64.ofBitVec value &&& 0x7FF0000000000000) != 0x7FF0000000000000)

/-- Retain the discarded low bit before the signed native conversion. -/
def uint64StickyHalf (value : W) : W := (value >>> 1) ||| (value &&& 1)

def fpFromUInt64 {σ : Type} (format : FPFormat) (value : W) (continuation : W → Res σ) : Res σ :=
  if value.msb then
    fp (.fromInt64 format) (uint64StickyHalf value) 0 fun half =>
      fp (.add format) half half continuation
  else fp (.fromInt64 format) value 0 continuation

/-- CVTT's integer-indefinite result is used only on its actual finite domain.
    Outside that domain, the guards produce Std's saturated/NaN-to-zero result. -/
def fpToInt64 {σ : Type} (format : FPFormat) (value : W) (continuation : W → Res σ) : Res σ :=
  if fpNaN format value then continuation 0
  else if (fpMagnitude format value).ult format.int64Limit then
    fp (.truncateInt64 format) value 0 continuation
  else continuation (if fpNegative format value then 0x8000000000000000 else 0x7FFFFFFFFFFFFFFF)

def fpToUInt64 {σ : Type} (format : FPFormat) (value : W) (continuation : W → Res σ) : Res σ :=
  if fpNaN format value || fpNegative format value then continuation 0
  else if (fpMagnitude format value).ult format.uint64Limit then
    if (fpMagnitude format value).ult format.int64Limit then
      fp (.truncateInt64 format) value 0 continuation
    else fp (.sub format) value format.int64Limit fun reduced =>
      fp (.truncateInt64 format) reduced 0 fun integer => continuation (integer ||| 0x8000000000000000)
  else continuation 0xFFFFFFFFFFFFFFFF

/-- Installed codecs compute words directly. Unsigned conversion and saturating
    casts use their proven portable sequences of native primitive requests. -/
def fpSequence {σ : Type} (kind : NativeFPOp) (a b : W) (continuation : W → Res σ) : Res σ :=
  match kind with
  | .neg format => continuation (fpNegWord format a)
  | .isFinite format => continuation (fpFiniteWord format a)
  | .fromUInt64 format => fpFromUInt64 format a continuation
  | .toInt64 format => fpToInt64 format a continuation
  | .toUInt64 format => fpToUInt64 format a continuation
  | _ => fp kind a b continuation

theorem fpSequence_direct {σ : Type} (kind : NativeFPOp) (a b : W) (continuation : W → Res σ)
    (h : kind.direct = true) : fpSequence kind a b continuation = fp kind a b continuation := by
  cases kind <;> first
    | rfl
    | (rename_i format; cases format <;> cases h)

end Runner
