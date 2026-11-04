module

public import Runner.Basis.Mem
public import Init.Data.Float
public import Init.Data.SInt.Float
public import Init.Data.SInt.Float32

@[expose] public section

namespace Runner

inductive FPFormat where
  | f32 | f64
  deriving DecidableEq, Repr

/-- Operations of the existing runner, evaluated by Lean's native CPU primitives.
    Float-to-integer conversions use the primitives' saturating, NaN-to-zero semantics. -/
inductive NativeFPOp where
  | add (format : FPFormat) | sub (format : FPFormat)
  | mul (format : FPFormat) | div (format : FPFormat)
  | neg (format : FPFormat)
  | eq (format : FPFormat) | lt (format : FPFormat) | le (format : FPFormat)
  | isFinite (format : FPFormat)
  | fromInt64 (format : FPFormat) | fromUInt64 (format : FPFormat)
  | toInt64 (format : FPFormat) | toUInt64 (format : FPFormat)
  | widen32 | narrow32
  deriving DecidableEq, Repr

def readFloat (word : W) : Float := Float.ofBits (UInt64.ofBitVec word)
def readFloat32 (word : W) : Float32 := Float32.ofBits (UInt32.ofBitVec (word.setWidth 32))

/-- A native result before its storage representation is chosen. -/
inductive NativeFPValue where
  | f32 (value : Float32)
  | f64 (value : Float)
  | word (value : W)

private def flagWord (value : Bool) : W := if value then 1 else 0

/-- One common evaluator; no runner-owned floating-point arithmetic or interpreter. -/
def nativeFP (op : NativeFPOp) (a b : W) : NativeFPValue :=
  match op with
  | .add .f32 => .f32 (readFloat32 a + readFloat32 b)
  | .add .f64 => .f64 (readFloat a + readFloat b)
  | .sub .f32 => .f32 (readFloat32 a - readFloat32 b)
  | .sub .f64 => .f64 (readFloat a - readFloat b)
  | .mul .f32 => .f32 (readFloat32 a * readFloat32 b)
  | .mul .f64 => .f64 (readFloat a * readFloat b)
  | .div .f32 => .f32 (readFloat32 a / readFloat32 b)
  | .div .f64 => .f64 (readFloat a / readFloat b)
  | .neg .f32 => .f32 (-readFloat32 a)
  | .neg .f64 => .f64 (-readFloat a)
  | .eq .f32 => .word (flagWord (readFloat32 a == readFloat32 b))
  | .eq .f64 => .word (flagWord (readFloat a == readFloat b))
  | .lt .f32 => .word (flagWord (Float32.lt (readFloat32 a) (readFloat32 b)))
  | .lt .f64 => .word (flagWord (Float.lt (readFloat a) (readFloat b)))
  | .le .f32 => .word (flagWord (Float32.le (readFloat32 a) (readFloat32 b)))
  | .le .f64 => .word (flagWord (Float.le (readFloat a) (readFloat b)))
  | .isFinite .f32 => .word (flagWord (readFloat32 a).isFinite)
  | .isFinite .f64 => .word (flagWord (readFloat a).isFinite)
  | .fromInt64 .f32 => .f32 (Int64.ofBitVec a).toFloat32
  | .fromInt64 .f64 => .f64 (Int64.ofBitVec a).toFloat
  | .fromUInt64 .f32 => .f32 (UInt64.ofBitVec a).toFloat32
  | .fromUInt64 .f64 => .f64 (UInt64.ofBitVec a).toFloat
  | .toInt64 .f32 => .word (readFloat32 a).toInt64.toBitVec
  | .toInt64 .f64 => .word (readFloat a).toInt64.toBitVec
  | .toUInt64 .f32 => .word (readFloat32 a).toUInt64.toBitVec
  | .toUInt64 .f64 => .word (readFloat a).toUInt64.toBitVec
  | .widen32 => .f64 (readFloat32 a).toFloat
  | .narrow32 => .f32 (readFloat a).toFloat32

/-- Floating outputs are related as native values. In particular, NaN payload bits
    are not fixed by the model. A binary32 result occupies one zero-extended word. -/
def NativeFPValue.Matches : NativeFPValue → W → Prop
  | .f32 value, result => result = (result.setWidth 32).setWidth 64 ∧ readFloat32 result = value
  | .f64 value, result => readFloat result = value
  | .word value, result => result = value

def NativeFPEval (op : NativeFPOp) (a b result : W) : Prop :=
  (nativeFP op a b).Matches result

/-- The native executable's representative; the semantic relation also permits
    other representations of the same native NaN value. -/
def nativeFPBits (op : NativeFPOp) (a b : W) : W :=
  match nativeFP op a b with
  | .f32 value => value.toBits.toBitVec.setWidth 64
  | .f64 value => value.toBits.toBitVec
  | .word value => value

/-- Appended opcodes: the existing integer and memory instructions keep 1 through 27. -/
def NativeFPOp.code : NativeFPOp → Nat
  | .add .f32 => 28 | .add .f64 => 29
  | .sub .f32 => 30 | .sub .f64 => 31
  | .mul .f32 => 32 | .mul .f64 => 33
  | .div .f32 => 34 | .div .f64 => 35
  | .neg .f32 => 36 | .neg .f64 => 37
  | .eq .f32 => 38 | .eq .f64 => 39
  | .lt .f32 => 40 | .lt .f64 => 41
  | .le .f32 => 42 | .le .f64 => 43
  | .isFinite .f32 => 44 | .isFinite .f64 => 45
  | .fromInt64 .f32 => 46 | .fromInt64 .f64 => 47
  | .fromUInt64 .f32 => 48 | .fromUInt64 .f64 => 49
  | .toInt64 .f32 => 50 | .toInt64 .f64 => 51
  | .toUInt64 .f32 => 52 | .toUInt64 .f64 => 53
  | .widen32 => 54 | .narrow32 => 55

def NativeFPOp.ofCode : Nat → Option NativeFPOp
  | 28 => some (.add .f32) | 29 => some (.add .f64)
  | 30 => some (.sub .f32) | 31 => some (.sub .f64)
  | 32 => some (.mul .f32) | 33 => some (.mul .f64)
  | 34 => some (.div .f32) | 35 => some (.div .f64)
  | 36 => some (.neg .f32) | 37 => some (.neg .f64)
  | 38 => some (.eq .f32) | 39 => some (.eq .f64)
  | 40 => some (.lt .f32) | 41 => some (.lt .f64)
  | 42 => some (.le .f32) | 43 => some (.le .f64)
  | 44 => some (.isFinite .f32) | 45 => some (.isFinite .f64)
  | 46 => some (.fromInt64 .f32) | 47 => some (.fromInt64 .f64)
  | 48 => some (.fromUInt64 .f32) | 49 => some (.fromUInt64 .f64)
  | 50 => some (.toInt64 .f32) | 51 => some (.toInt64 .f64)
  | 52 => some (.toUInt64 .f32) | 53 => some (.toUInt64 .f64)
  | 54 => some .widen32 | 55 => some .narrow32
  | _ => none

theorem NativeFPOp.ofCode_code (op : NativeFPOp) : ofCode op.code = some op := by
  cases op <;> first | (rename_i format; cases format <;> rfl) | rfl

theorem NativeFPOp.code_bounds (op : NativeFPOp) : 28 ≤ op.code ∧ op.code < 56 := by
  cases op <;> first | (rename_i format; cases format <;> decide) | decide

end Runner
