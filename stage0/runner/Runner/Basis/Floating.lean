module

public import Runner.Basis.Mem
public import NativeFloat.Primitives

@[expose] public section

namespace Runner

inductive FPFormat where
  | f32 | f64
  deriving DecidableEq, Repr

/-- Operations of the existing runner, expressed through opaque CPU primitives.
    Their numerical guarantees require the named native hardware contract. -/
inductive NativeFPOp where
  | add (format : FPFormat) | sub (format : FPFormat)
  | mul (format : FPFormat) | div (format : FPFormat)
  | neg (format : FPFormat)
  | eq (format : FPFormat) | lt (format : FPFormat) | le (format : FPFormat)
  | isFinite (format : FPFormat)
  | fromInt64 (format : FPFormat) | fromUInt64 (format : FPFormat)
  | toInt64 (format : FPFormat) | toUInt64 (format : FPFormat)
  | widen32 | narrow32
  | compare (format : FPFormat)
  | truncateInt64 (format : FPFormat)
  deriving DecidableEq, Repr

def readFloat (word : W) : Float := Float.hwOfBits (UInt64.ofBitVec word)
def readFloat32 (word : W) : Float32 := Float32.hwOfBits (UInt32.ofBitVec (word.setWidth 32))

def fpLow32 (word : W) : W := (word.setWidth 32).setWidth 64

/-- NEG is the deterministic sign-bit codec used by the physical integer XOR,
    including raw NaN payloads. Binary32 explicitly clears the upper word. -/
def fpNegWord : FPFormat → W → W
  | .f32, value => ((value.setWidth 32) ^^^ 0x80000000).setWidth 64
  | .f64, value => value ^^^ 0x8000000000000000

theorem fpNegWord_low32 (word : W) : fpNegWord .f32 (fpLow32 word) = fpNegWord .f32 word := by
  change (((word.setWidth 32).setWidth 64).setWidth 32 ^^^ (0x80000000 : BitVec 32)).setWidth 64 =
    (word.setWidth 32 ^^^ (0x80000000 : BitVec 32)).setWidth 64
  rw [BitVec.setWidth_setWidth_of_le (word.setWidth 32) (k := 32) (l := 64) (by decide),
    BitVec.setWidth_eq]

/-- Only actual scalar operands enter a CPU request. Unary instructions have no
    second hardware operand; their IR field-3 read still occurs before this point. -/
def NativeFPOp.inputs : NativeFPOp → W → W → W × W
  | .add .f32, a, b | .sub .f32, a, b | .mul .f32, a, b | .div .f32, a, b
  | .eq .f32, a, b | .lt .f32, a, b | .le .f32, a, b
  | .compare .f32, a, b => (fpLow32 a, fpLow32 b)
  | .add .f64, a, b | .sub .f64, a, b | .mul .f64, a, b | .div .f64, a, b
  | .eq .f64, a, b | .lt .f64, a, b | .le .f64, a, b
  | .compare .f64, a, b => (a, b)
  | .neg .f32, a, _ | .isFinite .f32, a, _ | .toInt64 .f32, a, _
  | .toUInt64 .f32, a, _ | .truncateInt64 .f32, a, _ | .widen32, a, _ => (fpLow32 a, 0)
  | _, a, _ => (a, 0)

theorem readFloat32_low32 (word : W) : readFloat32 (fpLow32 word) = readFloat32 word := by
  unfold readFloat32 fpLow32
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

/-- A native result before its storage representation is chosen. -/
inductive NativeFPValue where
  | f32 (value : Float32)
  | f64 (value : Float)
  | word (value : W)

def flagWord (value : Bool) : W := if value then 1 else 0

/-- The observable UCOMIS flags; the other arithmetic flags are cleared. -/
def fpCompareFlags (unordered less equal : Bool) : W :=
  if unordered then 0x45 else if less then 1 else if equal then 0x40 else 0

def truncateFloat64 (value : Float) : W :=
  if value.hwIsNaN || Float.hwLt value Int64.minValue.hwToFloat ||
      !(Float.hwLt value (UInt64.ofNat (2 ^ 63)).hwToFloat) then BitVec.ofNat 64 (2 ^ 63)
  else value.hwToInt64.toBitVec

def truncateFloat32 (value : Float32) : W :=
  if value.hwIsNaN || Float32.hwLt value Int64.minValue.hwToFloat32 ||
      !(Float32.hwLt value (UInt64.ofNat (2 ^ 63)).hwToFloat32) then BitVec.ofNat 64 (2 ^ 63)
  else value.hwToInt64.toBitVec

private theorem flagWord_normalize (value : Bool) :
    (if flagWord value = 0 then (0 : W) else 1) = flagWord value := by
  cases value <;> rfl

/-- Normalize a CPU answer at its scalar result width. This also keeps the two
    request trees symmetric for answers outside the machine's Eval relation. -/
def NativeFPOp.resultWord : NativeFPOp → W → W
  | .compare _, value => value &&& 0x45
  | .eq _, value | .lt _, value | .le _, value | .isFinite _, value => if value = 0 then 0 else 1
  | .add .f32, value | .sub .f32, value | .mul .f32, value | .div .f32, value
  | .neg .f32, value | .fromInt64 .f32, value | .fromUInt64 .f32, value
  | .narrow32, value => fpLow32 value
  | _, value => value

private theorem neg_resultWord (format : FPFormat) (word : W) :
    (NativeFPOp.neg format).resultWord (fpNegWord format word) = fpNegWord format word := by
  cases format
  · change ((((word.setWidth 32) ^^^ 0x80000000).setWidth 64).setWidth 32).setWidth 64 =
      ((word.setWidth 32) ^^^ (0x80000000 : BitVec 32)).setWidth 64
    rw [BitVec.setWidth_setWidth_of_le ((word.setWidth 32) ^^^ (0x80000000 : BitVec 32))
      (k := 32) (l := 64) (by decide), BitVec.setWidth_eq]
  · rfl

private theorem fpCompareFlags_mask (unordered less equal : Bool) :
    (fpCompareFlags unordered less equal &&& (0x45 : W)) = fpCompareFlags unordered less equal := by
  cases unordered <;> cases less <;> cases equal <;> rfl

/-- One common opaque primitive specification; no floating arithmetic is unfolded
    or implemented by the runner's proof kernel. -/
def nativeFP (op : NativeFPOp) (a b : W) : NativeFPValue :=
  match op with
  | .add .f32 => .f32 (Float32.hwAdd (readFloat32 a) (readFloat32 b))
  | .add .f64 => .f64 (Float.hwAdd (readFloat a) (readFloat b))
  | .sub .f32 => .f32 (Float32.hwSub (readFloat32 a) (readFloat32 b))
  | .sub .f64 => .f64 (Float.hwSub (readFloat a) (readFloat b))
  | .mul .f32 => .f32 (Float32.hwMul (readFloat32 a) (readFloat32 b))
  | .mul .f64 => .f64 (Float.hwMul (readFloat a) (readFloat b))
  | .div .f32 => .f32 (Float32.hwDiv (readFloat32 a) (readFloat32 b))
  | .div .f64 => .f64 (Float.hwDiv (readFloat a) (readFloat b))
  | .neg format => .word (fpNegWord format a)
  | .eq .f32 => .word (flagWord (Float32.hwBEq (readFloat32 a) (readFloat32 b)))
  | .eq .f64 => .word (flagWord (Float.hwBEq (readFloat a) (readFloat b)))
  | .lt .f32 => .word (flagWord (Float32.hwLt (readFloat32 a) (readFloat32 b)))
  | .lt .f64 => .word (flagWord (Float.hwLt (readFloat a) (readFloat b)))
  | .le .f32 => .word (flagWord (Float32.hwLe (readFloat32 a) (readFloat32 b)))
  | .le .f64 => .word (flagWord (Float.hwLe (readFloat a) (readFloat b)))
  | .isFinite .f32 => .word (flagWord (readFloat32 a).hwIsFinite)
  | .isFinite .f64 => .word (flagWord (readFloat a).hwIsFinite)
  | .fromInt64 .f32 => .f32 (Int64.ofBitVec a).hwToFloat32
  | .fromInt64 .f64 => .f64 (Int64.ofBitVec a).hwToFloat
  | .fromUInt64 .f32 => .f32 (UInt64.ofBitVec a).hwToFloat32
  | .fromUInt64 .f64 => .f64 (UInt64.ofBitVec a).hwToFloat
  | .toInt64 .f32 => .word (readFloat32 a).hwToInt64.toBitVec
  | .toInt64 .f64 => .word (readFloat a).hwToInt64.toBitVec
  | .toUInt64 .f32 => .word (readFloat32 a).hwToUInt64.toBitVec
  | .toUInt64 .f64 => .word (readFloat a).hwToUInt64.toBitVec
  | .widen32 => .f64 (readFloat32 a).hwToFloat
  | .narrow32 => .f32 (readFloat a).hwToFloat32
  | .compare .f32 => .word (fpCompareFlags ((readFloat32 a).hwIsNaN || (readFloat32 b).hwIsNaN)
      (Float32.hwLt (readFloat32 a) (readFloat32 b)) (Float32.hwBEq (readFloat32 a) (readFloat32 b)))
  | .compare .f64 => .word (fpCompareFlags ((readFloat a).hwIsNaN || (readFloat b).hwIsNaN)
      (Float.hwLt (readFloat a) (readFloat b)) (Float.hwBEq (readFloat a) (readFloat b)))
  | .truncateInt64 .f32 => .word (truncateFloat32 (readFloat32 a))
  | .truncateInt64 .f64 => .word (truncateFloat64 (readFloat a))

/-- Floating outputs are related as native values. In particular, NaN payload bits
    are not fixed by the model. A binary32 result occupies one zero-extended word. -/
def NativeFPValue.Matches : NativeFPValue → W → Prop
  | .f32 value, result => result = (result.setWidth 32).setWidth 64 ∧ readFloat32 result = value
  | .f64 value, result => readFloat result = value
  | .word value, result => result = value

def NativeFPEval (op : NativeFPOp) (a b result : W) : Prop :=
  (nativeFP op a b).Matches result

theorem nativeFP_inputs (op : NativeFPOp) (a b : W) :
    nativeFP op (op.inputs a b).1 (op.inputs a b).2 = nativeFP op a b := by
  cases op <;> first
    | (rename_i format; cases format <;> simp only [nativeFP, NativeFPOp.inputs, readFloat32_low32,
        fpNegWord_low32])
    | simp only [nativeFP, NativeFPOp.inputs, readFloat32_low32, fpNegWord_low32]

theorem NativeFPEval.resultWord {op : NativeFPOp} {a b result : W}
    (h : NativeFPEval op a b result) : op.resultWord result = result := by
  cases op <;> first
    | (rename_i format; cases format)
    | skip
  all_goals simp only [NativeFPEval, nativeFP, NativeFPValue.Matches] at h
  all_goals first
    | exact h.1.symm
    | rfl
    | (subst result; exact neg_resultWord _ _)
    | (subst result; exact flagWord_normalize _)
    | (subst result; exact fpCompareFlags_mask _ _ _)

/-- The native executable's representative; the semantic relation also permits
    other representations of the same native NaN value. -/
def nativeFPBits (op : NativeFPOp) (a b : W) : W :=
  match nativeFP op a b with
  | .f32 value => value.hwToBits.toBitVec.setWidth 64
  | .f64 value => value.hwToBits.toBitVec
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
  | .compare .f32 => 56 | .compare .f64 => 57
  | .truncateInt64 .f32 => 58 | .truncateInt64 .f64 => 59

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
  | 56 => some (.compare .f32) | 57 => some (.compare .f64)
  | 58 => some (.truncateInt64 .f32) | 59 => some (.truncateInt64 .f64)
  | _ => none

/-- Operations realized by one physical scalar floating instruction. The remaining
    operations require the runner's portable integer/primitive compositions. -/
def NativeFPOp.direct : NativeFPOp → Bool
  | .add _ | .sub _ | .mul _ | .div _ | .eq _ | .lt _ | .le _
  | .fromInt64 _ | .widen32 | .narrow32 | .compare _ | .truncateInt64 _ => true
  | _ => false

theorem NativeFPOp.ofCode_code (op : NativeFPOp) : ofCode op.code = some op := by
  cases op <;> first | (rename_i format; cases format <;> rfl) | rfl

theorem NativeFPOp.code_bounds (op : NativeFPOp) : 28 ≤ op.code ∧ op.code < 60 := by
  cases op <;> first | (rename_i format; cases format <;> decide) | decide

end Runner
