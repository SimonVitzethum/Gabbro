/- Native arithmetic and literal/computed-conversion images.
   Computed binary64 conversion and arithmetic use their Block hooks. -/
module
public import Stage0.Senke.Anweisung.Faelle.Gleit.Proben
public import Stage0.Senke.Ausdruck.Gleit.Slots.SlotContext
public import Stage0.Senke.Ausdruck.Gleit.Bereich
public import Stage0.Senke.Anweisung.Faelle.Gleit.AddCode
@[expose] public section

namespace Gabbro.Stage0.Senke.FloatArithmeticProbe
open Gabbro.Grammatik FloatProbe ControlProbe Runner.IR
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Both comparisons check the result, rather than just reaching the continuation. -/
def conversion (n : Int) (expected lo hi : Int × Int) : Body :=
  .floatOf (.lit n) lo hi (.floatLit expected lo hi
    (.cons (.ite
      (.and (.flle (.var (.there .here)) (.var .here))
        (.flle (.var .here) (.var (.there .here))))
      (returnBlock 7 (by decide) (by decide))
      (returnBlock 41 (by decide) (by decide))) .nil))

/-- Exercise conversion through the user-facing Block hook with a bound child. -/
def hookConversion (n : Int) (expected lo hi : Int × Int) : Body :=
  .bind (.add (.lit n) (.lit 0))
    (.floatOf (.var .here) lo hi (.floatLit expected lo hi
      (.cons (.ite
        (.and (.flle (.var (.there .here)) (.var .here))
          (.flle (.var .here) (.var (.there .here))))
        (returnBlock 7 (by decide) (by decide))
        (returnBlock 41 (by decide) (by decide))) .nil)))

/-- Compare the actual arithmetic Block result in both directions before returning. -/
def arithmetic (op : GleitOp) (expected : Int × Int) : Body :=
  .floatLit (1, 1) (0, 1) (10, 1)
    (.float op (.var .here) (.var .here) (0, 1) (10, 1)
      (.floatLit expected (0, 1) (10, 1)
        (.cons (.ite
          (.and (.flle (.var (.there .here)) (.var .here))
            (.flle (.var .here) (.var (.there .here))))
          (returnBlock 7 (by decide) (by decide))
          (returnBlock 41 (by decide) (by decide))) .nil)))

/-- Distinct operands use the public hook and compare its rounded result
    in both directions. Every arithmetic kernel shares this fixture. -/
def binaryArithmetic (op : GleitOp) (a b expected : Int × Int) : Body :=
  .floatLit a (0, 1) (10, 1)
    (.floatLit b (0, 1) (10, 1)
      (.float op (.var (.there .here)) (.var .here) (0, 1) (10, 1)
        (.floatLit expected (0, 1) (10, 1)
          (.cons (.ite
            (.and (.flle (.var (.there .here)) (.var .here))
              (.flle (.var .here) (.var (.there .here))))
            (returnBlock 7 (by decide) (by decide))
            (returnBlock 41 (by decide) (by decide))) .nil))))

def hookImages : List (String × Except String (List Runner.B) × Nat) :=
  [("hook-float-positive", blockImageOf (hookConversion 37 (37, 1) (0, 1) (100, 1)), 7),
   ("hook-float-negative", blockImageOf (hookConversion (-37) (-37, 1) (-100, 1) (0, 1)), 7),
   ("hook-float-zero", blockImageOf (hookConversion 0 (0, 1) (0, 1) (0, 1)), 7),
   ("hook-float-lower", blockImageOf (hookConversion 37 (37, 1) (38, 1) (100, 1)), 107),
   ("hook-float-upper", blockImageOf (hookConversion 37 (37, 1) (0, 1) (36, 1)), 107),
   ("hook-float-nan", blockImageOf (hookConversion 37 (37, 1) (0, 0) (100, 1)), 107),
   ("hook-float-reversed", blockImageOf (hookConversion 37 (37, 1) (100, 1) (0, 1)), 107)]

/-- Test the actual shared fragment, including its scratch-slot placement.
    Non-NaN words are checked exactly; NaNs by class. A match returns 7, otherwise 41. -/
def wordImage (fragment : Option (List II × Nat)) (expected : Nat) :
    Except String (List Runner.B) := do
  let cr ← match fragment with
    | some c => Except.ok c
    | none => Except.error "word fragment refused"
  let comparison := if (Float.hwOfBits (UInt64.ofNat expected)).hwIsNaN then
      [ci (Runner.NativeFPOp.eq .f64).code 8 8 8, ci 1 9 1 0, ci 10 8 8 9]
    else (konstWL 4 expected 9).1 ++ [ci 14 8 8 9]
  let code := cr.1 ++ comparison ++
    [ci 1 9 34 0, ci 5 8 8 9, ci 1 1 41 0, ci 4 1 1 8,
     ci 1 0 231 0, ci 1 2 0 0, ci 1 3 0 0, ci 1 4 0 0, ci 1 5 0 0, ci 1 6 0 0, ci 23 7 0 0]
  pure (Runner.Prog.irImage ((code.map fun i => .op i.o i.a i.b i.c) ++
    [.lab 99, .zeros 1024]) 99)

/-- Execute the actual native subtraction opcode. NaNs are checked by class,
    while non-NaN expectations retain their complete word, including zero sign. -/
def subtractionImage (a b expected : Nat) : Except String (List Runner.B) :=
  wordImage (floatWordsL .sub 8 (fun d => some (konstWL 4 a d))
    (fun d => some (konstWL 4 b d))) expected

/-- Fixed CPU-regression words for both formats. Their primitive conversion replies
    are supplied explicitly below; the proof kernel performs no floating arithmetic. -/
def computedSamples : List (Runner.FPFormat × Int × Nat) :=
  [
    (Runner.FPFormat.f32, 0, 0),
    (Runner.FPFormat.f32, 37, 1108606976),
    (Runner.FPFormat.f32, -37, 3256090624),
    (Runner.FPFormat.f32, -9223372036854775808, 3741319168),
    (Runner.FPFormat.f32, 9223372036854775807, 1593835520),
    (Runner.FPFormat.f32, 16777217, 1266679808),
    (Runner.FPFormat.f32, 33554431, 1275068416),
    (Runner.FPFormat.f32, 8388608, 1258291200),
    (Runner.FPFormat.f32, 9007199254740993, 1509949440),
    (Runner.FPFormat.f32, 18014398509481983, 1518338048),
    (Runner.FPFormat.f32, 4503599627370496, 1501560832),
    (Runner.FPFormat.f64, 0, 0),
    (Runner.FPFormat.f64, 37, 4630404104378646528),
    (Runner.FPFormat.f64, -37, 13853776141233422336),
    (Runner.FPFormat.f64, -9223372036854775808, 14114281232179134464),
    (Runner.FPFormat.f64, 9223372036854775807, 4890909195324358656),
    (Runner.FPFormat.f64, 16777217, 4715268810125344768),
    (Runner.FPFormat.f64, 33554431, 4719772409215844352),
    (Runner.FPFormat.f64, 8388608, 4710765210229538816),
    (Runner.FPFormat.f64, 9007199254740993, 4845873199050653696),
    (Runner.FPFormat.f64, 18014398509481983, 4850376798678024192),
    (Runner.FPFormat.f64, 4503599627370496, 4841369599423283200)]

theorem computedSamples_bits
    (answers : ∀ format z bits, (format, z, bits) ∈ computedSamples →
      (match format with
      | .f32 => (Int64.ofInt z).hwToFloat32.hwToBits.toNat
      | .f64 => (Int64.ofInt z).hwToFloat.hwToBits.toNat) = bits) :
    computedSamples.all (fun (f, z, bits) =>
      decide ((match f with
        | .f32 => (Int64.ofInt z).hwToFloat32.hwToBits.toNat
        | .f64 => (Int64.ofInt z).hwToFloat.hwToBits.toNat) = bits)) = true := by
  apply List.all_eq_true.mpr
  rintro ⟨format, z, bits⟩ member
  simp only [decide_eq_true_eq]
  exact answers format z bits member

/-- Execute the emitted conversion, including a real integer-producing child.
    These format-specific fragment probes complement the binary64 block-hook probes. -/
def computedImage (f : Runner.FPFormat) (z : Int) (expected : Nat) :
    Except String (List Runner.B) :=
  wordImage (nativeFPWordL (.fromInt64 f) 8
    (some (konstWL 4 (BitVec.ofInt 64 z).toNat 8)) (some ([ci 1 9 0 0], 10))) expected

def computedImages : List (String × Except String (List Runner.B) × Nat) :=
  computedSamples.zipIdx |>.map fun ((f, z, expected), i) =>
    (s!"computed-float-{i}", computedImage f z expected, 7)

/-- Real expression children exercise ordinary lowering, including its reservation. -/
def expressionImage : Except String (List Runner.B) :=
  wordImage (computedFloatOfE (layU u (fun _ => some gateBinding) 0)
    (Expr.add (Γ := []) (Λ := []) (.lit 19) (.lit 18)) 8 4)
    4630404104378646528

/-- Execute the production single-evaluation binder with the ordinary expression
    candidate, the actual retained-result guard and both existing stop outcomes. -/
def rangeImage (z : Int) (lo hi : Int × Int) : Except String (List Runner.B) := do
  let emitted ← match nativeFloatBindL 8 lo hi
      (fun d => computedFloatOfE (layU u (fun _ => some gateBinding) 0)
        (Expr.add (Γ := []) (Λ := [])
          (.mul (.lit (z / 1073741824)) (.lit 1073741824))
          (.lit (z % 1073741824))) d 4)
      (fun _ => some (stopC 7 0, 8)) with
    | some c => Except.ok c
    | none => Except.error "computed range fragment refused"
  pure (Runner.Prog.irImage ((emitted.1.map fun i => .op i.o i.a i.b i.c) ++
    [.lab 99, .zeros 1024]) 99)

def rangeImages : List (String × Except String (List Runner.B) × Nat) :=
  [("computed-expression-add", expressionImage, 7),
   ("computed-range-inside", rangeImage 37 (0, 1) (100, 1), 7),
   ("computed-range-lower", rangeImage 0 (0, 1) (100, 1), 7),
   ("computed-range-upper", rangeImage 100 (0, 1) (100, 1), 7),
   ("computed-range-below", rangeImage (-1) (0, 1) (100, 1), 107),
   ("computed-range-above", rangeImage 101 (0, 1) (100, 1), 107),
   ("computed-range-reversed", rangeImage 1 (2, 1) (0, 1), 107),
   ("computed-range-nan-lower", rangeImage 0 (0, 0) (1, 1), 107),
   ("computed-range-nan-upper", rangeImage 0 (0, 1) (0, 0), 107),
   ("computed-range-infinite", rangeImage (-37) (-(2^1024), 1) (2^1024, 1), 7),
   ("computed-range-positive-infinity", rangeImage 37 (2^1024, 1) (2^1024, 1), 107),
   ("computed-range-negative-infinity", rangeImage (-37) (-(2^1024), 1) (-(2^1024), 1), 107),
   ("computed-range-round-in", rangeImage (2^53 + 1) (0, 1) (2^53, 1), 7),
   ("computed-range-round-out", rangeImage (2^53 + 3) (0, 1) (2^53 + 2, 1), 107)]

/-- Primitive replies for the fixed conversion/range operands, excluding the
    final source rejection decision and every compiler/outcome statement. -/
structure ComputedRangeAnswers : Prop where
  inside : RangeAnswers (0, 1) (100, 1) (Float.hwOfInt 37) true true true
  zero : RangeAnswers (0, 1) (100, 1) (Float.hwOfInt 0) true true true
  upper : RangeAnswers (0, 1) (100, 1) (Float.hwOfInt 100) true true true
  below : RangeAnswers (0, 1) (100, 1) (Float.hwOfInt (-1)) true false true
  above : RangeAnswers (0, 1) (100, 1) (Float.hwOfInt 101) true true false
  nanLower : RangeAnswers (0, 0) (100, 1) (Float.hwOfInt 0) true false true
  positiveInfinity : RangeAnswers (2^1024, 1) (2^1024, 1) (Float.hwOfInt 37) true false true
  negativeInfinity : RangeAnswers (-(2^1024), 1) (-(2^1024), 1) (Float.hwOfInt (-37)) true true false

/-- The expected range exits agree with the source decision after rounding.
    Emission and processor execution are measured separately. -/
theorem computed_range_decisions_zeuge (answers : ComputedRangeAnswers) :
    floatRangeReject (0, 1) (100, 1) (gleitAusInt 37) = false ∧
    floatRangeReject (0, 1) (100, 1) (gleitAusInt 0) = false ∧
    floatRangeReject (0, 1) (100, 1) (gleitAusInt 100) = false ∧
    floatRangeReject (0, 1) (100, 1) (gleitAusInt (-1)) = true ∧
    floatRangeReject (0, 1) (100, 1) (gleitAusInt 101) = true ∧
    floatRangeReject (0, 0) (100, 1) (gleitAusInt 0) = true ∧
    floatRangeReject (2^1024, 1) (2^1024, 1) (gleitAusInt 37) = true ∧
    floatRangeReject (-(2^1024), 1) (-(2^1024), 1) (gleitAusInt (-37)) = true := by
  exact ⟨answers.inside.reject, answers.zero.reject, answers.upper.reject,
    answers.below.reject, answers.above.reject, answers.nanLower.reject,
    answers.positiveInfinity.reject, answers.negativeInfinity.reject⟩

def images : List (String × Except String (List Runner.B) × Nat) :=
  [("float-add", blockImageOf (arithmetic .add (2, 1)), 7),
   ("float-sub", blockImageOf (arithmetic .sub (0, 1)), 7),
   ("float-sub-positive-zero", subtractionImage 4607182418800017408 4607182418800017408 0, 7),
   ("float-sub-negative", subtractionImage 4607182418800017408 4611686018427387904 13830554455654793216, 7),
   ("float-sub-negative-zero", subtractionImage 9223372036854775808 0 9223372036854775808, 7),
   ("float-sub-subnormal", subtractionImage 4503599627370496 4503599627370495 1, 7),
   ("float-sub-nan-left", subtractionImage 18442240474082181127 9218868437227405321 18442240474082181127, 7),
   ("float-sub-nan-right", subtractionImage 0 18442240474082181129 9218868437227405321, 7),
   ("float-of-zero", blockImageOf (conversion 0 (0, 1) (-1, 1) (1, 1)), 7),
   ("float-of-negative", blockImageOf (conversion (-1) (-1, 1) (-2, 1) (2, 1)), 7),
   ("float-of-exact", blockImageOf (conversion (2^53) (2^53, 1) (0, 1) (2^54, 1)), 7),
   ("float-of-tie-even", blockImageOf (conversion (2^53 + 1) (2^53, 1) (0, 1) (2^54, 1)), 7),
   ("float-of-tie-odd", blockImageOf (conversion (2^53 + 3) (2^53 + 4, 1) (0, 1) (2^54, 1)), 7),
   ("float-of-negative-tie", blockImageOf (conversion (-(2^53 + 1)) (-(2^53), 1) (-(2^54), 1) (0, 1)), 7),
   ("float-of-signed-min", blockImageOf (conversion (-(2^63)) (-(2^63), 1) (-(2^64), 1) (0, 1)), 7),
   ("float-of-signed-max", blockImageOf (conversion (2^63 - 1) (2^63, 1) (0, 1) (2^64, 1)), 7),
   ("float-of-carry", blockImageOf (conversion (2^54 - 1) (2^54, 1) (0, 1) (2^55, 1)), 7),
   ("float-of-wide-literal", blockImageOf (conversion (2^80) (2^80, 1) (0, 1) (2^81, 1)), 7),
   ("float-of-rounded-in-range", blockImageOf (conversion (2^53 + 1) (2^53, 1) (0, 1) (2^53, 1)), 7),
   ("float-of-rounded-outside", blockImageOf (conversion (2^53 + 3) (0, 1) (0, 1) (2^53 + 2, 1)), 107),
   ("float-of-overflow", blockImageOf (conversion (2^1024) (0, 1) (-(2^1024), 1) (2^1024, 1)), 107),
   ("float-of-nan-bound", blockImageOf (conversion 0 (0, 1) (0, 0) (1, 1)), 107),
   ("float-of-empty-range", blockImageOf (conversion 1 (0, 1) (2, 1) (0, 1)), 107)]

/-- Fixed native add/sub replies only; no source, IR or acceptance conclusion. -/
structure AddSubAnswers : Prop where
  negativeZero : Float.hwAdd (Float.hwOfBits (UInt64.ofNat (2^63 + (0) * 2^52 + (0)))) (Float.hwOfBits (UInt64.ofNat (2^63 + (0) * 2^52 + (0)))) = (Float.hwOfBits (UInt64.ofNat (2^63 + (0) * 2^52 + (0))))
  oppositeZeros : Float.hwAdd (Float.hwOfBits (UInt64.ofNat (0 + (0) * 2^52 + (0)))) (Float.hwOfBits (UInt64.ofNat (2^63 + (0) * 2^52 + (0)))) = (Float.hwOfBits (UInt64.ofNat (0 + (0) * 2^52 + (0))))
  subnormalAdd : Float.hwAdd (Float.hwOfBits (UInt64.ofNat (0 + (0) * 2^52 + (1)))) (Float.hwOfBits (UInt64.ofNat (0 + (0) * 2^52 + (1)))) = (Float.hwOfBits (UInt64.ofNat (0 + (0) * 2^52 + (2))))
  subnormalCancel : Float.hwSub (Float.hwOfBits (UInt64.ofNat (0 + (0) * 2^52 + (1)))) (Float.hwOfBits (UInt64.ofNat (0 + (0) * 2^52 + (1)))) = (Float.hwOfBits (UInt64.ofNat (0 + (0) * 2^52 + (0))))
  zeroSubtract : Float.hwSub (Float.hwOfBits (UInt64.ofNat (2^63 + (0) * 2^52 + (0)))) (Float.hwOfBits (UInt64.ofNat (0 + (0) * 2^52 + (0)))) = (Float.hwOfBits (UInt64.ofNat (2^63 + (0) * 2^52 + (0))))
  normalSubtract : Float.hwSub (Float.hwOfBits (UInt64.ofNat (0 + (1) * 2^52 + (0)))) (Float.hwOfBits (UInt64.ofNat (0 + (0) * 2^52 + (2^52 - 1)))) = (Float.hwOfBits (UInt64.ofNat (0 + (0) * 2^52 + (1))))
  evenTie : Float.hwAdd (Float.hwOfBits (UInt64.ofNat (0 + (1023) * 2^52 + (0)))) (Float.hwOfBits (UInt64.ofNat (0 + (970) * 2^52 + (0)))) = (Float.hwOfBits (UInt64.ofNat (0 + (1023) * 2^52 + (0))))
  oddTie : Float.hwAdd (Float.hwOfBits (UInt64.ofNat (0 + (1023) * 2^52 + (1)))) (Float.hwOfBits (UInt64.ofNat (0 + (970) * 2^52 + (0)))) = (Float.hwOfBits (UInt64.ofNat (0 + (1023) * 2^52 + (2))))
  smallSubtract : Float.hwSub (Float.hwOfBits (UInt64.ofNat (0 + (1023) * 2^52 + (0)))) (Float.hwOfBits (UInt64.ofNat (0 + (969) * 2^52 + (0)))) = (Float.hwOfBits (UInt64.ofNat (0 + (1023) * 2^52 + (0))))
  infinityAdd : Float.hwAdd (Float.hwOfBits (UInt64.ofNat (0 + (2047) * 2^52 + (0)))) (Float.hwOfBits (UInt64.ofNat (2^63 + (2047) * 2^52 + (0)))) = (Float.hwOfBits (UInt64.ofNat (0 + (2047) * 2^52 + (1))))
  infinitySubtract : Float.hwSub (Float.hwOfBits (UInt64.ofNat (0 + (2047) * 2^52 + (0)))) (Float.hwOfBits (UInt64.ofNat (0 + (2047) * 2^52 + (0)))) = (Float.hwOfBits (UInt64.ofNat (0 + (2047) * 2^52 + (1))))
  leftNaN : Float.hwAdd (Float.hwOfBits (UInt64.ofNat (2^63 + (2047) * 2^52 + (7)))) (Float.hwOfBits (UInt64.ofNat (0 + (2047) * 2^52 + (9)))) = (Float.hwOfBits (UInt64.ofNat (2^63 + (2047) * 2^52 + (7))))
  rightNaN : Float.hwSub (Float.hwOfBits (UInt64.ofNat (0 + (0) * 2^52 + (0)))) (Float.hwOfBits (UInt64.ofNat (2^63 + (2047) * 2^52 + (9)))) = (Float.hwOfBits (UInt64.ofNat (0 + (2047) * 2^52 + (9))))
  overflow : Float.hwAdd (Float.hwOfBits (UInt64.ofNat (0 + (2046) * 2^52 + (2^52 - 1)))) (Float.hwOfBits (UInt64.ofNat (0 + (2046) * 2^52 + (2^52 - 1)))) =
      (Float.hwOfBits (UInt64.ofNat (0 + (2047) * 2^52 + (0))))

/-- The unchanged edge claims follow from the explicit primitive hardware replies. -/
theorem float_add_sub_model_zeuge (answers : AddSubAnswers) :
    Float.hwAdd (Float.hwOfBits (UInt64.ofNat (2^63 + (0) * 2^52 + (0)))) (Float.hwOfBits (UInt64.ofNat (2^63 + (0) * 2^52 + (0)))) = (Float.hwOfBits (UInt64.ofNat (2^63 + (0) * 2^52 + (0)))) ∧
    Float.hwAdd (Float.hwOfBits (UInt64.ofNat (0 + (0) * 2^52 + (0)))) (Float.hwOfBits (UInt64.ofNat (2^63 + (0) * 2^52 + (0)))) = (Float.hwOfBits (UInt64.ofNat (0 + (0) * 2^52 + (0)))) ∧
    Float.hwAdd (Float.hwOfBits (UInt64.ofNat (0 + (0) * 2^52 + (1)))) (Float.hwOfBits (UInt64.ofNat (0 + (0) * 2^52 + (1)))) = (Float.hwOfBits (UInt64.ofNat (0 + (0) * 2^52 + (2)))) ∧
    Float.hwSub (Float.hwOfBits (UInt64.ofNat (0 + (0) * 2^52 + (1)))) (Float.hwOfBits (UInt64.ofNat (0 + (0) * 2^52 + (1)))) = (Float.hwOfBits (UInt64.ofNat (0 + (0) * 2^52 + (0)))) ∧
    Float.hwSub (Float.hwOfBits (UInt64.ofNat (2^63 + (0) * 2^52 + (0)))) (Float.hwOfBits (UInt64.ofNat (0 + (0) * 2^52 + (0)))) = (Float.hwOfBits (UInt64.ofNat (2^63 + (0) * 2^52 + (0)))) ∧
    Float.hwSub (Float.hwOfBits (UInt64.ofNat (0 + (1) * 2^52 + (0)))) (Float.hwOfBits (UInt64.ofNat (0 + (0) * 2^52 + (2^52 - 1)))) = (Float.hwOfBits (UInt64.ofNat (0 + (0) * 2^52 + (1)))) ∧
    Float.hwAdd (Float.hwOfBits (UInt64.ofNat (0 + (1023) * 2^52 + (0)))) (Float.hwOfBits (UInt64.ofNat (0 + (970) * 2^52 + (0)))) = (Float.hwOfBits (UInt64.ofNat (0 + (1023) * 2^52 + (0)))) ∧
    Float.hwAdd (Float.hwOfBits (UInt64.ofNat (0 + (1023) * 2^52 + (1)))) (Float.hwOfBits (UInt64.ofNat (0 + (970) * 2^52 + (0)))) = (Float.hwOfBits (UInt64.ofNat (0 + (1023) * 2^52 + (2)))) ∧
    Float.hwSub (Float.hwOfBits (UInt64.ofNat (0 + (1023) * 2^52 + (0)))) (Float.hwOfBits (UInt64.ofNat (0 + (969) * 2^52 + (0)))) = (Float.hwOfBits (UInt64.ofNat (0 + (1023) * 2^52 + (0)))) ∧
    Float.hwAdd (Float.hwOfBits (UInt64.ofNat (0 + (2047) * 2^52 + (0)))) (Float.hwOfBits (UInt64.ofNat (2^63 + (2047) * 2^52 + (0)))) = (Float.hwOfBits (UInt64.ofNat (0 + (2047) * 2^52 + (1)))) ∧
    Float.hwSub (Float.hwOfBits (UInt64.ofNat (0 + (2047) * 2^52 + (0)))) (Float.hwOfBits (UInt64.ofNat (0 + (2047) * 2^52 + (0)))) = (Float.hwOfBits (UInt64.ofNat (0 + (2047) * 2^52 + (1)))) ∧
    Float.hwAdd (Float.hwOfBits (UInt64.ofNat (2^63 + (2047) * 2^52 + (7)))) (Float.hwOfBits (UInt64.ofNat (0 + (2047) * 2^52 + (9)))) = (Float.hwOfBits (UInt64.ofNat (2^63 + (2047) * 2^52 + (7)))) ∧
    Float.hwSub (Float.hwOfBits (UInt64.ofNat (0 + (0) * 2^52 + (0)))) (Float.hwOfBits (UInt64.ofNat (2^63 + (2047) * 2^52 + (9)))) = (Float.hwOfBits (UInt64.ofNat (0 + (2047) * 2^52 + (9)))) ∧
    Float.hwAdd (Float.hwOfBits (UInt64.ofNat (0 + (2046) * 2^52 + (2^52 - 1)))) (Float.hwOfBits (UInt64.ofNat (0 + (2046) * 2^52 + (2^52 - 1)))) =
      (Float.hwOfBits (UInt64.ofNat (0 + (2047) * 2^52 + (0)))) := by
  exact ⟨answers.negativeZero, answers.oppositeZeros, answers.subnormalAdd, answers.subnormalCancel, answers.zeroSubtract, answers.normalSubtract, answers.evenTie, answers.oddTie, answers.smallSubtract, answers.infinityAdd, answers.infinitySubtract, answers.leftNaN, answers.rightNaN, answers.overflow⟩

end Gabbro.Stage0.Senke.FloatArithmeticProbe
