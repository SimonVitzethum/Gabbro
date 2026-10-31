/- Arithmetic foundations: executable rounding and literal-conversion images.
   Computed binary64 conversion is connected to the block hook; float arithmetic remains refused. -/
import Stage0.Senke.Anweisung.Faelle.Gleit.Proben
import Stage0.Senke.Ausdruck.Gleit.RundCode
import Stage0.Senke.Ausdruck.Gleit.Betrag
import Stage0.Senke.Ausdruck.Gleit.Schieben
import Stage0.Senke.Ausdruck.Gleit.Skalieren
import Stage0.Senke.Ausdruck.Gleit.SlotContext
import Stage0.Senke.Ausdruck.Gleit.Bereich

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

def hookImages : List (String × Except String (List Runner.B) × Nat) :=
  [("hook-float-positive", blockImageOf (hookConversion 37 (37, 1) (0, 1) (100, 1)), 7),
   ("hook-float-negative", blockImageOf (hookConversion (-37) (-37, 1) (-100, 1) (0, 1)), 7),
   ("hook-float-zero", blockImageOf (hookConversion 0 (0, 1) (0, 1) (0, 1)), 7),
   ("hook-float-lower", blockImageOf (hookConversion 37 (37, 1) (38, 1) (100, 1)), 107),
   ("hook-float-upper", blockImageOf (hookConversion 37 (37, 1) (0, 1) (36, 1)), 107),
   ("hook-float-nan", blockImageOf (hookConversion 37 (37, 1) (0, 0) (100, 1)), 107),
   ("hook-float-reversed", blockImageOf (hookConversion 37 (37, 1) (100, 1) (0, 1)), 107)]

/-- Test the actual shared fragment, including its scratch-slot placement.
    Equality to the expected word returns 7; a mismatch returns 41. -/
def wordImage (fragment : Option (List II × Nat)) (expected : Nat) :
    Except String (List Runner.B) := do
  let cr ← match fragment with
    | some c => Except.ok c
    | none => Except.error "word fragment refused"
  let code := cr.1 ++ (konstWL 4 expected 9).1 ++
    [ci 14 8 8 9, ci 1 9 34 0, ci 5 8 8 9, ci 1 1 41 0, ci 4 1 1 8,
     ci 1 0 231 0, ci 1 2 0 0, ci 1 3 0 0, ci 1 4 0 0, ci 1 5 0 0, ci 1 6 0 0, ci 23 7 0 0]
  pure (Runner.Prog.irImage ((code.map fun i => .op i.o i.a i.b i.c) ++
    [.lab 99, .zeros 1024]) 99)

def roundingImage (q r den expected : Nat) : Except String (List Runner.B) :=
  wordImage (floatRoundL 8 (fun d => some (konstWL 4 q d))
    (fun d => some (konstWL 4 r d)) (fun d => some (konstWL 4 den d))) expected

def magnitudeImage (n : Int) : Except String (List Runner.B) :=
  wordImage (floatMagnitudeL 8
    (fun d => some (konstWL 4 (BitVec.ofInt 64 n).toNat d))) n.natAbs

def shiftImage (a k expected : Nat) : Except String (List Runner.B) :=
  wordImage (floatShiftJamL 8 (fun d => some (konstWL 4 a d))
    (fun d => some (konstWL 4 k d))) expected

def scaleImage (a k expected : Nat) : Except String (List Runner.B) :=
  wordImage (floatRoundShiftL 8 (fun d => some (konstWL 4 a d))
    (fun d => some (konstWL 4 k d))) expected

/-- Expected words are explicit IEEE encodings, independently obtained by rounding
    the integer significand to 24/53 bits with ties to even, then packing sign,
    biased exponent and fraction. The kernel also checks agreement with ofInt. -/
def computedSamples : List (Gleitkomma.Format × Int × Nat) :=
  [
    (Gleitkomma.f32, 0, 0),
    (Gleitkomma.f32, 37, 1108606976),
    (Gleitkomma.f32, -37, 3256090624),
    (Gleitkomma.f32, -9223372036854775808, 3741319168),
    (Gleitkomma.f32, 9223372036854775807, 1593835520),
    (Gleitkomma.f32, 16777217, 1266679808),
    (Gleitkomma.f32, 33554431, 1275068416),
    (Gleitkomma.f32, 8388608, 1258291200),
    (Gleitkomma.f32, 9007199254740993, 1509949440),
    (Gleitkomma.f32, 18014398509481983, 1518338048),
    (Gleitkomma.f32, 4503599627370496, 1501560832),
    (Gleitkomma.f64, 0, 0),
    (Gleitkomma.f64, 37, 4630404104378646528),
    (Gleitkomma.f64, -37, 13853776141233422336),
    (Gleitkomma.f64, -9223372036854775808, 14114281232179134464),
    (Gleitkomma.f64, 9223372036854775807, 4890909195324358656),
    (Gleitkomma.f64, 16777217, 4715268810125344768),
    (Gleitkomma.f64, 33554431, 4719772409215844352),
    (Gleitkomma.f64, 8388608, 4710765210229538816),
    (Gleitkomma.f64, 9007199254740993, 4845873199050653696),
    (Gleitkomma.f64, 18014398509481983, 4850376798678024192),
    (Gleitkomma.f64, 4503599627370496, 4841369599423283200)]

theorem computedSamples_bits : computedSamples.all (fun (f, z, bits) =>
    decide (Gleitkomma.zuBits f (Gleitkomma.ofInt f z) = bits)) = true := by
  decide +kernel

/-- Execute the emitted conversion, including a real integer-producing child.
    These format-specific fragment probes complement the binary64 block-hook probes. -/
def computedImage (f : Gleitkomma.Format) (z : Int) (expected : Nat) :
    Except String (List Runner.B) :=
  wordImage (computedFloatOfL f 8
    (fun d => some (konstWL 4 (BitVec.ofInt 64 z).toNat d))) expected

def computedImages : List (String × Except String (List Runner.B) × Nat) :=
  computedSamples.zipIdx |>.map fun ((f, z, expected), i) =>
    (s!"computed-float-{i}", computedImage f z expected, 7)

/-- Real expression children exercise ordinary lowering, including its reservation. -/
def expressionImage : Except String (List Runner.B) :=
  wordImage (computedFloatOfE (layU u (fun _ => some gateBinding) 0) Gleitkomma.f64
    (Expr.add (Γ := []) (Λ := []) (.lit 19) (.lit 18)) 8 4)
    4630404104378646528

/-- Execute range rejection and the actual Stop107 exit sequence. The conversion
    producer is emitted by the ordinary expression candidate at every requested slot. -/
def rangeImage (z : Int) (lo hi : Int × Int) : Except String (List Runner.B) := do
  let cc ← match canonicalFloatRangeL 8 lo hi
      (fun d => computedFloatOfE (layU u (fun _ => some gateBinding) 0) Gleitkomma.f64
        (Expr.add (Γ := []) (Λ := [])
          (.mul (.lit (z / 1073741824)) (.lit 1073741824))
          (.lit (z % 1073741824))) d 4) with
    | some c => Except.ok c
    | none => Except.error "computed range fragment refused"
  let code := wennC 8 cc.1 (stopC 107 0) (stopC 7 0)
  pure (Runner.Prog.irImage ((code.map fun i => .op i.o i.a i.b i.c) ++
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

/-- The expected range exits agree with the source decision after rounding.
    Emission and processor execution are measured separately. -/
theorem computed_range_decisions_zeuge :
    floatRangeReject (0, 1) (100, 1) (gleitAusInt 37) = false ∧
    floatRangeReject (0, 1) (100, 1) (gleitAusInt 0) = false ∧
    floatRangeReject (0, 1) (100, 1) (gleitAusInt 100) = false ∧
    floatRangeReject (0, 1) (100, 1) (gleitAusInt (-1)) = true ∧
    floatRangeReject (0, 1) (100, 1) (gleitAusInt 101) = true ∧
    floatRangeReject (0, 1) (0, 0) (gleitAusInt 0) = true ∧
    floatRangeReject (2^1024, 1) (2^1024, 1) (gleitAusInt 37) = true ∧
    floatRangeReject (-(2^1024), 1) (-(2^1024), 1) (gleitAusInt (-37)) = true := by
  decide +kernel

def images : List (String × Except String (List Runner.B) × Nat) :=
  [("scale-zero", scaleImage 0 0 0, 7),
   ("scale-full-word", scaleImage (2^64 - 1) 0 (2^64 - 1), 7),
   ("scale-tie-odd", scaleImage 15 1 8, 7),
   ("scale-tie-even", scaleImage 13 1 6, 7),
   ("scale-two-odd", scaleImage 14 2 4, 7),
   ("scale-two-even", scaleImage 10 2 2, 7),
   ("scale-signed-min-magnitude", scaleImage (2^63) 11 (2^52), 7),
   ("scale-significand-carry", scaleImage (2^64 - 1) 11 (2^53), 7),
   ("scale-large-den-tie-even", scaleImage (2^63 + 2^61) 62 2, 7),
   ("scale-large-den-tie-odd", scaleImage (3 * 2^62 + 2^61) 62 4, 7),
   ("scale-kernel-normal", scaleImage (2^53 + 3) 1 (2^52 + 2), 7),
   ("shift-zero", shiftImage 11 0 11, 7),
   ("shift-exact", shiftImage 12 1 6, 7),
   ("shift-sticky", shiftImage 13 1 7, 7),
   ("shift-odd", shiftImage 11 1 5, 7),
   ("shift-small", shiftImage 1 63 1, 7),
   ("shift-high-bit", shiftImage (2^63) 1 (2^62), 7),
   ("shift-full-word", shiftImage (2^64 - 1) 1 (2^63 - 1), 7),
   ("shift-63-exact", shiftImage (2^63) 63 1, 7),
   ("shift-63-sticky", shiftImage (2^63 + 1) 63 1, 7),
   ("shift-64-zero", shiftImage 0 64 0, 7),
   ("shift-64", shiftImage 12 64 1, 7),
   ("shift-65", shiftImage 12 65 1, 7),
   ("shift-subnormal-distance", shiftImage 42 1074 1, 7),
   ("shift-high-count", shiftImage 42 (2^63) 1, 7),
   ("shift-max-count", shiftImage 42 (2^64 - 1) 1, 7),
   ("magnitude-zero", magnitudeImage 0, 7),
   ("magnitude-negative", magnitudeImage (-42), 7),
   ("magnitude-positive", magnitudeImage 42, 7),
   ("magnitude-signed-min", magnitudeImage (-2^63), 7),
   ("magnitude-signed-max", magnitudeImage (2^63 - 1), 7),
   ("round-below-half", roundingImage 4 1 4 4, 7),
   ("round-above-half", roundingImage 4 3 4 5, 7),
   ("round-tie-even", roundingImage 4 1 2 4, 7),
   ("round-tie-odd", roundingImage 5 1 2 6, 7),
   ("round-exact", roundingImage 5 0 4 5, 7),
   ("round-significand-carry", roundingImage (2^53 - 1) 3 4 (2^53), 7),
   ("round-large-remainder", roundingImage 7 (2^63 - 2) (2^63 - 1) 8, 7),
   ("round-high-quotient", roundingImage (2^63 + 1) 1 2 (2^63 + 2), 7),
   ("round-word-wrap", roundingImage (2^64 - 1) 1 2 0, 7),
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

/-- All fixtures lower into complete images; real-runner execution is a separate check. -/
theorem float_arithmetic_images_zeuge : images.all (fun x => x.2.1.isOk) = true := by
  decide +kernel

/-- The exact add/sub edge semantics still required of a complete software routine.
    These model checks do not claim that add/sub images have been lowered. -/
theorem float_add_sub_model_zeuge :
    Gleitkomma.add Gleitkomma.f64 ⟨true, 0, 0⟩ ⟨true, 0, 0⟩ = ⟨true, 0, 0⟩ ∧
    Gleitkomma.add Gleitkomma.f64 ⟨false, 0, 0⟩ ⟨true, 0, 0⟩ = ⟨false, 0, 0⟩ ∧
    Gleitkomma.add Gleitkomma.f64 ⟨false, 0, 1⟩ ⟨false, 0, 1⟩ = ⟨false, 0, 2⟩ ∧
    Gleitkomma.sub Gleitkomma.f64 ⟨false, 0, 1⟩ ⟨false, 0, 1⟩ = ⟨false, 0, 0⟩ ∧
    Gleitkomma.sub Gleitkomma.f64 ⟨true, 0, 0⟩ ⟨false, 0, 0⟩ = ⟨true, 0, 0⟩ ∧
    Gleitkomma.sub Gleitkomma.f64 ⟨false, 1, 0⟩ ⟨false, 0, 2^52 - 1⟩ = ⟨false, 0, 1⟩ ∧
    Gleitkomma.add Gleitkomma.f64 ⟨false, 1023, 0⟩ ⟨false, 970, 0⟩ = ⟨false, 1023, 0⟩ ∧
    Gleitkomma.add Gleitkomma.f64 ⟨false, 1023, 1⟩ ⟨false, 970, 0⟩ = ⟨false, 1023, 2⟩ ∧
    Gleitkomma.sub Gleitkomma.f64 ⟨false, 1023, 0⟩ ⟨false, 969, 0⟩ = ⟨false, 1023, 0⟩ ∧
    Gleitkomma.add Gleitkomma.f64 ⟨false, 2047, 0⟩ ⟨true, 2047, 0⟩ = ⟨false, 2047, 1⟩ ∧
    Gleitkomma.sub Gleitkomma.f64 ⟨false, 2047, 0⟩ ⟨false, 2047, 0⟩ = ⟨false, 2047, 1⟩ ∧
    Gleitkomma.add Gleitkomma.f64 ⟨true, 2047, 7⟩ ⟨false, 2047, 9⟩ = ⟨true, 2047, 7⟩ ∧
    Gleitkomma.sub Gleitkomma.f64 ⟨false, 0, 0⟩ ⟨true, 2047, 9⟩ = ⟨false, 2047, 9⟩ ∧
    Gleitkomma.add Gleitkomma.f64 ⟨false, 2046, 2^52 - 1⟩ ⟨false, 2046, 2^52 - 1⟩ =
      ⟨false, 2047, 0⟩ := by decide +kernel

/-- No operation is silently accepted while only its rounding fragment is proved. -/
theorem float_operations_refused_zeuge :
    [GleitOp.add, .sub, .mul, .div].all (fun op =>
      !(blockImageOf (show Body from .floatLit (1, 1) (0, 1) (10, 1)
        (.float op (.var .here) (.var .here) (0, 1) (10, 1) .nil))).isOk) = true := by
  decide +kernel

end Gabbro.Stage0.Senke.FloatArithmeticProbe
