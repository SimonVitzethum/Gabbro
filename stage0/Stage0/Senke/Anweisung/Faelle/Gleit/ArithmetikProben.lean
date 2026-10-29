/- Arithmetic foundations: executable rounding and literal-conversion images.
   General conversion and float arithmetic remain outside the accepted fragment. -/
import Stage0.Senke.Anweisung.Faelle.Gleit.Proben
import Stage0.Senke.Ausdruck.Gleit.RundCode
import Stage0.Senke.Ausdruck.Gleit.Betrag
import Stage0.Senke.Ausdruck.Gleit.Schieben

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

def images : List (String × Except String (List Runner.B) × Nat) :=
  [("shift-zero", shiftImage 11 0 11, 7),
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
