/- Accepted division through the public Block hook and retained-word routine.
   Expected results are explicit binary64 words; runner execution is separate. -/
module
public import Stage0.Senke.Anweisung.Faelle.Gleit.ArithmetikProben
@[expose] public section

namespace Gabbro.Stage0.Senke.FloatArithmeticProbe
open Gabbro.Grammatik FloatProbe ControlProbe Runner.IR
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- The same shared operand retention used by the public Block hook. Raw
    words additionally exercise nonfinite outputs and preserve zero signs. -/
def divisionImage (a b expected : Nat) : Except String (List Runner.B) :=
  wordImage (floatWordsL .div 8 (fun d => some (konstWL 4 a d))
    (fun d => some (konstWL 4 b d))) expected

/-- Exit 7 checks the arithmetic result. Source nonfinite results use 107;
    raw-word special-case images still return 7 after checking their native value class or non-NaN word. -/
def divisionImages : List (String × Except String (List Runner.B) × Nat) :=
  [("float-div-normal", blockImageOf (binaryArithmetic .div (3, 1) (2, 1) (3, 2)), 7),
   ("float-div-rounding", blockImageOf (binaryArithmetic .div (1, 1) (3, 1) (1, 3)), 7),
   ("float-div-subnormal", blockImageOf
      (binaryArithmetic .div (1, 2 ^ 1022) (2, 1) (1, 2 ^ 1023)), 7),
   ("float-div-zero-source", blockImageOf (binaryArithmetic .div (1, 1) (0, 1) (0, 1)), 107),
   ("float-div-invalid-source", blockImageOf (binaryArithmetic .div (0, 1) (0, 1) (0, 1)), 107),
   ("float-div-infinity", divisionImage 4607182418800017408 0 9218868437227405312, 7),
   ("float-div-invalid", divisionImage 0 0 9218868437227405313, 7),
   ("float-div-negative-zero", divisionImage 9223372036854775808 4607182418800017408
      9223372036854775808, 7),
   ("float-div-negative-infinity", divisionImage 4607182418800017408 9223372036854775808
      18442240474082181120, 7),
   ("float-div-finite-over-infinity", divisionImage 4607182418800017408 18442240474082181120
      9223372036854775808, 7),
   ("float-div-infinity-over-infinity", divisionImage 9218868437227405312 9218868437227405312
      9218868437227405313, 7),
   ("float-div-least-subnormal", divisionImage 1 4607182418800017408 1, 7),
   ("float-div-underflow-tie-even", divisionImage 1 4611686018427387904 0, 7),
   ("float-div-underflow-tie-odd", divisionImage 3 4611686018427387904 2, 7),
   ("float-div-nan-left", divisionImage 18442240474082181127 9218868437227405321
      18442240474082181127, 7),
   ("float-div-nan-right", divisionImage 4607182418800017408 18442240474082181129
      18442240474082181129, 7)]

end Gabbro.Stage0.Senke.FloatArithmeticProbe
