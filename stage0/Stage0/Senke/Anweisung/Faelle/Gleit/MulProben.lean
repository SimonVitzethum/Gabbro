/- Accepted multiplication images through the Block hook and retained words.
   Word checks retain zero signs; unordered results are checked by native NaN class.
   Images are fixtures for the assembly runner; they do not execute here. -/
module
public import Stage0.Senke.Anweisung.Faelle.Gleit.ArithmetikProben
@[expose] public section

namespace Gabbro.Stage0.Senke.FloatArithmeticProbe
open Gabbro.Grammatik FloatProbe ControlProbe Runner.IR
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The same retained-input pipeline is used by Block emission. This lower
    interface additionally admits nonfinite words, for the dispatcher tests. -/
def multiplicationImage (a b expected : Nat) : Except String (List Runner.B) :=
  wordImage (floatWordsL .mul 8 (fun d => some (konstWL 4 a d))
    (fun d => some (konstWL 4 b d))) expected

/-- Execution images for the assembly runner. Expected exit 7 means that
    both Block comparisons or the exact result-word comparison succeeded. -/
def multiplicationImages : List (String × Except String (List Runner.B) × Nat) :=
  [("float-mul-normal", blockImageOf (binaryArithmetic .mul (3, 2) (2, 1) (3, 1)), 7),
   ("float-mul-rounding", blockImageOf
      (binaryArithmetic .mul (2 ^ 52 + 1, 2 ^ 52) (2 ^ 52 + 1, 2 ^ 52) (2 ^ 51 + 1, 2 ^ 51)), 7),
   ("float-mul-subnormal", blockImageOf (binaryArithmetic .mul (1, 2 ^ 1022) (1, 2) (1, 2 ^ 1023)), 7),
   ("float-mul-invalid", multiplicationImage 0 9218868437227405312 9218868437227405313, 7),
   ("float-mul-negative-zero", multiplicationImage 9223372036854775808 4607182418800017408
      9223372036854775808, 7),
   ("float-mul-negative-underflow", multiplicationImage 9223372036854775809 1 9223372036854775808, 7),
   ("float-mul-nan-left", multiplicationImage 18442240474082181127 9218868437227405321
      18442240474082181127, 7),
   ("float-mul-nan-right", multiplicationImage 4607182418800017408 18442240474082181129
      18442240474082181129, 7),
   ("float-mul-overflow", multiplicationImage 9218868437227405311 4611686018427387904
      9218868437227405312, 7),
   ("float-mul-smallest-normal", multiplicationImage 4503599627370495 4607182418800017409
      4503599627370496, 7)]

/-- Source bounds apply after multiplication rounding. A product outside
    its declared interval uses the common stop-107 path. -/
def multiplicationRange : Body :=
  .floatLit (2, 1) (0, 1) (10, 1)
    (.float .mul (.var .here) (.var .here) (0, 1) (3, 1)
      (returnBlock 41 (by decide) (by decide)))

end Gabbro.Stage0.Senke.FloatArithmeticProbe
