/- Emitted runner images for the shared arithmetic operand preparation. -/
import Stage0.Senke.Ausdruck.Arithmetik.Simulation
import Stage0.Senke.BildLese
import Stage0.Senke.Anweisung.Faelle.Gleit.ArithmetikProben

namespace Gabbro.Stage0.Senke.AddSubProbe
open Gabbro.Grammatik Runner.IR Gleitkomma

/-- Actual backward-branch loop images; output slots are checked independently.
    The 1074 case takes 1127 transfers before recovering 53 quotient bits. -/
def normalizationLoopImages : List (String × Except String (List Runner.B) × Nat) :=
  [("precision24-distance149", 0, 1, 149, 2^24, 173, 2^24, 0, 173),
   ("precision60-distance0", 1, 0, 0, 2^60, 60, 2^60, 0, 60),
   ("below61", 0, 2^61-1, 61, 8, 1, 1, 2^61-2, 1),
   ("below62", 0, 2^61-1, 62, 8, 1, 0, 2^61-1, 1),
   ("above62", 0, 2^61+1, 62, 8, 1, 1, 1, 1),
   ("maximum63", 0, 2^63-1, 63, 8, 1, 1, 2^62-1, 1),
   ("maximum64", 0, 2^63-1, 64, 8, 1, 0, 2^63-1, 1),
   ("zeroFuel62", 0, 2^61, 62, 8, 0, 0, 2^61, 0),
   ("stopped62", 8, 2^61, 62, 8, 1, 8, 2^61, 0),
   ("boundary61", 0, 2^60, 61, 8, 1, 1, 0, 1),
   ("boundary62", 0, 2^61, 62, 8, 1, 1, 0, 1),
   ("boundary63", 0, 2^62, 63, 8, 1, 1, 0, 1),
   ("tail63", 0, 2^61, 63, 8, 2, 1, 0, 2),
   ("numerator-entry", 0, 13, 4, 8, 68, 13, 0, 4),
   ("four", 0, 13, 4, 8, 20, 13, 0, 4),
   ("distance62", 0, 1, 62, 8, 70, 8, 0, 65),
   ("distance65", 0, 13, 65, 8, 80, 13, 0, 65),
   ("distance1074", 0, 1, 1074, 2^53, 1127, 2^53, 0, 1127),
   ("floor1074", 0, 13, 1074, 0, 1127, 0, 13, 0),
   ("early1074", 1, 13, 1074, 8, 1127, 8, 13, 3),
   ("fuel1074", 0, 13, 1074, 8, 1000, 0, 13, 1000)].flatMap
    fun (name, q, r, k, target, fuel, qo, ro, count) =>
      [(0, qo), (1, ro), (2, if 61 < k then max 61 (k-count) else k),
       (4, fuel-count), (5, count)].map fun (field, expected) =>
        let fragment := do
          let loop ← floatNormalizeLoopL 16
          let init := (konstWL 4 q 16).1 ++ (konstWL 4 r 17).1 ++
            (konstWL 4 k 18).1 ++ (konstWL 4 target 19).1 ++
            (konstWL 4 fuel 20).1 ++ [ci 1 21 0 0]
          pure (init ++ loop.1 ++ [ci 2 8 (16+field) 0], loop.2)
        ("normalize-loop-" ++ name ++ "-" ++ toString field,
          FloatArithmeticProbe.wordImage fragment expected, 7)

/-- All boundary fixtures use the production loop and encode successfully;
    actual execution is measured separately by the runner regression. -/
theorem normalizationLoopImages_zeuge : normalizationLoopImages.length = 105 ∧
    normalizationLoopImages.all (fun x => x.2.1.isOk) = true := by
  decide +kernel

#print axioms normalizationLoopImages_zeuge

/-- Actual exact-tail adaptive normalization; check each output independently. -/
def adaptiveImages : List (String × Except String (List Runner.B) × Nat) :=
  let lit := fun n j => some (konstWL 4 n j)
  [("tiny", 0, 13, 16, 8, 1, 10),
   ("carry", 1, 10, 16, 8, 3, 4),
   ("below", 3, 4, 16, 8, 6, 8),
   ("tie", 6, 8, 16, 8, 13, 0),
   ("floor", 0, 13, 16, 0, 0, 13),
   ("stop", 8, 3, 16, 8, 8, 3),
   ("exact", 7, 0, 16, 8, 14, 0),
   ("wide", 2^61, 2^61-2, 2^61-1, 2^61+1, 2^62+1, 2^61-3)].flatMap
    (fun (name, q, r, den, target, qout, rout) =>
      [false, true].map fun out =>
        ("adaptive-" ++ name ++ (if out then "-rest" else "-magnitude"),
          FloatArithmeticProbe.wordImage
            (floatNormalizeStepL out 8 (lit q) (lit r) (lit den) (lit target))
            (if out then rout else qout), 7))

/-- Actual alignment-to-magnitude images, including borrow after cancellation. -/
def sumMagnitudeImages : List (String × Except String (List Runner.B) × Nat) :=
  let lit := fun n j => some (konstWL 4 n j)
  [("sum-magnitude-positive", 10, 13, 2, 1, 6),
   ("sum-magnitude-negative", 2^64-10, 13, 2, 1, 13),
   ("sum-magnitude-exact", 0, 16, 2, 0, 4),
   ("sum-magnitude-cancel", 4, 16, 2, 0, 0),
   ("sum-magnitude-tiny", 0, 13, 1074, 1, 0),
   ("sum-magnitude-above-word", 7, 13, 65, 1, 6),
   ("sum-magnitude-negative-tail", 2^64-7, 13, 65, 1, 7)].map
    (fun (name, h, a, k, sticky, expected) =>
      (name, FloatArithmeticProbe.wordImage
        (floatSumMagnitudeL 8
          (fun j => floatNegativeSumL j (lit h) (lit a) (lit k))
          (lit sticky)) expected, 7)) ++
  [("operand-magnitude-subnormal-cancel", 0x800fffffffffffff, 0x0010000000000000, 0, 1),
   ("operand-magnitude-negative", 0xbff0000000000009, 0x3ff0000000000000, 0, 9),
   ("operand-magnitude-shift", 0x0000000000000001, 0x0000000000000003, 2, 13)].map
    (fun (name, a, b, k, expected) =>
      (name, FloatArithmeticProbe.wordImage
        (floatSumMagnitudeL 8
          (fun j => floatAlignSumL j
            (fun n => floatCoefficientL n (lit a))
            (fun n => floatCoefficientL n (lit b)) (lit k))
          (lit 0)) expected, 7))

/-- Actual output fragments, including the top-exponent carry and the
    subnormal/normal boundary. Expected words are independent IEEE fields. -/
def outputImages : List (String × Except String (List Runner.B) × Nat) :=
  let lit := fun n j => some (konstWL 4 n j)
  let normal :=
    [("output-normal-exact", 0, 1023, 2^52, 0, 0, 0x3ff0000000000000),
     ("output-normal-even", 0, 1023, 2^52, 4, 0, 0x3ff0000000000000),
     ("output-normal-odd", 0, 1023, 2^52+1, 4, 0, 0x3ff0000000000002),
     ("output-normal-tail", 0, 1023, 2^52, 4, 1, 0x3ff0000000000001),
     ("output-normal-carry", 0, 1023, 2^53-1, 4, 0, 0x4000000000000000),
     ("output-normal-negative", 2^63, 1023, 2^52, 5, 0, 0xbff0000000000001),
     ("output-max-finite", 0, 2046, 2^53-1, 3, 1, 0x7fefffffffffffff),
     ("output-overflow", 0, 2046, 2^53-1, 4, 0, 0x7ff0000000000000),
     ("output-overflow-negative", 2^63, 2046, 2^53-1, 4, 1, 0xfff0000000000000)].map
      (fun (name, s, e, q, g, t, expected) =>
        (name, FloatArithmeticProbe.wordImage
          (floatAddNormalOutputL 8 (lit s) (lit e) (lit q) (lit g) (lit t) (2^52)) expected, 7))
  let tiny :=
    [("output-positive-zero", 0, 0, 0, 0, 0),
     ("output-negative-zero", 2^63, 0, 0, 0, 2^63),
     ("output-zero-even-tie", 0, 0, 4, 0, 0),
     ("output-zero-tiny-tail", 0, 0, 4, 1, 1),
     ("output-subnormal-even", 0, 2, 4, 0, 2),
     ("output-subnormal-odd", 0, 1, 4, 0, 2),
     ("output-max-subnormal", 0, 2^52-1, 3, 1, 2^52-1),
     ("output-min-normal", 0, 2^52-1, 4, 0, 2^52),
     ("output-negative-min-normal", 2^63, 2^52-1, 4, 1, 2^63+2^52)].map
      (fun (name, s, q, g, t, expected) =>
        (name, FloatArithmeticProbe.wordImage
          (floatAddSubnormalOutputL 8 (lit s) (lit q) (lit g) (lit t)) expected, 7))
  normal ++ tiny

theorem outputImages_zeuge : outputImages.length = 18 ∧
    outputImages.all (fun x => x.2.1.isOk) = true := by
  decide +kernel

/-- Non-degenerate joint fixtures for emitted rounding and packing, including
    a halfway normal, an overflow carry and a halfway subnormal rounding to zero. -/
theorem floatAddOutput_joint_zeuge [Kern] {D : Deklaration} (L : Lay D) :
    let lit := fun n j => some (konstWL 4 n j)
    WordCode (L := L) (Env.nil : Env D []) (fun _ => True)
      (fun dst => floatAddNormalOutputL dst (lit 0) (lit 1078)
        (lit (2^52)) (lit 4) (lit 0) (2^52))
      (BitVec.ofNat 64 (zuBits f64 (rundeBruchKern f64 false (2^55+4) 1 55))) ∧
    WordCode (L := L) (Env.nil : Env D []) (fun _ => True)
      (fun dst => floatAddNormalOutputL dst (lit (2^63)) (lit 2046)
        (lit (2^53-1)) (lit 4) (lit 0) (2^52))
      (BitVec.ofNat 64 0xfff0000000000000) ∧
    WordCode (L := L) (Env.nil : Env D []) (fun _ => True)
      (fun dst => floatAddSubnormalOutputL dst (lit 0) (lit 0) (lit 4) (lit 0))
      (BitVec.ofNat 64 (zuBits f64 (rundeBruchKern f64 false 1 (2^1075) (-1075)))) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · apply floatAddNormalOutputL_ok f64 false (2^55+4) 1 (2^52) 4 0 1 55
    all_goals first | exact WordCode.konst _ (by decide +kernel) | decide +kernel
  · intro fp K dst code top hc hK m pc hp
    exact floatAddNormalOutputL_top_f64 (L := L) (ρ := (Env.nil : Env D []))
      (W := fun _ => True) true (2^53-1) 4 0 1
      (WordCode.konst _ (by decide)) (WordCode.konst _ (by decide))
      (WordCode.konst _ (by decide)) (WordCode.konst _ (by decide))
      (WordCode.konst _ (by decide)) (by decide) (by decide) (by decide) (by decide +kernel)
      hc hK m pc hp
  · apply floatAddSubnormalOutputL_ok f64 false 1 (2^1075) 0 4 0 (2^1072) (-1075)
    all_goals first | exact WordCode.konst _ (by decide +kernel) | decide +kernel

/-- These images call the production fragment; they do not implement an
    alternate negation or special-case particular source programs. -/
def images : List (String × Except String (List Runner.B) × Nat) :=
  [("addsub-neg-positive-zero", 0, 0x8000000000000000),
   ("addsub-neg-negative-zero", 0x8000000000000000, 0),
   ("addsub-neg-positive-one", 0x3ff0000000000000, 0xbff0000000000000),
   ("addsub-neg-negative-one", 0xbff0000000000000, 0x3ff0000000000000),
   ("addsub-neg-subnormal", 1, 0x8000000000000001),
   ("addsub-neg-infinity", 0x7ff0000000000000, 0xfff0000000000000),
   ("addsub-neg-nan-payload", 0xfff0000000000009, 0x7ff0000000000009),
   ("addsub-neg-max-finite", 0x7fefffffffffffff, 0xffefffffffffffff)].map
    (fun (name, input, expected) =>
      (name, FloatArithmeticProbe.wordImage
        (floatNegL 8 (fun d => some (konstWL 4 input d))) expected, 7))

/-- The same extractor covers normal, subnormal and special bit patterns. -/
def fieldImages : List (String × Except String (List Runner.B) × Nat) :=
  [("addsub-field-normal-exponent", 0x3ff0000000000000, 52, 11, 1023),
   ("addsub-field-normal-fraction", 0x3ff0000000000009, 0, 52, 9),
   ("addsub-field-negative-exponent", 0xbff0000000000000, 52, 11, 1023),
   ("addsub-field-subnormal-exponent", 1, 52, 11, 0),
   ("addsub-field-subnormal-fraction", 1, 0, 52, 1),
   ("addsub-field-infinity-exponent", 0x7ff0000000000000, 52, 11, 2047),
   ("addsub-field-nan-payload", 0xfff0000000000009, 0, 52, 9),
   ("addsub-field-sign", 0xfff0000000000009, 63, 1, 1)].map
    (fun (name, input, offset, width, expected) =>
      (name, FloatArithmeticProbe.wordImage
        (floatFieldL offset width 8 (fun d => some (konstWL 4 input d))) expected, 7))

/-- Production coefficient decoding at the normal/subnormal and sign edges. -/
def coefficientImages : List (String × Except String (List Runner.B) × Nat) :=
  [("coefficient-positive-zero", 0, 0),
   ("coefficient-negative-zero", 0x8000000000000000, 0),
   ("coefficient-min-subnormal", 1, 1),
   ("coefficient-negative-min-subnormal", 0x8000000000000001, 2^64-1),
   ("coefficient-max-subnormal", 0x000fffffffffffff, 2^52-1),
   ("coefficient-min-normal", 0x0010000000000000, 2^52),
   ("coefficient-negative-normal", 0xbff0000000000009, 2^64-(2^52+9)),
   ("coefficient-max-finite", 0x7fefffffffffffff, 2^53-1)].map
    (fun (name, input, expected) =>
      (name, FloatArithmeticProbe.wordImage
        (floatCoefficientL 8 (fun d => some (konstWL 4 input d))) expected, 7))

/-- Actual coefficient extraction, exact alignment and signed sum together. -/
def alignmentImages : List (String × Except String (List Runner.B) × Nat) :=
  [("align-cancel", 0xbff0000000000000, 0x3ff0000000000000, 0, 0),
   ("align-different-exponents", 0x3fe0000000000000, 0x3ff0000000000000, 1, 3*2^52),
   ("align-negative-result", 0x3fe0000000000000, 0xbff0000000000000, 1, 2^64-2^52),
   ("align-subnormal-cancel", 0x800fffffffffffff, 0x0010000000000000, 0, 1),
   ("align-negative-subnormal", 0x000fffffffffffff, 0x8010000000000000, 0, 2^64-1),
   ("align-carry", 0x3fffffffffffffff, 0x3fffffffffffffff, 0, 2^54-2),
   ("align-zero", 0x8000000000000000, 0x0000000000000001, 0, 1)].map
    (fun (name, lo, hi, k, expected) =>
      (name, FloatArithmeticProbe.wordImage
        (floatAlignSumL 8
          (fun d => floatCoefficientL d (fun j => some (konstWL 4 lo j)))
          (fun d => floatCoefficientL d (fun j => some (konstWL 4 hi j)))
          (fun d => some (konstWL 4 k d))) expected, 7))

/-- Connected sum boundary images retain cancellation tails independently. -/
def negativeSumImages : List (String × Except String (List Runner.B) × Nat) :=
  [("negative-sum-cancel", 7, 14, 1, 0),
   ("negative-sum-positive-tail", 7, 13, 1, 0),
   ("negative-sum-negative-tail", 6, 13, 1, 2^64-1),
   ("negative-sum-zero", 0, 0, 1074, 0),
   ("negative-sum-63", 1, 13, 63, 0),
   ("negative-sum-64", 1, 13, 64, 0),
   ("negative-sum-65", 1, 13, 65, 0),
   ("negative-sum-1074", 1, 13, 1074, 0),
   ("negative-sum-maxcount", 1, 13, 2^64-1, 0),
   ("negative-sum-lower", 2^64-2^61, 2^61, 0, 2^64-2^62)].map
    (fun (name, hi, a, k, expected) =>
      (name, FloatArithmeticProbe.wordImage
        (floatNegativeSumL 8 (fun d => some (konstWL 4 hi d))
          (fun d => some (konstWL 4 a d))
          (fun d => some (konstWL 4 k d))) expected, 7))

theorem negativeSumImages_zeuge : negativeSumImages.length = 10 ∧
    negativeSumImages.all (fun x => x.2.1.isOk) = true := by
  decide +kernel

/-- One emitted sum simultaneously satisfies producer premises, exact signed
    interpretation and reconstruction of a positive cancellation tail. -/
theorem floatNegativeSumL_joint_zeuge [Kern] {D : Deklaration} (L : Lay D) :
    WordCode (L := L) (Env.nil : Env D []) (fun _ => True)
      (fun d => floatNegativeSumL d (fun j => some (konstWL 4 7 j))
        (fun j => some (konstWL 4 13 j)) (fun j => some (konstWL 4 1 j)))
      (BitVec.ofInt 64 (7 + (-(13 : Int)) / 2)) ∧
    (-(2^61 : Int) ≤ 7 ∧ (7 : Int) ≤ 2^61) ∧
    (13 : Nat) ≤ 2^61 ∧
    (BitVec.ofInt 64 (7 + (-(13 : Int)) / 2)).toInt = 0 ∧
    7 * (2 : Int) - 13 = 0 * 2 + (-(13 : Int)) % 2 := by
  refine ⟨?_, by decide, by decide, by decide, by decide⟩
  exact floatNegativeSumL_ok (WordCode.konst 7 (by decide))
    (WordCode.konst 13 (by decide)) (WordCode.konst 1 (by decide))

/-- Actual signed alignment at large exponent distances, using saturating
    shifts and an independently preserved tail. Counts never wrap at 64. -/
def negativeShiftImages : List (String × Except String (List Runner.B) × Nat) :=
  [("negative-shift-exact", 12, 1, 2^64-6),
   ("negative-shift-borrow", 13, 1, 2^64-7),
   ("negative-shift-zero", 0, 1074, 0),
   ("negative-shift-63-exact", 2^63, 63, 2^64-1),
   ("negative-shift-63-tail", 2^63+1, 63, 2^64-2),
   ("negative-shift-64", 13, 64, 2^64-1),
   ("negative-shift-65", 13, 65, 2^64-1),
   ("negative-shift-1074", 13, 1074, 2^64-1),
   ("negative-shift-maxcount", 13, 2^64-1, 2^64-1)].map
    (fun (name, a, k, expected) =>
      (name, FloatArithmeticProbe.wordImage
        (floatNegativeShiftL 8 (fun d => some (konstWL 4 a d))
          (fun d => some (konstWL 4 k d))) expected, 7))

theorem negativeShiftImages_zeuge : negativeShiftImages.length = 9 ∧
    negativeShiftImages.all (fun x => x.2.1.isOk) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 2048 in
/-- At a subnormal-scale distance the exact negative quotient is minus one;
    the code, canonical quotient and producer premises hold together. -/
theorem floatNegativeShiftL_joint_zeuge [Kern] {D : Deklaration} (L : Lay D) :
    (-(13 : Int)) / (2^1074 : Nat) = -1 ∧
    (13 : Nat) % 2^1074 = 13 ∧
    WordCode (L := L) (Env.nil : Env D []) (fun _ => True)
      (fun d => floatNegativeShiftL d (fun j => some (konstWL 4 13 j))
        (fun j => some (konstWL 4 1074 j))) (BitVec.ofInt 64 (-1)) ∧
    ∃ c, floatNegativeShiftL 8 (fun j => some (konstWL 4 13 j))
      (fun j => some (konstWL 4 1074 j)) = some (c, 14) ∧ c.length = 157 := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, ?_⟩
  · have result : WordCode (L := L) (Env.nil : Env D []) (fun _ => True) _ _ :=
      floatNegativeShiftL_ok (WordCode.konst 13 (by decide))
        (WordCode.konst 1074 (by decide))
    have hv : (-(13 : Int)) / (2^1074 : Nat) = -1 := by decide +kernel
    intro fp K d c top hc hK m pc hp
    apply (result hc hK m pc hp).mono
    intro w hw
    change w = BitVec.ofInt 64 ((-(13 : Int)) / (2^1074 : Nat)) at hw
    exact hw.trans (congrArg (BitVec.ofInt 64) hv)

  · refine ⟨((floatNegativeShiftL 8 (fun j => some (konstWL 4 13 j))
        (fun j => some (konstWL 4 1074 j))).getD ([], 0)).1, ?_, ?_⟩ <;> decide +kernel

/-- Negative alignment executes the production borrow rather than rounding a
    negated sticky operand. Zero, exact, tiny and wide quotients are covered. -/
def negativeQuotImages : List (String × Except String (List Runner.B) × Nat) :=
  [("negative-quot-zero", 0, 0, 0),
   ("negative-quot-tiny", 0, 1, 2^64-1),
   ("negative-quot-exact", 6, 0, 2^64-6),
   ("negative-quot-borrow", 6, 1, 2^64-7),
   ("negative-quot-wide", 2^52, 1, 2^64-2^52-1)].map
    (fun (name, q, sticky, expected) =>
      (name, FloatArithmeticProbe.wordImage
        (floatNegativeQuotL 8 (fun d => some (konstWL 4 q d))
          (fun d => some (konstWL 4 sticky d))) expected, 7))

theorem negativeQuotImages_zeuge : negativeQuotImages.length = 5 ∧
    negativeQuotImages.all (fun x => x.2.1.isOk) = true := by
  decide +kernel

/-- The borrow and exact signed tail jointly describe cancellation to one
    unit; the actual emitted fragment has its simulation and exact sizes. -/
theorem floatNegativeQuotL_joint_zeuge [Kern] {D : Deklaration} (L : Lay D) :
    (-(13 : Int)) / 2 = -7 ∧ (-(13 : Int)) % 2 = 1 ∧
    7 * (2 : Int) - 13 = (7 + -7) * 2 + 1 ∧
    WordCode (L := L) (Env.nil : Env D []) (fun _ => True)
      (fun d => floatNegativeQuotL d (fun j => some (konstWL 4 6 j))
        (fun j => some (konstWL 4 1 j))) (BitVec.ofInt 64 (-7)) ∧
    ∃ c, floatNegativeQuotL 8 (fun j => some (konstWL 4 6 j))
      (fun j => some (konstWL 4 1 j)) = some (c, 11) ∧ c.length = 37 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact floatNegativeQuotL_ok 13 2 (by decide)
      (WordCode.konst 6 (by decide)) (WordCode.konst 1 (by decide))
  · refine ⟨((floatNegativeQuotL 8 (fun j => some (konstWL 4 6 j))
        (fun j => some (konstWL 4 1 j))).getD ([], 0)).1, ?_, ?_⟩ <;> decide +kernel

/-- The production rounding fragment checks exact ties, tails at distance 1074,
    the significand carry, and both sides of the halfway boundary. -/
def guardImages : List (String × Except String (List Runner.B) × Nat) :=
  [("guard-tie-even", 4, 4, 0, 4),
   ("guard-tie-odd", 5, 4, 0, 6),
   ("guard-tiny-tail", 4, 4, 1, 5),
   ("guard-below", 5, 3, 1, 5),
   ("guard-above", 4, 5, 0, 5),
   ("guard-carry", 2^53-1, 4, 1, 2^53),
   ("guard-exact", 2^52, 0, 0, 2^52)].map
    (fun (name, q, g, sticky, expected) =>
      (name, FloatArithmeticProbe.wordImage
        (floatGuardRoundL 8 (fun d => some (konstWL 4 q d))
          (fun d => some (konstWL 4 g d))
          (fun d => some (konstWL 4 sticky d))) expected, 7))

theorem guardImages_zeuge : guardImages.length = 7 ∧
    guardImages.all (fun x => x.2.1.isOk) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 2048 in
/-- The unbounded-distance mathematical input and actual emitted simulation
    have jointly satisfiable premises on a value just above a halfway tie. -/
theorem floatGuardRoundL_joint_zeuge [Kern] {D : Deklaration} (L : Lay D) :
    0 < (2^1074 : Nat) ∧ 1 < (2^1074 : Nat) ∧ (4 : Nat) < 8 ∧
    rundeInt 4 (4 * 2^1074 + 1) (8 * 2^1074) = 5 ∧
    WordCode (L := L) (Env.nil : Env D []) (fun _ => True)
      (fun d => floatGuardRoundL d
        (fun j => some (konstWL 4 4 j))
        (fun j => some (konstWL 4 4 j))
        (fun j => some (konstWL 4 1 j))) 5 := by
  refine ⟨by decide, by decide, by decide, by decide +kernel, ?_⟩
  have hround : rundeInt 4 (4 * 2^1074 + 1) (8 * 2^1074) = 5 := by decide +kernel
  change WordCode (L := L) (Env.nil : Env D []) (fun _ => True) _ (BitVec.ofNat 64 5)
  rw [← hround]
  exact floatGuardRoundL_ok 4 4 1 (2^1074) (by decide) (by decide) (by decide)
    (WordCode.konst 4 (by decide)) (WordCode.konst 4 (by decide))
    (WordCode.konst 1 (by decide))

/-- One fixture joins the real connected producer, its simulation, exact
    footprint ceiling and cancellation across the normal/subnormal boundary. -/
theorem floatAlignSumL_joint_zeuge [Kern] {D : Deklaration} (L : Lay D) :
    let lo := fun d => some (konstWL 4 0x800fffffffffffff d)
    let hi := fun d => some (konstWL 4 0x0010000000000000 d)
    let k := fun d => some (konstWL 4 0 d)
    let code := fun d => floatAlignSumL d
      (fun j => floatCoefficientL j lo) (fun j => floatCoefficientL j hi) k
    WordCode (L := L) (Env.nil : Env D []) (fun _ => True) code 1 ∧
    (∃ c, code 8 = some (c, 15) ∧ c.length = 297) ∧
    Gleitkomma.rundeExakt Gleitkomma.f64
      (Gleitkomma.exaktAdd ⟨-(2^52-1), -1074⟩ ⟨2^52, -1074⟩) = ⟨false, 0, 1⟩ := by
  dsimp only
  refine ⟨?_, ?_, by decide +kernel⟩
  · have he : floatAlignSumWord (floatCoefficientWord 0x800fffffffffffff)
        (floatCoefficientWord 0x0010000000000000) 0 = 1 := by decide +kernel
    rw [← he]
    intro fp K d c top hcode hK m pc hp
    exact floatCoefficientAlignSumL_ok (L := L)
      (ρ := (Env.nil : Env D [])) (W := fun _ => True)
      (WordCode.konst 0x800fffffffffffff (by decide))
      (WordCode.konst 0x0010000000000000 (by decide))
      (WordCode.konst 0 (by decide)) hcode hK m pc hp
  · refine ⟨((floatAlignSumL 8
        (fun d => floatCoefficientL d (fun j => some (konstWL 4 0x800fffffffffffff j)))
        (fun d => floatCoefficientL d (fun j => some (konstWL 4 0x0010000000000000 j)))
        (fun d => some (konstWL 4 0 d))).getD ([], 0)).1, ?_, ?_⟩ <;> decide +kernel

theorem alignmentImages_zeuge : alignmentImages.length = 7 ∧
    alignmentImages.all (fun x => x.2.1.isOk) = true := by
  decide +kernel

theorem coefficientImages_zeuge : coefficientImages.length = 8 ∧
    coefficientImages.all (fun x => x.2.1.isOk) = true := by
  decide +kernel

/-- Model, producer, actual simulation and exact sizes hold jointly for a
    negative finite normal with a nonzero low significand. -/
theorem floatCoefficientL_joint_zeuge [Kern] {D : Deklaration} (L : Lay D) :
    let a : GFloat := ⟨true, 1023, 9⟩
    let producer := fun d => some (konstWL 4 (Gleitkomma.zuBits _ a) d)
    Gleitkomma.wf Gleitkomma.f64 a ∧
    Gleitkomma.wertExakt Gleitkomma.f64 a = some ⟨-(2^52+9), -52⟩ ∧
    WordCode (L := L) (Env.nil : Env D []) (fun _ => True)
      (fun d => floatCoefficientL d producer) (BitVec.ofInt 64 (-(2^52+9))) ∧
    ∃ code, floatCoefficientL 8 producer = some (code, 14) ∧ code.length = 139 := by
  dsimp only
  refine ⟨by decide, by decide, ?_, ?_⟩
  · have hc := floatCoefficientWord_canonical (⟨true, 1023, 9⟩ : GFloat) (by decide)
    change floatCoefficientWord (BitVec.ofNat 64 0xbff0000000000009) =
      BitVec.ofInt 64 (-(2^52+9)) at hc
    rw [← hc]
    intro fp K d c top h hK m pc hp
    exact floatCoefficientL_ok (L := L) (ρ := (Env.nil : Env D []))
      (W := fun _ => True) (WordCode.konst 0xbff0000000000009 (by decide)) h hK m pc hp
  · refine ⟨((floatCoefficientL 8 (fun d => some
        (konstWL 4 0xbff0000000000009 d))).getD ([], 0)).1, ?_, ?_⟩ <;> decide +kernel

theorem fieldImages_zeuge : fieldImages.length = 8 ∧
    fieldImages.all (fun x => x.2.1.isOk) = true := by
  decide +kernel

theorem images_zeuge : images.length = 8 ∧ images.all (fun x => x.2.1.isOk) = true := by
  decide +kernel

/-- A real input producer satisfies the generic simulation premises together
    with the concrete output and the exact temporary/instruction bounds. -/
theorem floatNegL_joint_zeuge [Kern] {D : Deklaration} (L : Lay D) :
    let producer := fun d => some (konstWL 4 0x3ff0000000000000 d)
    let generated := floatNegL 8 producer
    WordCode (L := L) (Env.nil : Env D []) (fun _ => True)
      (fun d => floatNegL d producer) (BitVec.ofNat 64 0xbff0000000000000) ∧
    ∃ code, generated = some (code, 11) ∧ code.length = 35 := by
  dsimp only
  constructor
  · exact floatNegL_ok (L := L) (ρ := (Env.nil : Env D []))
      (W := fun _ => True) (WordCode.konst 0x3ff0000000000000 (by decide))
  · refine ⟨((floatNegL 8 (fun d => some (konstWL 4 0x3ff0000000000000 d))).getD ([], 0)).1, ?_, ?_⟩ <;>
      decide +kernel

/-- Concrete production, simulation and size premises hold jointly. -/
theorem floatFieldL_joint_zeuge [Kern] {D : Deklaration} (L : Lay D) :
    let producer := fun d => some (konstWL 4 0xfff0000000000009 d)
    WordCode (L := L) (Env.nil : Env D []) (fun _ => True)
      (fun d => floatFieldL 52 11 d producer) (BitVec.ofNat 64 2047) ∧
    ∃ code, floatFieldL 52 11 8 producer = some (code, 11) ∧ code.length = 37 := by
  dsimp only
  constructor
  · exact floatFieldL_ok (L := L) (ρ := (Env.nil : Env D []))
      (W := fun _ => True) 52 11 (by decide) (by decide)
      (WordCode.konst 0xfff0000000000009 (by decide))
  · refine ⟨((floatFieldL 52 11 8 (fun d => some (konstWL 4 0xfff0000000000009 d))).getD ([], 0)).1, ?_, ?_⟩ <;>
      decide +kernel

#print axioms floatNegL_joint_zeuge

/-- A nonzero exact tail requiring several actual SMALL iterations. -/
def normalizationWitnessCode : List II :=
  ((floatNormalizeLoopL 16).getD ([], 0)).1

def normalizationWitnessMemory : Runner.Mem where
  b a := if a.toNat < 4294967296 then
      ((normalizationWitnessCode.flatMap encII)[a.toNat]?).getD 0
    else if a.toNat = 4294967296+8*17 then 13
    else if a.toNat = 4294967296+8*18 then 4
    else if a.toNat = 4294967296+8*19 then 8
    else if a.toNat = 4294967296+8*20 then 68 else 0
  rd _ := true
  wr _ := true

theorem normalizationLoopHead_zeuge [Kern] {D : Deklaration} (L : Lay D) :
    FloatNormalizeHead L (Env.nil : Env D []) (fun _ => True)
      0 4294967296 64 16 7 normalizationWitnessCode 13 4 68 8
      normalizationWitnessMemory 68 0 4 0 13 := by
  have pre : Pre L normalizationWitnessMemory 0 4294967296 64 16
      normalizationWitnessCode (Env.nil : Env D []) (fun _ => True) 7 := by
    refine ⟨by decide, by decide, ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩,
      ?_, ?_, (fun _ x => nomatch x), trivial, wstab_true _ _⟩
    · apply codeAt_bytes normalizationWitnessCode 0 (by decide +kernel)
      intro i hi
      refine ⟨rfl, rfl, ?_⟩
      have bound : (normalizationWitnessCode.flatMap encII).length < 4294967296 := by
        decide +kernel
      simp only [normalizationWitnessMemory, Nat.zero_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show i < 2^64 by omega),
        if_pos (show i < 4294967296 by omega),
        List.getElem?_eq_getElem hi, Option.getD_some]
    · change 0 + 16 * normalizationWitnessCode.length < 2^64 ∧
        4294967296 + 8 * 64 ≤ 2^64 ∧
        0 + 16 * normalizationWitnessCode.length ≤ 4294967296
      decide +kernel

  exact FloatNormalizeHead.of_numerator 13 4 68 (by decide) (by decide) (by decide)
    (by decide) pre (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Canonical outputs and actual whole-loop execution hold jointly on a
    nonzero tail, a nonzero reserved prefix and several normalization steps. -/
theorem floatNormalizeLoopL_from_numerator_zeuge [Kern] {D : Deklaration} (L : Lay D) :
    ∃ m' fuel' count' distance' q' r',
      Star ⟨0, 4294967296⟩ normalizationWitnessMemory
        ⟨BitVec.ofNat 64 (16*normalizationWitnessCode.length), 4294967296⟩ m' ∧
      Agree 4294967296 16 64 normalizationWitnessMemory m' ∧
      FloatNormalizeHead L (Env.nil : Env D []) (fun _ => True)
        0 4294967296 64 16 7 normalizationWitnessCode 13 4 68 8
        m' fuel' count' distance' q' r' ∧
      (fuel' = 0 ∨ 8 ≤ q') ∧ count' ≤ 68 ∧
      (13 * 2^(count'+distance') : Int) / 2^(distance'+4) = q' ∧
      (13 * 2^(count'+distance') : Int) % 2^(distance'+4) = r' * 2^4 := by
  have hc : floatNormalizeLoopL 16 = some (normalizationWitnessCode,
      ((floatNormalizeLoopL 16).getD ([], 0)).2) := by decide +kernel
  have h := normalizationLoopHead_zeuge L
  exact floatNormalizeLoopL_from_numerator hc (by decide +kernel) 13 4 68
    (by decide) (by decide) (by decide) (by decide) h.pre h.room
    h.readQ h.readR h.readDistance h.readTarget h.readFuel h.readCount

/-- The concrete nonzero-tail frame also satisfies the sufficient precision
    budget jointly with the actual emitted-loop execution premises. -/
theorem floatNormalizeLoopL_reaches_target_zeuge [Kern] {D : Deklaration} (L : Lay D) :
    ∃ m' fuel' count' distance' q' r',
      Star ⟨0, 4294967296⟩ normalizationWitnessMemory
        ⟨BitVec.ofNat 64 (16*normalizationWitnessCode.length), 4294967296⟩ m' ∧
      Agree 4294967296 16 64 normalizationWitnessMemory m' ∧
      FloatNormalizeHead L (Env.nil : Env D []) (fun _ => True)
        0 4294967296 64 16 7 normalizationWitnessCode 13 4 68 8
        m' fuel' count' distance' q' r' ∧
      8 ≤ q' ∧ count' ≤ 68 ∧
      (13 * 2^(count'+distance') : Int) / 2^(distance'+4) = q' ∧
      (13 * 2^(count'+distance') : Int) % 2^(distance'+4) = r' * 2^4 := by
  have hc : floatNormalizeLoopL 16 = some (normalizationWitnessCode,
      ((floatNormalizeLoopL 16).getD ([], 0)).2) := by decide +kernel
  exact floatNormalizeLoopL_reaches_target hc (by decide +kernel)
    (normalizationLoopHead_zeuge L) 3 (by decide) (by decide) (by decide)

#print axioms floatNormalizeLoopL_reaches_target_zeuge

#print axioms normalizationLoopHead_zeuge
#print axioms floatNormalizeLoopL_from_numerator_zeuge

end Gabbro.Stage0.Senke.AddSubProbe
