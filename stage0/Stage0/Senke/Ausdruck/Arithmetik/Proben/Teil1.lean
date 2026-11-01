/- Emitted runner images for the shared arithmetic operand preparation. -/
module

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung
public import Stage0.Senke.BildLese
public import Stage0.Senke.Anweisung.Faelle.Gleit.ArithmetikProben

@[expose] public section



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

/-- Actual normalization followed by the quotient output write. -/
def normalizationQuotientImages : List (String × Except String (List Runner.B) × Nat) :=
  [("tail", 13, 4, 8, 68, 1),
   ("even", 16, 5, 16, 68, 2),
   ("zero", 0, 4, 8, 68, 0),
   ("large", 1, 1074, 2^53, 1127, 2^50)].map
    fun (name, r, k, target, fuel, expected) =>
      let fragment := do
        let loop ← floatNormalizeLoopL 16
        let quotient ← wordK 6 24 (some ([ci 2 24 16 0], 25)) 8
        let init := [ci 1 16 0 0] ++ (konstWL 4 r 17).1 ++
          (konstWL 4 k 18).1 ++ (konstWL 4 target 19).1 ++
          (konstWL 4 fuel 20).1 ++ [ci 1 21 0 0]
        pure (init ++ loop.1 ++ quotient.1 ++ [ci 2 8 24 0], max loop.2 quotient.2)
      ("normalize-quotient-" ++ name,
        FloatArithmeticProbe.wordImage fragment expected, 7)

theorem normalizationQuotientImages_zeuge : normalizationQuotientImages.length = 4 ∧
    normalizationQuotientImages.all (fun x => x.2.1.isOk) = true := by
  decide +kernel

#print axioms normalizationQuotientImages_zeuge

/-- All output writes execute after the actual loop. Checking each field
    after all five writes detects clobbering by later producer temporaries. -/
def normalizationFieldsImages : List (String × Except String (List Runner.B) × Nat) :=
  [("tail", 0, 13, 4, 8, 68, 13, 0, 4),
   ("sticky", 13, 3, 4, 8, 68, 13, 3, 0),
   ("zero", 0, 0, 4, 8, 68, 0, 0, 68),
   ("large", 0, 1, 1074, 2^53, 1127, 2^53, 0, 1127),
   ("floor", 0, 13, 1074, 0, 1127, 0, 13, 0)].flatMap
    fun (name, q, r, k, target, fuel, qo, ro, count) =>
      [31,63].flatMap fun signBit => [false,true].flatMap fun negative =>
        [(0, if negative then 2^signBit else 0), (1,1500-count),
         (2,qo/8), (3,qo%8), (4,if ro = 0 then 0 else 1)].map fun (field,expected) =>
          let fragment := do
            let loop ← floatNormalizeLoopL 16
            let fields ← floatStateSlotsL 24 (floatNormalizedFieldsL 16 14 15 signBit)
            let init := (konstWL 4 q 16).1 ++ (konstWL 4 r 17).1 ++
              (konstWL 4 k 18).1 ++ (konstWL 4 target 19).1 ++
              (konstWL 4 fuel 20).1 ++ [ci 1 21 0 0, ci 1 14
                (if negative then -1 else 1) 0, ci 1 15 1500 0]
            pure (init ++ loop.1 ++ fields.1 ++ [ci 2 8 (24+field) 0],
              max loop.2 fields.2)
          ("normalize-fields-" ++ name ++ "-" ++ toString signBit ++ "-" ++
            toString negative ++ "-" ++ toString field,
            FloatArithmeticProbe.wordImage fragment expected,7)

theorem normalizationFieldsImages_zeuge : normalizationFieldsImages.length = 100 ∧
    normalizationFieldsImages.all (fun x => x.2.1.isOk) = true := by
  decide +kernel

#print axioms normalizationFieldsImages_zeuge

/-- Actual packed operands execute all initialization writes and the loop.
    Every state word is read back independently, including cancellation. -/
def decodedInitializationImages : List (String × Except String (List Runner.B) × Nat) :=
  let lit := fun n j => some (konstWL 4 n j)
  [("unit", 0x800fffffffffffff, 0x0010000000000000, 0, 2^55, 55),
   ("negative-unit", 0x000fffffffffffff, 0x8010000000000000, 0, 2^55, 55),
   ("cancel", 0xbff0000000000000, 0x3ff0000000000000, 0, 0, 55),
   ("shift", 1, 3, 2, 13*2^52, 52)].flatMap
    fun (name, a, b, k, q, count) =>
      [(0,q), (1,0), (2,0), (3,2^55), (4,55-count), (5,count)].map
        fun (field, expected) =>
          let fragment := do
            let init ← floatStateSlotsL 16
              (floatExactAddInitProducers (lit a) (lit b) (lit k))
            let loop ← floatNormalizeLoopL 16
            pure (init.1 ++ loop.1 ++ [ci 2 8 (16+field) 0], max init.2 loop.2)
          ("decoded-init-" ++ name ++ "-" ++ toString field,
            FloatArithmeticProbe.wordImage fragment expected, 7)

theorem decodedInitializationImages_zeuge : decodedInitializationImages.length = 24 ∧
    decodedInitializationImages.all (fun x => x.2.1.isOk) = true := by
  decide +kernel

#print axioms decodedInitializationImages_zeuge

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
     ("output-overflow-negative", 2^63, 2046, 2^53-1, 4, 1, 0xfff0000000000000)].flatMap
      (fun (name, s, e, q, g, t, expected) =>
        let retained := do
          let init ← floatStateSlotsL 8 [lit s, lit e, lit q, lit g, lit t]
          let load := fun (i j : Nat) => some ([ci 2 j i 0], j+1)
          let out ← floatAddNormalOutputL 13 (load 8) (load 9) (load 10)
            (load 11) (load 12) (2^52)
          pure (init.1 ++ out.1 ++ [ci 2 8 13 0], max init.2 out.2)
        [(name, FloatArithmeticProbe.wordImage
          (floatAddNormalOutputL 8 (lit s) (lit e) (lit q) (lit g) (lit t) (2^52)) expected, 7),
         (name ++ "-retained-slots", FloatArithmeticProbe.wordImage retained expected, 7)])
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

theorem outputImages_zeuge : outputImages.length = 27 ∧
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

/-- Scale extraction executes at both format boundaries, independently of
    the operand sign and including each end of the finite exponent range. -/
def scaleIndexImages : List (String × Except String (List Runner.B) × Nat) :=
  [("f32", f32), ("f64", f64)].flatMap fun (name, F) =>
    [("zero", 0, 0), ("subnormal", 0, 1),
     ("largest-subnormal", 0, 2^F.fracBits-1),
     ("normal", 1, 0), ("largest-finite", F.bexpMax-1, 2^F.fracBits-1)].flatMap
      fun (tag, exp, frac) => [false, true].map fun sign =>
        let a : GBits F := ⟨sign, exp, frac⟩
        ("scale-" ++ name ++ "-" ++ tag ++ "-" ++ toString sign,
          FloatArithmeticProbe.wordImage
            (floatScaleIndexL F 8 (fun d => some (konstWL 4 (zuBits F a) d)))
            (max exp 1), 7)

theorem scaleIndexImages_zeuge : scaleIndexImages.length = 20 ∧
    scaleIndexImages.all (fun x => x.2.1.isOk) = true := by
  decide +kernel

#print axioms scaleIndexImages_zeuge

/-- Ordering and subtraction execute in both directions, including zero versus
    subnormal, equal exponents, and the largest finite gap of each format. -/
def scaleDistanceImages : List (String × Except String (List Runner.B) × Nat) :=
  [("f32", f32), ("f64", f64)].flatMap fun (name, F) =>
    [("zero-subnormal", 0, 0, 0, 1), ("normal-subnormal", 1, 0, 0, 1),
     ("adjacent", 2, 0, 1, 0), ("max-gap", F.bexpMax-1, 0, 0, 1)].flatMap
      fun (tag, ae, af, be, bf) => [false, true].flatMap fun reverse =>
        let a : GBits F := ⟨true, ae, af⟩
        let b : GBits F := ⟨false, be, bf⟩
        let (a,b) := if reverse then (b,a) else (a,b)
        let lit := fun v d => some (konstWL 4 (zuBits F v) d)
        [("distance", floatScaleDistanceL F 8 (lit a) (lit b),
            max a.bexp 1 - max b.bexp 1 + (max b.bexp 1 - max a.bexp 1)),
         ("order", floatScaleOrderL F 8 (lit a) (lit b),
            if max a.bexp 1 < max b.bexp 1 then 1 else 0)].map
          fun (field, code, expected) =>
            ("scale-" ++ field ++ "-" ++ name ++ "-" ++ tag ++ "-" ++ toString reverse,
              FloatArithmeticProbe.wordImage code expected, 7)

theorem scaleDistanceImages_zeuge : scaleDistanceImages.length = 32 ∧
    scaleDistanceImages.all (fun x => x.2.1.isOk) = true := by
  decide +kernel

#print axioms scaleDistanceImages_zeuge

/-- Both source operations execute every effective sign pair, including signed
    zeros and the subnormal/normal boundary, through the same packed decoder. -/
def sameSignImages : List (String × Except String (List Runner.B) × Nat) :=
  [("f32", f32), ("f64", f64)].flatMap fun (name, F) =>
    [false, true].flatMap fun subtract =>
      [false, true].flatMap fun sa => [false, true].flatMap fun sb =>
        [("zero", 0, 0), ("subnormal", 0, 1), ("normal", 1, 0)].map
          fun (tag, exp, frac) =>
            let a : GBits F := ⟨sa, exp, frac⟩
            let b : GBits F := ⟨sb, exp, frac⟩
            let lit := fun v d => some (konstWL 4 (zuBits F v) d)
            ("effective-sign-" ++ name ++ "-" ++ tag ++ "-" ++ toString subtract ++
                "-" ++ toString sa ++ "-" ++ toString sb,
              FloatArithmeticProbe.wordImage (floatSameSignL F subtract 8 (lit a) (lit b))
                (if sa == (if subtract then !sb else sb) then 1 else 0), 7)

theorem sameSignImages_zeuge : sameSignImages.length = 48 ∧
    sameSignImages.all (fun x => x.2.1.isOk) = true := by
  decide +kernel

#print axioms sameSignImages_zeuge

/-- Execute the quotient sign at cancellation, tail-only and signed word edges;
    the expected bit comes from canonical IEEE rounding, for both formats. -/
def resultSignImages : List (String × Except String (List Runner.B) × Nat) :=
  [("f32", f32), ("f64", f64)].flatMap fun (name,F) =>
    ([("cancel", 0, 0, 1, 0), ("positive-tail", 0, 1, 2^1074, 0),
      ("negative-tail", -1, 2^1074-13, 2^1074, 0),
      ("negative-underflow", -1, 0, 1, -2000),
      ("negative-overflow", -1, 0, 1, 2000),
      ("negative-word-edge", -2^63, 0, 1, 0),
      ("positive-word-edge", 2^63-1, 0, 1, 0)] :
      List (String × Int × Int × Int × Int)).map fun (tag,z,r,den,e) =>
        ("result-sign-" ++ name ++ "-" ++ tag,
          FloatArithmeticProbe.wordImage
            (wordK 13 8 (some (konstWL 4 (z % 2^64).toNat 8)) 0)
            (if (rundeExakt F ⟨z*den+r,e⟩).sign then 1 else 0), 7)

theorem resultSignImages_zeuge : resultSignImages.length = 14 ∧
    resultSignImages.all (fun x => x.2.1.isOk) = true := by
  decide +kernel

#print axioms resultSignImages_zeuge

/-- All signed-zero source pairs use the executed zero dispatcher. -/
def zeroSignImages : List (String × Except String (List Runner.B) × Nat) :=
  [("f32", f32), ("f64", f64)].flatMap fun (name,F) =>
    [false,true].flatMap fun subtract => [false,true].flatMap fun sa =>
      [false,true].map fun sb =>
        let a : GBits F := ⟨sa,0,0⟩
        let b : GBits F := ⟨sb,0,0⟩
        let lit := fun v d => some (konstWL 4 (zuBits F v) d)
        ("zero-sign-" ++ name ++ "-" ++ toString subtract ++ "-" ++
          toString sa ++ "-" ++ toString sb,
          FloatArithmeticProbe.wordImage (floatZeroSignL F subtract 8 (lit a) (lit b))
            (if (if subtract then sub F a b else add F a b).sign then 1 else 0), 7)

theorem zeroSignImages_zeuge : zeroSignImages.length = 16 ∧
    zeroSignImages.all (fun x => x.2.1.isOk) = true := by
  decide +kernel

theorem floatSumSignL_canonical_zeuge [Kern] {D : Deklaration} (L : Lay D) :
    WordCode (L := L) (Env.nil : Env D []) (fun _ => True)
      (fun j => wordK 13 j (some (konstWL 4 (2^64-1) j)) 0)
      (Runner.IR.bool (rundeExakt f64 ⟨-1 * (2^1074) + (2^1074-13),0⟩).sign) := by
  exact floatSumSignL_canonical (L := L) (ρ := (Env.nil : Env D []))
    (W := fun _ => True) (sum := fun j => some (konstWL 4 (2^64-1) j)) f64 (-1) (2^1074-13) (2^1074) 0
    (by decide) (by decide +kernel) (by decide +kernel)
    (by
      intro fp K dst code top hc ht m pc hp
      have h : BitVec.ofNat 64 (2^64-1) = BitVec.ofInt 64 (-1) := by decide +kernel
      exact (WordCode.konst (2^64-1) (by decide +kernel) hc ht m pc hp).mono
        (fun w hw => hw.trans h))

theorem floatZeroSignL_canonical_zeuge [Kern] {D : Deklaration} (L : Lay D) :
    WordCode (L := L) (Env.nil : Env D []) (fun _ => True)
      (fun d => floatZeroSignL f64 true d
        (fun j => some (konstWL 4 (2^63) j))
        (fun j => some (konstWL 4 0 j))) (Runner.IR.bool true) := by
  exact floatZeroSignL_canonical f64 (by unfold Format.dicht; decide) (by decide) true true false
    (by decide) (by decide) (by decide)
    (WordCode.konst _ (by decide)) (WordCode.konst _ (by decide))

#print axioms floatZeroSignL_canonical_zeuge

#print axioms zeroSignImages_zeuge
#print axioms floatSumSignL_canonical_zeuge

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

end Gabbro.Stage0.Senke.AddSubProbe
