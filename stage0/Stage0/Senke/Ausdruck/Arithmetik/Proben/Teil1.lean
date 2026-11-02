/- Emitted runner images for the shared arithmetic operand preparation. -/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Proben.Teil1a

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung
public import Stage0.Senke.Images.BildLese
public import Stage0.Senke.Anweisung.Faelle.Gleit.ArithmetikProben

@[expose] public section



namespace Gabbro.Stage0.Senke.AddSubProbe
open Gabbro.Grammatik Runner.IR Gleitkomma

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
