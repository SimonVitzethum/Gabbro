/- Emitted runner images for the shared arithmetic operand preparation. -/
import Stage0.Senke.Ausdruck.Arithmetik.Ausrichtung
import Stage0.Senke.Anweisung.Faelle.Gleit.ArithmetikProben

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
end Gabbro.Stage0.Senke.AddSubProbe
