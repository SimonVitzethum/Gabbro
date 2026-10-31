/- Emitted runner images for the shared arithmetic operand preparation. -/
import Stage0.Senke.Ausdruck.Arithmetik.Felder
import Stage0.Senke.Anweisung.Faelle.Gleit.ArithmetikProben

namespace Gabbro.Stage0.Senke.AddSubProbe
open Gabbro.Grammatik Runner.IR

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
