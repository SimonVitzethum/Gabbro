/- Emitted runner images for the shared arithmetic operand preparation. -/
import Stage0.Senke.Ausdruck.Arithmetik.Vorzeichen
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

#print axioms floatNegL_joint_zeuge
end Gabbro.Stage0.Senke.AddSubProbe
