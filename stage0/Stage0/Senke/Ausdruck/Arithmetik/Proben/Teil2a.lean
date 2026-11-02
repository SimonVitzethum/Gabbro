module

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung
public import Stage0.Senke.Images.BildLese
public import Stage0.Senke.Anweisung.Faelle.Gleit.ArithmetikProben
public import Stage0.Senke.Ausdruck.Arithmetik.Proben.Teil1

@[expose] public section

namespace Gabbro.Stage0.Senke.AddSubProbe
open Gabbro.Grammatik Runner.IR Gleitkomma

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

end Gabbro.Stage0.Senke.AddSubProbe
