module

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung
public import Stage0.Senke.BildLese
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

/-- A nonzero quotient and tail jointly witness actual field execution with
    a negative retained sum and an arbitrary nonzero reservation. -/
def fieldsWitnessCode : List II :=
  ((floatStateSlotsL 24 (floatNormalizedFieldsL 16 22 23 63)).getD ([],0)).1

def fieldsWitnessMemory : Runner.Mem where
  b a := if a.toNat < 4294967296 then
      ((fieldsWitnessCode.flatMap encII)[a.toNat]?).getD 0
    else if a.toNat = 4294967296+8*16 then 13
    else if a.toNat = 4294967296+8*17 then 3
    else if a.toNat = 4294967296+8*18 then 4
    else if a.toNat = 4294967296+8*19 then 8
    else if a.toNat = 4294967296+8*20 then 68
    else if 4294967296+8*22 ≤ a.toNat ∧ a.toNat < 4294967296+8*23 then 255
    else if a.toNat = 4294967296+8*23 then 220
    else if a.toNat = 4294967296+8*23+1 then 5 else 0
  rd _ := true
  wr _ := true

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem normalizationFields_joint_zeuge [Kern] {D : Deklaration} (L : Lay D) :
    ∃ m', Star ⟨0,4294967296⟩ fieldsWitnessMemory
        ⟨BitVec.ofNat 64 (16*fieldsWitnessCode.length),4294967296⟩ m' ∧
      Agree 4294967296 24 64 fieldsWitnessMemory m' ∧
      ∀ i, (hi : i < 5) →
        m'.rd64 (slot 4294967296 (BitVec.ofNat 64 (24+i))) =
          some (([2^63,1500,1,5,1] : List Runner.W)[i]'(by simpa using hi)) := by
  have pre : Pre L fieldsWitnessMemory 0 4294967296 64 16
      fieldsWitnessCode (Env.nil : Env D []) (fun _ => True) 7 := by
    refine ⟨by decide, by decide, ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩,
      ?_, ?_, (fun _ x => nomatch x), trivial, wstab_true _ _⟩
    · apply codeAt_bytes fieldsWitnessCode 0 (by decide +kernel)
      intro i hi
      refine ⟨rfl, rfl, ?_⟩
      have bound : (fieldsWitnessCode.flatMap encII).length < 4294967296 := by
        decide +kernel
      simp only [fieldsWitnessMemory, Nat.zero_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show i < 2^64 by omega),
        if_pos (show i < 4294967296 by omega),
        List.getElem?_eq_getElem hi, Option.getD_some]
    · change 0 + 16 * fieldsWitnessCode.length < 2^64 ∧
        4294967296 + 8 * 64 ≤ 2^64 ∧
        0 + 16 * fieldsWitnessCode.length ≤ 4294967296
      decide +kernel
  have head := FloatNormalizeHead.of_numerator (target := (8 : Int)) 211 4 68
    (by decide) (by decide) (by decide) (by decide) pre (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have pre' : Pre L fieldsWitnessMemory 0 4294967296 64 24
      fieldsWitnessCode (Env.nil : Env D []) (fun _ => True) 7 :=
    { pre with ctx := by decide }
  have result := head.write_fields (signedSum := 22) (exponent := 23)
    (signBit := 63) (dst := 24) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (-1) 1500
    (by decide +kernel) (by decide +kernel)
    (top := ((floatStateSlotsL 24 (floatNormalizedFieldsL 16 22 23 63)).getD ([],0)).2)
    (by decide +kernel) (by decide +kernel) (by decide) pre'
  obtain ⟨last, run, agree, reads⟩ := result
  refine ⟨last, by simpa using run, agree, ?_⟩
  intro i hi
  interval_cases i
  · convert reads 0 (by decide) using 1 <;>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;> decide +kernel
  · convert reads 1 (by decide) using 1 <;>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;> decide +kernel
  · convert reads 2 (by decide) using 1 <;>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;> decide +kernel
  · convert reads 3 (by decide) using 1 <;>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;> decide +kernel
  · convert reads 4 (by decide) using 1 <;>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;> decide +kernel

#print axioms normalizationFields_joint_zeuge

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
      (13 * 2^(count'+distance') : Int) % 2^(distance'+4) = r' * 2^4 ∧
      ∀ F ∈ [Gleitkomma.f32, Gleitkomma.f64],
        let nd := Gleitkomma.normQD F.p ((F.p : Int)-1-count')
          (13 * 2^distance') (8 * 2^(distance'+4))
        nd.1 / nd.2 = (q'/8).toNat ∧
        nd.1 % nd.2 = (q'%8).toNat * 2^(distance'+4) + r'.toNat * 2^4 ∧
        nd.2 = 8 * 2^(distance'+4) := by
  have hc : floatNormalizeLoopL 16 = some (normalizationWitnessCode,
      ((floatNormalizeLoopL 16).getD ([], 0)).2) := by decide +kernel
  obtain ⟨m, f, c, d, q, r, run, agree, head, reached, bound, quotient, tail⟩ :=
    floatNormalizeLoopL_reaches_target hc (by decide +kernel)
      (normalizationLoopHead_zeuge L) 3 (by decide) (by decide) (by decide)
  refine ⟨m, f, c, d, q, r, run, agree, head, reached, bound, quotient, tail, ?_⟩
  intro F _
  simpa using head.normQD_output F.p

#print axioms floatNormalizeLoopL_reaches_target_zeuge

#print axioms normalizationLoopHead_zeuge
#print axioms floatNormalizeLoopL_from_numerator_zeuge

end Gabbro.Stage0.Senke.AddSubProbe
