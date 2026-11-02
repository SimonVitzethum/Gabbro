module

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung
public import Stage0.Senke.Images.BildLese
public import Stage0.Senke.Anweisung.Faelle.Gleit.ArithmetikProben
public import Stage0.Senke.Ausdruck.Arithmetik.Proben.Teil2

@[expose] public section

namespace Gabbro.Stage0.Senke.AddSubProbe
open Gabbro.Grammatik Runner.IR Gleitkomma

/-- Cancellation exercises the same actual loop and reserved frame as the
    nonzero fixture; only the exact-tail input word is changed to zero. -/
theorem floatNormalizeLoopL_finite_magnitude_zero_zeuge [Kern]
    {D : Deklaration} (L : Lay D) :
    ∃ m m' fuel count distance,
      FloatNormalizeHead L (Env.nil : Env D []) (fun _ => True)
        0 4294967296 64 16 7 normalizationWitnessCode 0 4 68 8
        m 68 0 4 0 0 ∧
      Star ⟨0, 4294967296⟩ m
        ⟨BitVec.ofNat 64 (16*normalizationWitnessCode.length), 4294967296⟩ m' ∧
      Agree 4294967296 16 64 m m' ∧
      FloatNormalizeHead L (Env.nil : Env D []) (fun _ => True)
        0 4294967296 64 16 7 normalizationWitnessCode 0 4 68 8
        m' fuel count distance 0 0 := by
  have h := normalizationLoopHead_zeuge L
  let m := Runner.Mem.write normalizationWitnessMemory
    (Runner.IR.slot 4294967296 (BitVec.ofNat 64 17)) 8 0
  have ag : Agree 4294967296 17 64 normalizationWitnessMemory m :=
    agree_write h.pre.frame.room (by decide) (by decide) 0
  have pre : Pre L m 0 4294967296 64 16 normalizationWitnessCode
      (Env.nil : Env D []) (fun _ => True) 7 :=
    ⟨h.pre.ctx, h.pre.small, h.pre.frame.agree ag,
      h.pre.code.agree ag h.pre.far, h.pre.far,
      (fun _ x => nomatch x), trivial, wstab_true _ _⟩
  have kept (i : Nat) (hi : i < 64) (hne : 17 ≠ i) :
      m.rd64 (Runner.IR.slot 4294967296 (BitVec.ofNat 64 i)) =
        normalizationWitnessMemory.rd64 (Runner.IR.slot 4294967296 (BitVec.ofNat 64 i)) :=
    rd_other h.pre.frame.room (by decide) hi hne 0
  have head : FloatNormalizeHead L (Env.nil : Env D []) (fun _ => True)
      0 4294967296 64 16 7 normalizationWitnessCode 0 4 68 8
      m 68 0 4 0 0 := by
    apply FloatNormalizeHead.of_numerator 0 4 68 (by decide) (by decide)
      (by decide) (by decide) pre (by decide)
    · rw [kept 16 (by decide) (by decide)]; exact h.readQ
    · exact rd_same h.pre.frame (by decide) 0
    · rw [kept 18 (by decide) (by decide)]; exact h.readDistance
    · rw [kept 19 (by decide) (by decide)]; exact h.readTarget
    · rw [kept 20 (by decide) (by decide)]; exact h.readFuel
    · rw [kept 21 (by decide) (by decide)]; exact h.readCount
  have hc : floatNormalizeLoopL 16 = some (normalizationWitnessCode,
      ((floatNormalizeLoopL 16).getD ([], 0)).2) := by decide +kernel
  obtain ⟨last, f, c, d, q, r, run, agree, finalHead, cases, _⟩ :=
    floatNormalizeLoopL_finite_magnitude hc (by decide +kernel) head
      (by decide) 3 (by decide) (by decide)
  have zeros := finalHead.zero_words
  obtain ⟨rfl, rfl⟩ := zeros
  exact ⟨m, last, f, c, d, head, run, agree, finalHead⟩

#print axioms floatNormalizeLoopL_finite_magnitude_zero_zeuge

/-- The same total theorem also has a nonzero exact-tail execution witness. -/
theorem floatNormalizeLoopL_finite_magnitude_zeuge [Kern]
    {D : Deklaration} (L : Lay D) :
    ∃ m' fuel count distance q r,
      Star ⟨0, 4294967296⟩ normalizationWitnessMemory
        ⟨BitVec.ofNat 64 (16*normalizationWitnessCode.length), 4294967296⟩ m' ∧
      Agree 4294967296 16 64 normalizationWitnessMemory m' ∧
      FloatNormalizeHead L (Env.nil : Env D []) (fun _ => True)
        0 4294967296 64 16 7 normalizationWitnessCode 13 4 68 8
        m' fuel count distance q r ∧ 8 ≤ q := by
  have hc : floatNormalizeLoopL 16 = some (normalizationWitnessCode,
      ((floatNormalizeLoopL 16).getD ([], 0)).2) := by decide +kernel
  obtain ⟨last, f, c, d, q, r, run, agree, finalHead, cases, _⟩ :=
    floatNormalizeLoopL_finite_magnitude hc (by decide +kernel)
      (normalizationLoopHead_zeuge L) (by decide) 3 (by decide) (by decide)
  refine ⟨last, f, c, d, q, r, run, agree, finalHead, ?_⟩
  rcases cases with zero | positive
  · omega
  · exact positive.2

/-- Output fields are derived jointly from an actually reached memory state. -/
theorem normalizationOutputFields_zeuge [Kern] {D : Deklaration} (L : Lay D) :
    ∃ m' fuel count distance q r,
      Star ⟨0, 4294967296⟩ normalizationWitnessMemory
        ⟨BitVec.ofNat 64 (16*normalizationWitnessCode.length), 4294967296⟩ m' ∧
      FloatNormalizeHead L (Env.nil : Env D []) (fun _ => True)
        0 4294967296 64 16 7 normalizationWitnessCode 13 4 68 8
        m' fuel count distance q r ∧ 8 ≤ q ∧
      (13 * 2^(count+distance) : Int) / (8 * 2^(distance+4)) = q / 8 ∧
      (13 * 2^(count+distance) : Int) % (8 * 2^(distance+4)) =
        (q % 8) * 2^(distance+4) + r * 2^4 ∧
      0 ≤ q % 8 ∧ q % 8 < 8 ∧
        (r * 2^4 = 0 ↔ r = 0) := by
  obtain ⟨m', f, c, d, q, r, run, _, head, normalized⟩ :=
    floatNormalizeLoopL_finite_magnitude_zeuge L
  exact ⟨m', f, c, d, q, r, run, head, normalized, head.output_fields⟩

#print axioms normalizationOutputFields_zeuge

#print axioms floatNormalizeLoopL_finite_magnitude_zeuge

/-- Joint decoded-input witness: opposite signs cancel to one subnormal unit,
    then the production loop performs all 55 guard-precision transfers from executed writes. -/
def decodedInitWitness : List II × Nat :=
  let lit := fun n j => some (konstWL 4 n j)
  (floatStateSlotsL 16 (floatExactAddInitProducers
    (lit 0x800fffffffffffff) (lit 0x0010000000000000) (lit 0))).getD ([],0)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
theorem floatExactAddNormalize_ok_zeuge [Kern] {D : Deklaration} (L : Lay D)
    {m : Runner.Mem} {pc fp : Runner.W}
    (pre : Pre L m pc fp 64 16 (decodedInitWitness.1 ++ normalizationWitnessCode)
      (Env.nil : Env D []) (fun _ => True)) :
    ∃ m' q, Star ⟨pc,fp⟩ m
      ⟨pc + BitVec.ofNat 64 (16*(decodedInitWitness.1 ++ normalizationWitnessCode).length),fp⟩ m' ∧
      (2^55 : Int) ≤ q := by
  let lit := fun n j => some (konstWL 4 n j)
  have hc : floatStateSlotsL 16 (floatExactAddInitProducers
      (lit 0x800fffffffffffff) (lit 0x0010000000000000) (lit 0)) =
      some decodedInitWitness := by decide +kernel
  have hl : floatNormalizeLoopL 16 = some (normalizationWitnessCode,
      ((floatNormalizeLoopL 16).getD ([],0)).2) := by decide +kernel
  obtain ⟨m', f, c, d, q, r, run, _, _, result, _⟩ :=
    floatExactAddNormalize_ok (L := L)
      (lo := lit 0x800fffffffffffff) (hi := lit 0x0010000000000000) (distance := lit 0)
      (ρ := (Env.nil : Env D [])) (W := fun _ => True)
      (⟨true,0,2^52-1⟩ : GFloat) (⟨false,1,0⟩ : GFloat) 0
      (by decide) (by decide) (by decide) (by decide +kernel)
      (WordCode.konst 0x800fffffffffffff (by decide))
      (WordCode.konst 0x0010000000000000 (by decide))
      (WordCode.konst 0 (by decide)) hc (by decide +kernel) (by decide)
      hl (by decide +kernel) pre
  refine ⟨m', q, run, ?_⟩
  norm_num [floatCoefficient, f64, floatSumMagnitude] at result
  exact result

#print axioms floatExactAddNormalize_ok_zeuge

/-- Whole finite pipeline. Alignment is computed from the encoded operands;
    the fixture distance is retained only as audit metadata. -/
def exactCompositionBoundaryFragment (a b k : Nat) : Option (List II × Nat) := do
  let _ := k
  let lit := fun n j => some (konstWL 4 n j)
  let result ← floatFiniteAddL f64 8 (lit a) (lit b)
  pure result

/-- Canonical expected bits for the complete finite pipeline, including all
    eight boundary counterexamples from the original failing audit. -/
def exactCompositionCases : List (String × Nat × Nat × Nat × Nat) :=
  [("one-plus-zero", 0x3ff0000000000000, 0, 0, 0x3ff0000000000000),
   ("one-plus-negative-zero", 0x3ff0000000000000, 0x8000000000000000, 0, 0x3ff0000000000000),
   ("negative-one-plus-zero", 0xbff0000000000000, 0, 0, 0xbff0000000000000),
   ("negative-one-plus-negative-zero", 0xbff0000000000000, 0x8000000000000000, 0, 0xbff0000000000000),
   ("carry", 0x3ff0000000000000, 0x3ff0000000000000, 0, 0x4000000000000000),
   ("partial-cancellation", 0x3ff8000000000000, 0xbff0000000000000, 0, 0x3fe0000000000000),
   ("minimum-normal-identity", 0x0010000000000000, 0, 0, 0x0010000000000000),
   ("maximum-finite-identity", 0x7fefffffffffffff, 0, 0, 0x7fefffffffffffff),
   ("aligned-gap", 0x3fe0000000000000, 0x3ff0000000000000, 1, 0x3ff8000000000000),
   ("zero",0,0,0,0),
   ("negative-zero",0x8000000000000000,0x8000000000000000,0,0x8000000000000000),
   ("cancellation",0x3ff0000000000000,0xbff0000000000000,0,0),
   ("minimum-subnormal",1,0,0,1),
   ("subnormal-to-normal",0xfffffffffffff,1,0,0x10000000000000),
   ("normal-to-subnormal",0x10000000000000,0x800fffffffffffff,0,1),
   ("halfway-even",0x3ca0000000000000,0x3ff0000000000000,53,0x3ff0000000000000),
   ("overflow",0x7fefffffffffffff,0x7fefffffffffffff,0,0x7ff0000000000000)]

def exactCompositionBoundaryImages : List (String × Except String (List Runner.B) × Nat) :=
  exactCompositionCases.map fun (name,a,b,k,expected) =>
    ("exact-composition-" ++ name,
      FloatArithmeticProbe.wordImage (exactCompositionBoundaryFragment a b k) expected, 7)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem exactCompositionBoundary_zeuge :
    wf f64 (⟨false,1023,0⟩ : GFloat) ∧
    wf f64 (⟨false,0,0⟩ : GFloat) ∧
    zuBits f64 (add f64 ⟨false,1023,0⟩ ⟨false,0,0⟩) = 0x3ff0000000000000 ∧
    exactCompositionCases.length = 17 ∧
    exactCompositionBoundaryImages.all (fun x => x.2.1.isOk) = true := by
  decide +kernel

#print axioms exactCompositionBoundary_zeuge

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- Independent canonical IEEE expectations for every whole-chain fixture. -/
theorem exactCompositionCanonical_zeuge :
    exactCompositionCases.all (fun (_,a,b,_,expected) =>
      let x : GBits f64 := ⟨a / 2^63 == 1, a / 2^52 % 2048, a % 2^52⟩
      let y : GBits f64 := ⟨b / 2^63 == 1, b / 2^52 % 2048, b % 2^52⟩
      decide (wf f64 x ∧ wf f64 y) && (zuBits f64 (add f64 x y) == expected)) = true := by
  decide +kernel

#print axioms exactCompositionCanonical_zeuge

/-- The same runtime emitter, with binary32 decoding and packing parameters. -/
def finite32Cases : List (String × Nat × Nat × Nat) :=
  [("zero",0,0,0), ("negative-zero",0x80000000,0x80000000,0x80000000),
   ("cancellation",0x3f800000,0xbf800000,0), ("minimum-subnormal",1,0,1),
   ("subnormal-to-normal",0x7fffff,1,0x800000),
   ("normal-to-subnormal",0x800000,0x807fffff,1),
   ("halfway-even",0x33800000,0x3f800000,0x3f800000),
   ("overflow",0x7f7fffff,0x7f7fffff,0x7f800000)]

def finite32Images : List (String × Except String (List Runner.B) × Nat) :=
  finite32Cases.map fun (name,a,b,expected) =>
    ("finite32-" ++ name, FloatArithmeticProbe.wordImage
      (floatFiniteAddL f32 8 (fun j => some (konstWL 4 a j))
        (fun j => some (konstWL 4 b j))) expected, 7)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem finite32Canonical_zeuge :
    finite32Cases.all (fun (_,a,b,expected) =>
      let x : GBits f32 := ⟨a / 2^31 == 1, a / 2^23 % 256, a % 2^23⟩
      let y : GBits f32 := ⟨b / 2^31 == 1, b / 2^23 % 256, b % 2^23⟩
      decide (wf f32 x ∧ wf f32 y) && (zuBits f32 (add f32 x y) == expected)) = true ∧
    finite32Images.all (fun x => x.2.1.isOk) = true := by
  decide +kernel

#print axioms finite32Canonical_zeuge

/-- The source-scale bridge has a nonzero executed-loop witness, including
    the same fetch, frame and exact-tail premises as the generic theorem. -/
theorem normalizationSourceScale_zeuge [Kern] {D : Deklaration} (L : Lay D) :
    ∃ m' fuel count distance q r,
      Star ⟨0, 4294967296⟩ normalizationWitnessMemory
        ⟨BitVec.ofNat 64 (16*normalizationWitnessCode.length), 4294967296⟩ m' ∧
      FloatNormalizeHead L (Env.nil : Env D []) (fun _ => True)
        0 4294967296 64 16 7 normalizationWitnessCode 13 4 68 8
        m' fuel count distance q r ∧ 8 ≤ q ∧
      let nd := normQD 53 (3-(count : Int)) (13 * 2^distance)
        (8 * 2^(distance+4+49))
      nd.1 / nd.2 = (q/8).toNat := by
  obtain ⟨m', f, c, d, q, r, run, _, head, reached⟩ :=
    floatNormalizeLoopL_finite_magnitude_zeuge L
  refine ⟨m', f, c, d, q, r, run, head, reached, ?_⟩
  have h := head.normQD_source_output 53 49
  have exponent : (53 : Int)-1-c-49 = 3-c := by omega
  have hh : (normQD 53 ((53 : Int)-1-c-49) (13 * 2^d)
      (8 * 2^(d+4+49))).1 /
      (normQD 53 ((53 : Int)-1-c-49) (13 * 2^d)
      (8 * 2^(d+4+49))).2 = (q/8).toNat := h.1
  rw [exponent] at hh
  exact hh

#print axioms normalizationSourceScale_zeuge

/-- Both format precisions share the canonical rounding bridge on the same
    nonzero executed loop, rather than independent arithmetic-only fixtures. -/
theorem normalizationSourceRound_zeuge [Kern] {D : Deklaration} (L : Lay D) :
    ∃ m' fuel count distance q r,
      Star ⟨0, 4294967296⟩ normalizationWitnessMemory
        ⟨BitVec.ofNat 64 (16*normalizationWitnessCode.length), 4294967296⟩ m' ∧
      FloatNormalizeHead L (Env.nil : Env D []) (fun _ => True)
        0 4294967296 64 16 7 normalizationWitnessCode 13 4 68 8
        m' fuel count distance q r ∧ 8 ≤ q ∧
      (∀ p scale : Nat,
        normQ p ((p : Int)-1-count-scale) (13 * 2^distance)
          (8 * 2^(distance+4+scale)) =
        rundeInt (q/8).toNat (2 * (q%8).toNat + if r = 0 then 0 else 1) 16) := by
  obtain ⟨m', f, c, d, q, r, run, _, head, reached⟩ :=
    floatNormalizeLoopL_finite_magnitude_zeuge L
  refine ⟨m', f, c, d, q, r, run, head, reached, ?_⟩
  intro p scale
  exact head.normQ_source_guard p scale

#print axioms normalizationSourceRound_zeuge

end Gabbro.Stage0.Senke.AddSubProbe
