/- Canonical operand ordering and finite-path boundary witnesses. -/
module
public import Stage0.Senke.Gleit.RoutineAlign
public import Stage0.Senke.Gleit.RoutineModel
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR
set_option maxRecDepth 4096

/-- Removing the sign bit yields exactly the canonical magnitude key.
    Reuse the shared field extraction theorem rather than a second decoder. -/
theorem routineMagnitudeWord_canonical (a : GFloat) (ha : wf f64 a) :
    (routineMagnitudeWord (BitVec.ofNat 64 (zuBits f64 a))).toNat = floatMag a := by
  have field := floatFieldWord_model (BitVec.ofNat 64 (zuBits f64 a)) 0 63 (by decide)
  have same : routineMagnitudeWord (BitVec.ofNat 64 (zuBits f64 a)) =
      floatFieldWord (BitVec.ofNat 64 (zuBits f64 a)) 0 63 := by
    simp only [routineMagnitudeWord, floatFieldWord, BitVec.ushiftRight_zero]
    rfl
  rw [same, field]
  have bound := zuBits_f64_lt a ha
  have mag := floatMag_lt ha
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound, Nat.pow_zero, Nat.div_one,
    float_bits]
  cases a.sign <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] <;> omega

/-- Unsigned comparison computes the canonical magnitude ordering, even for
    a negative operand whose original encoding has its high bit set. -/
theorem routineOrder_canonical (a b : GFloat) (ha : wf f64 a) (hb : wf f64 b) :
    (routineMagnitudeWord (BitVec.ofNat 64 (zuBits f64 a))).ult
      (routineMagnitudeWord (BitVec.ofNat 64 (zuBits f64 b))) =
      decide (floatMag a < floatMag b) := by
  simp only [BitVec.ult, routineMagnitudeWord_canonical a ha,
    routineMagnitudeWord_canonical b hb]

/-- A magnitude-ordered pair also has ordered scale indices. In particular
    the directional exponent subtraction cannot wrap on canonical operands. -/
theorem routineOrder_indices (a b : GFloat) (ha : wf f64 a) (hb : wf f64 b)
    (order : floatMag b ≤ floatMag a) : max b.bexp 1 ≤ max a.bexp 1 := by
  have af := ha.2
  have bf := hb.2
  change a.frac < 4503599627370496 at af
  change b.frac < 4503599627370496 at bf
  unfold floatMag at order
  omega

/-- Hidden-bit insertion and the effective exponent are derived from the
    actual packed operands, including zero and every subnormal. -/
theorem routineSigIndex_canonical (a : GFloat) (ha : wf f64 a) :
    let w := BitVec.ofNat 64 (zuBits f64 a)
    routineSigWord w = BitVec.ofNat 64 (softSig a.bexp a.frac) ∧
    routineIndexWord w = BitVec.ofNat 64 (max a.bexp 1) := by
  obtain ⟨_, he, hf⟩ := routineUnpack_canonical a ha
  have bound : a.bexp < 2 ^ 64 := by have := ha.1; change a.bexp ≤ 2047 at this; omega
  have zero : (BitVec.ofNat 64 a.bexp == 0) = decide (a.bexp = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    simp
  dsimp only
  simp only [routineSigWord, routineIndexWord, he, hf, zero]
  by_cases hz : a.bexp = 0
  · simp [softSig, hz, Runner.IR.bool]
  · have positive : 1 ≤ a.bexp := by omega
    simp [softSig, hz, Runner.IR.bool, Nat.max_eq_left positive,
      BitVec.ofNat_add, Nat.add_comm]

/-- The exact sum is not generally a 54-bit magnitude. A one-word jammed
    value needs a rounding-preservation theorem; it cannot be substituted
    for this numerator in `softRound_replay`. Both inputs are finite and
    nonzero, so the special dispatcher does not eliminate this case. -/
theorem routineExactWide_zeuge :
    let a : GFloat := ⟨false, 0, 1⟩
    let b : GFloat := ⟨false, 1023, 0⟩
    wf f64 a ∧ wf f64 b ∧ floatAddSpecial f64 a b = none ∧
    wertExakt f64 a = some ⟨1, -1074⟩ ∧
    wertExakt f64 b = some ⟨2 ^ 52, -52⟩ ∧
    (exaktAdd ⟨1, -1074⟩ ⟨2 ^ 52, -52⟩).zaehler.natAbs = 1 + 2 ^ 1074 ∧
    2 ^ 64 < (exaktAdd ⟨1, -1074⟩ ⟨2 ^ 52, -52⟩).zaehler.natAbs := by
  decide +kernel

/-- Cancellation, subnormal output and overflow require separate rounding
    cases. These are accepted canonical source operands, not malformed words.
    The existing bounded normal replay alone cannot justify the total routine. -/
theorem routineFiniteBoundaries_zeuge :
    let a : GFloat := ⟨false, 1023, 1⟩
    let b : GFloat := ⟨true, 1023, 0⟩
    wf f64 a ∧ wf f64 b ∧ floatAddSpecial f64 a b = none ∧
    add f64 a b = ⟨false, 971, 0⟩ ∧
    routineAlignWord (BitVec.ofNat 64 (zuBits f64 a))
      (BitVec.ofNat 64 (zuBits f64 b)) = 8 ∧
    add f64 ⟨false, 0, 1⟩ ⟨false, 0, 1⟩ = ⟨false, 0, 2⟩ ∧
    add f64 ⟨false, 2046, 2 ^ 52 - 1⟩ ⟨false, 2046, 2 ^ 52 - 1⟩ =
      ⟨false, 2047, 0⟩ := by
  decide +kernel

#print axioms routineMagnitudeWord_canonical
#print axioms routineOrder_canonical
#print axioms routineOrder_indices
#print axioms routineSigIndex_canonical
#print axioms routineExactWide_zeuge
#print axioms routineFiniteBoundaries_zeuge
end Gabbro.Stage0.Senke
