/- Canonical result fields of the guard-rounding and packing continuation. -/
module
public import Stage0.Senke.Gleit.Normal.Pack
public import Stage0.Senke.Gleit.Routine.RoutineModel
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR

private theorem packUnpack (w : Runner.W) :
    packWord (unpackSignWord w) (unpackBexpWord w) (unpackFracWord w) = w := by
  change ((((w >>> 63) <<< 63) |||
      (((w >>> 52) &&& BitVec.ofNat 64 (2 ^ 11 - 1)) <<< 52)) |||
      (w &&& BitVec.ofNat 64 (2 ^ 52 - 1))) = w
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  by_cases low : i < 52
  · simp [hi, low, show i < 63 by omega]
  · by_cases middle : i < 63
    · simp [hi, low, middle, show i - 52 < 64 by omega,
        show i - 52 < 11 by omega, show 52 + (i - 52) = i by omega]
    · have top : i = 63 := by omega
      subst i
      simp

/-- Reconstruct the canonical encoding from the existing field extraction
    correspondence. Packing introduces neither a second decoder nor masks. -/
theorem packWord_canonical (a : GFloat) (ha : wf f64 a) :
    packWord (Runner.IR.bool a.sign) (BitVec.ofNat 64 a.bexp)
      (BitVec.ofNat 64 a.frac) = BitVec.ofNat 64 (zuBits f64 a) := by
  obtain ⟨hs, he, hf⟩ := routineUnpack_canonical a ha
  rw [← hs, ← he, ← hf]
  exact packUnpack _

set_option maxRecDepth 4096 in
/-- Identify all output fields of the actual word continuation. Its input
    has three guard bits and is below the next hidden-bit position. The
    rounded carry, subnormal boundary and exponent overflow are explicit. -/
theorem routineRoundPackWord_model (s : Bool) (e n : Nat)
    (eb : e ≤ 2047) (nb : n < 2 ^ 56) :
    let q := rundeInt (n / 8) (n % 8) 8
    let exponent := softCarryExp e q
    let significand := softCarry q
    routineRoundPackWord (Runner.IR.bool s) (BitVec.ofNat 64 e) (BitVec.ofNat 64 n) =
      BitVec.ofNat 64 (zuBits f64
        (if exponent < 2047 then
          if significand < 2 ^ 52 then ⟨s, 0, significand⟩
          else ⟨s, exponent, significand - 2 ^ 52⟩
        else ⟨s, 2047, 0⟩)) := by
  dsimp only
  let q := rundeInt (n / 8) (n % 8) 8
  have qb : q ≤ 2 ^ 53 := by
    dsimp only [q]
    unfold rundeInt
    split
    · omega
    · split
      · omega
      · split <;> omega
  have q64 : q < 2 ^ 64 := by omega
  have sigBound : softCarry q < 2 ^ 53 := by
    unfold softCarry
    split <;> omega
  have expBound : softCarryExp e q < 2 ^ 64 := by
    unfold softCarryExp
    split <;> omega
  have magnitude : routineRoundMagnitudeWord (BitVec.ofNat 64 n) = BitVec.ofNat 64 q := by
    simp only [routineRoundMagnitudeWord, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]
    rfl
  have carry : (BitVec.ofNat 64 q == BitVec.ofNat 64 (2 ^ 53)) =
      decide (q = 2 ^ 53) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt q64,
      Nat.mod_eq_of_lt (by decide : 2 ^ 53 < 2 ^ 64)]
  have exponent : BitVec.ofNat 64 e + Runner.IR.bool (decide (q = 2 ^ 53)) =
      BitVec.ofNat 64 (softCarryExp e q) := by
    by_cases hc : q = 2 ^ 53
    · simp only [softCarryExp, hc, decide_true, Runner.IR.bool, ite_true]
      rw [BitVec.ofNat_add]
      rfl
    · simp only [softCarryExp, hc, decide_false, Runner.IR.bool,
        Bool.false_eq_true, ite_false]
      simp
  have significand : BitVec.ofNat 64 q >>>
      ((Runner.IR.bool (decide (q = 2 ^ 53))).toNat % 64) =
      BitVec.ofNat 64 (softCarry q) := by
    by_cases hc : q = 2 ^ 53
    · simp only [softCarry, hc, decide_true, Runner.IR.bool, ite_true]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by decide : 2 ^ 53 < 2 ^ 64),
        Nat.mod_eq_of_lt (by decide : 2 ^ 52 < 2 ^ 64)]
      change (2 ^ 53 : Nat) >>> 1 = 2 ^ 52
      rw [Nat.shiftRight_eq_div_pow]
      decide
    · simp only [softCarry, hc, decide_false, Runner.IR.bool,
        Bool.false_eq_true, ite_false]
      simp
  have expTest : (BitVec.ofNat 64 (softCarryExp e q)).ult 2047 =
      decide (softCarryExp e q < 2047) := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt expBound]
    rfl
  have sigTest : (BitVec.ofNat 64 (softCarry q)).ult (BitVec.ofNat 64 (2 ^ 52)) =
      decide (softCarry q < 2 ^ 52) := by
    simp only [BitVec.ult, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : softCarry q < 2 ^ 64),
      Nat.mod_eq_of_lt (by decide : 2 ^ 52 < 2 ^ 64)]
  change routineRoundPackWord (Runner.IR.bool s) (BitVec.ofNat 64 e) (BitVec.ofNat 64 n) = _
  simp only [routineRoundPackWord, magnitude]
  rw [carry, exponent, significand, expTest, sigTest]
  by_cases finite : softCarryExp e q < 2047
  · simp only [finite, decide_true, ite_true]
    by_cases subnormal : softCarry q < 2 ^ 52
    · simp only [subnormal, decide_true, ite_true]
      simpa only [float_bits] using
        packWord_canonical ⟨s, 0, softCarry q⟩ ⟨by decide, subnormal⟩
    · simp only [subnormal, decide_false, Bool.false_eq_true, ite_false]
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
      simpa only [float_bits] using
        packWord_canonical ⟨s, softCarryExp e q, softCarry q - 2 ^ 52⟩
          ⟨by change softCarryExp e q ≤ 2047; omega,
            by change softCarry q - 2 ^ 52 < 2 ^ 52; omega⟩
  · simp only [finite, decide_false, Bool.false_eq_true, ite_false]
    simpa only [float_bits] using
      packWord_canonical ⟨s, 2047, 0⟩ ⟨by decide, by decide⟩

/-- The same continuation reaches a normal tie, a subnormal result and an
    overflowing carry. Every fixture satisfies the model theorem's bounds. -/
theorem routineRoundPackWord_model_zeuge :
    ∀ p ∈ [(1023, 2 ^ 55 + 4), (1, 16), (2046, 2 ^ 56 - 1)],
      p.1 ≤ 2047 ∧ p.2 < 2 ^ 56 ∧
      routineRoundPackWord 0 (BitVec.ofNat 64 p.1) (BitVec.ofNat 64 p.2) =
        BitVec.ofNat 64 (zuBits f64
          (if softCarryExp p.1 (rundeInt (p.2 / 8) (p.2 % 8) 8) < 2047 then
            if softCarry (rundeInt (p.2 / 8) (p.2 % 8) 8) < 2 ^ 52 then
              ⟨false, 0, softCarry (rundeInt (p.2 / 8) (p.2 % 8) 8)⟩
            else ⟨false, softCarryExp p.1 (rundeInt (p.2 / 8) (p.2 % 8) 8),
              softCarry (rundeInt (p.2 / 8) (p.2 % 8) 8) - 2 ^ 52⟩
          else ⟨false, 2047, 0⟩)) := by
  intro p member
  have bounds : p.1 ≤ 2047 ∧ p.2 < 2 ^ 56 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  exact ⟨bounds.1, bounds.2, routineRoundPackWord_model false p.1 p.2 bounds.1 bounds.2⟩

#print axioms packWord_canonical
#print axioms routineRoundPackWord_model
#print axioms routineRoundPackWord_model_zeuge
end Gabbro.Stage0.Senke
