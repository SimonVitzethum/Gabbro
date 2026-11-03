/- Gradual underflow of a normalized product uses the adder's round/pack
   continuation. A sticky shift may leave just one bit; that case still
   retains the xor sign of an underflowed zero. -/
module
public import Stage0.Senke.Gleit.Mul.Compress
public import Stage0.Senke.Gleit.Normal.GuardModel
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR

/-- A nonzero right shift of a normalized guard magnitude has at most 55
    bits. After 53 places there are fewer than four bits left, so it rounds
    to zero. These bounds include arbitrarily large shift counts. -/
theorem softMulUnderflow_bounds (n k : Nat) (nb : n < 2 ^ 56) (kp : 0 < k) :
    softShiftJamNat n k < 2 ^ 55 ∧
      (53 < k → softShiftJamNat n k < 4) := by
  have data := softMulJam_data n k
  have power : 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) kp
  have product := Nat.mul_le_mul_left (2 ^ 55) power
  have quotient : n / 2 ^ k < 2 ^ 55 :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (by omega)
  constructor
  · omega
  · intro large
    have power : 2 ^ 54 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    have product := Nat.mul_le_mul_left 4 power
    have quotient : n / 2 ^ k < 4 :=
      (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (by omega)
    omega

/-- The subnormal continuation reproduces the general rounding replay,
    including the half-minimum-subnormal tie and the smallest normal carry.
    No premise requires the shifted magnitude to retain a leading bit. -/
theorem softMulUnderflow_model (s : Bool) (n k : Nat)
    (nl : 2 ^ 55 ≤ n) (nb : n < 2 ^ 56) (kp : 0 < k) :
    routineRoundPackWord (Runner.IR.bool s) 1
      (BitVec.ofNat 64 (softShiftJamNat n k)) =
      BitVec.ofNat 64 (zuBits f64
        (rundeExakt f64 ⟨if s then -(n : Int) else n, -1077 - (k : Int)⟩)) := by
  let j := softShiftJamNat n k
  let q := rundeInt (j / 8) (j % 8) 8
  have bounds := softMulUnderflow_bounds n k nb kp
  have jb : j < 2 ^ 56 := by omega
  have qb : q ≤ 2 ^ 52 := by
    dsimp only [q]
    unfold rundeInt
    split <;> omega
  have qScale : softRoundDyadic j (-3) = q := by
    change rundeInt ((j * 1) / 8) ((j * 1) % 8) 8 = q
    simp only [Nat.mul_one]
  have sticky := softRoundDyadic_shiftJam n k 3 (by decide)
  rw [qScale] at sticky
  have nonzero : (if s then -(n : Int) else (n : Int)) ≠ 0 := by
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have mag : (if s then -(n : Int) else (n : Int)).natAbs = n := by cases s <;> simp
  have sign : decide ((if s then -(n : Int) else (n : Int)) < 0) = s := by
    cases s <;> simp [show (0 : Int) < n by omega]
  have replay := softRound_replay_all (if s then -(n : Int) else n)
    (-1077 - (k : Int)) nonzero
  dsimp only at replay
  have bits : bitlen n = 56 := bitlen_unique n 56 nl nb (by decide)
  rw [mag, sign, bits] at replay
  have position : (-1077 - (k : Int)) + (56 : Nat) - 1 = -1022 - (k : Int) := by omega
  have scale : (-1077 - (k : Int)) + 1074 = -((k + 3 : Nat) : Int) := by omega
  rw [position, scale, sticky] at replay
  have noOverflow : ¬ (f64.emax : Int) < -1022 - (k : Int) := by change ¬ (1023 : Int) < _; omega
  have subnormal : ¬ f64.emin ≤ -1022 - (k : Int) := by change ¬ (-1022 : Int) ≤ _; omega
  rw [if_neg noOverflow, if_neg subnormal] at replay
  have carry : q ≠ 2 ^ 53 := by omega
  have packed := routineRoundPackWord_model s 1 j (by decide) jb
  change routineRoundPackWord (Runner.IR.bool s) 1 (BitVec.ofNat 64 j) = _
  rw [packed]
  have underflow : (-1022 - (k : Int) < f64.emin - (f64.p : Int)) ↔ 53 < k := by
    change (-1022 - (k : Int) < -1075) ↔ _
    omega
  rw [underflow] at replay
  by_cases tiny : 53 < k
  · rw [if_pos tiny] at replay
    have small : j < 4 := bounds.2 tiny
    have zero : q = 0 := by
      dsimp only [q]
      rw [rundeInt_fall _ _ _ (by omega : 2 * (j % 8) < 8)]
      omega
    rw [replay]
    simp only [softCarryExp, softCarry, if_neg carry, zero]
    decide +kernel
  · rw [if_neg tiny] at replay
    rw [replay]
    simp only [softCarryExp, softCarry, if_neg carry, show (1 : Nat) < 2047 by decide,
      ite_true, show f64.p - 1 = 52 from rfl]
    by_cases sub : q < 2 ^ 52
    · simp only [if_pos sub]
    · have boundary : q = 2 ^ 52 := by omega
      simp only [if_neg sub, boundary, Nat.sub_self]

/-- Below-half, tie, above-half and gradual underflow exercise the same
    continuation, with both signs and a shift exceeding the word width. -/
theorem softMulUnderflow_zeuge :
    routineRoundPackWord 0 1 (floatShiftJamWord (BitVec.ofNat 64 (2 ^ 55)) 53) = 0 ∧
    routineRoundPackWord 1 1 (floatShiftJamWord (BitVec.ofNat 64 (2 ^ 55)) 54) =
      BitVec.ofNat 64 (2 ^ 63) ∧
    routineRoundPackWord 0 1 (floatShiftJamWord (BitVec.ofNat 64 (2 ^ 55 + 1)) 53) = 1 ∧
    routineRoundPackWord 0 1 (floatShiftJamWord (BitVec.ofNat 64 (2 ^ 55)) 1) =
      BitVec.ofNat 64 (2 ^ 51) ∧
    routineRoundPackWord 0 1 (floatShiftJamWord (BitVec.ofNat 64 (2 ^ 55)) 1071) = 0 := by
  decide +kernel

#print axioms softMulUnderflow_bounds
#print axioms softMulUnderflow_model
#print axioms softMulUnderflow_zeuge
end Gabbro.Stage0.Senke
