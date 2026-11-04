/- The emitted finite normalization rounds its actual aligned magnitude. -/
module
public import Stage0.Senke.Gleit.Normal.Routine
public import Stage0.Senke.Gleit.Normal.Interval
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR

/-- The nonzero finite continuation is canonical rounding of the aligned
    word at its guard-bit scale. Left normalization is lossless; the right
    branch retains the discarded bit through the same sticky certificate. -/
theorem routineFiniteDirectionalWord_exact (large small : Runner.W) (s : Bool) (n e : Nat)
    (magnitude : routineDirectionalWord large small = BitVec.ofNat 64 n)
    (index : routineIndexWord large = BitVec.ofNat 64 e)
    (sign : unpackSignWord large = Runner.IR.bool s)
    (np : 4 ≤ n) (nb : n < 2 ^ 57) (ep : 1 ≤ e) (eb : e ≤ 2046) :
    routineFiniteDirectionalWord large small =
      BitVec.ofNat 64 (zuBits f64
        (rundeExakt f64 ⟨if s then -(n : Int) else (n : Int), (e : Int) - 1078⟩)) := by
  have n64 : n < 2 ^ 64 := by omega
  have e64 : e < 2 ^ 64 := by omega
  have nonzero : ¬ (BitVec.ofNat 64 n == 0) = true := by
    intro zero
    have same := congrArg BitVec.toNat (beq_iff_eq.mp zero)
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt n64,
      show (0 : Runner.W).toNat = 0 from rfl] at same
    omega
  have compare : (BitVec.ofNat 64 n).ult (BitVec.ofNat 64 (2 ^ 56)) =
      decide (n < 2 ^ 56) := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt n64,
      Nat.mod_eq_of_lt (by decide : 2 ^ 56 < 2 ^ 64)]
  unfold routineFiniteDirectionalWord
  rw [magnitude, index, sign, if_neg nonzero, compare]
  by_cases left : n < 2 ^ 56
  · simp only [left, decide_true, ite_true]
    have bounds := routineLeftCount_bounds n e np left ep
    have normalized := routineLeftCount_normalizes n e np left ep
    let c := routineLeftCount n e
    have cp : c < e := bounds.2.2.2.2
    have clt : c < 64 := bounds.2.2.2.1
    have c64 : c < 2 ^ 64 := by have := bounds.2.2.1; omega
    have shift : (BitVec.ofNat 64 n) <<< ((BitVec.ofNat 64 c).toNat % 64) =
        BitVec.ofNat 64 (n * 2 ^ c) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt c64, Nat.mod_eq_of_lt clt,
        Nat.mod_eq_of_lt n64, Nat.shiftLeft_eq]
    have sub : BitVec.ofNat 64 e - BitVec.ofNat 64 c = BitVec.ofNat 64 (e - c) :=
      BitVec.ofNat_sub_ofNat_of_le _ _ c64 (by omega)
    rw [routineLeftCountWord_model n e np left ep e64, sub, shift]
    have power := Nat.two_pow_pos c
    have low : 4 ≤ n * 2 ^ c := by nlinarith
    rw [routineRoundPackWord_exact s (e - c) (n * 2 ^ c)
      (by omega) (by omega) low normalized.1 normalized.2]
    apply congrArg (fun a : GFloat => BitVec.ofNat 64 (zuBits f64 a))
    have exactScale := softRound_signed_mul_pow s n c (((e - c : Nat) : Int) - 1078)
      (by omega)
    have scale : (((e - c : Nat) : Int) - 1078) + (c : Int) = (e : Int) - 1078 := by omega
    rwa [scale] at exactScale
  · simp only [left, decide_false, Bool.false_eq_true, ite_false]
    let j := softShiftJamNat n 1
    have interval := softShiftJamNat_interval n 1
    have certificate : n = j * 2 ^ 1 ∨
        (j % 2 = 1 ∧ (j - 1) * 2 ^ 1 < n ∧ n < (j + 1) * 2 ^ 1) := by
      rcases interval with exactValue | jam
      · exact Or.inl exactValue.2
      · exact Or.inr jam
    have jb : 2 ^ 55 ≤ j ∧ j < 2 ^ 56 := by
      rcases certificate with exactValue | ⟨odd, lo, hi⟩ <;> omega
    have bits : bitlen j = 56 := bitlen_unique j 56 jb.1 jb.2 (by omega)
    have jam : floatShiftJamWord (BitVec.ofNat 64 n) 1 = BitVec.ofNat 64 j := by
      have result := congrArg (BitVec.ofNat 64) (floatShiftJamWord_nat (BitVec.ofNat 64 n) 1)
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt n64, show (1 : Runner.W).toNat = 1 from rfl] using result
    have add : BitVec.ofNat 64 e + 1 = BitVec.ofNat 64 (e + 1) := by
      rw [BitVec.ofNat_add]
      rfl
    rw [add, jam, routineRoundPackWord_exact s (e + 1) j
      (by omega) (by omega) (by omega) jb.2 (Or.inl jb.1)]
    apply congrArg (fun a : GFloat => BitVec.ofNat 64 (zuBits f64 a))
    have aligned := softRound_signed_interval s j n 1 (((e + 1 : Nat) : Int) - 1078)
      (by omega) (by rw [bits]; change (-1022 : Int) ≤ _; omega) certificate
    have scale : (((e + 1 : Nat) : Int) - 1078) - (1 : Nat) = (e : Int) - 1078 := by omega
    rw [scale] at aligned
    exact aligned.symm

/-- Cancellation is selected before sign packing, so its result is the
    canonical positive zero, independently of the larger operand's sign. -/
theorem routineFiniteDirectionalWord_zero (large small : Runner.W)
    (zero : routineDirectionalWord large small = 0) :
    routineFiniteDirectionalWord large small = 0 := by
  simp only [routineFiniteDirectionalWord, zero, beq_self_eq_true, ite_true]

/-- Actual finite operands jointly satisfy the normalization premises on
    both branches. The cancellation fixture also tests the zero shortcut. -/
theorem routineFiniteDirectionalWord_exact_zeuge :
    let one := BitVec.ofNat 64 4607182418800017408
    let two := BitVec.ofNat 64 4611686018427387904
    let minusOne := BitVec.ofNat 64 13830554455654793216
    routineDirectionalWord two one = BitVec.ofNat 64 (3 * 2 ^ 54) ∧
    routineIndexWord two = 1024 ∧ unpackSignWord two = 0 ∧
    routineFiniteDirectionalWord two one = BitVec.ofNat 64 (zuBits f64
      (rundeExakt f64 ⟨3 * 2 ^ 54, -54⟩)) ∧
    routineDirectionalWord two two = BitVec.ofNat 64 (2 ^ 56) ∧
    routineFiniteDirectionalWord two two = BitVec.ofNat 64 (zuBits f64
      (rundeExakt f64 ⟨2 ^ 56, -54⟩)) ∧
    routineDirectionalWord one minusOne = 0 ∧
    routineFiniteDirectionalWord one minusOne = 0 := by
  decide +kernel

#print axioms routineFiniteDirectionalWord_exact
#print axioms routineFiniteDirectionalWord_zero
#print axioms routineFiniteDirectionalWord_exact_zeuge
end Gabbro.Stage0.Senke
