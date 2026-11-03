/- Lossless normalization of multiplication operands, including subnormals.
   A 64-point offset keeps every effective exponent index nonnegative. -/
module
public import Stage0.Senke.Gleit.Normal.Search
public import Stage0.Senke.Gleit.RoutineOrderModel
public import Stage0.Senke.Gleit.Normal.Signed
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR Runner.Mem

/-- The significand has at most 53 bits. Shift only the missing leading bits. -/
def softMulNormalizeCount (n : Nat) : Nat := 53 - bitlen n

def softMulNormalizeWord (a : Runner.W) : Runner.W :=
  let sig := routineSigWord a
  sig <<< ((routineLeadingZerosWord sig - 11).toNat % 64)

def softMulNormalizeIndexWord (a : Runner.W) : Runner.W :=
  routineIndexWord a + 64 - (routineLeadingZerosWord (routineSigWord a) - 11)

/-- Positive source significands normalize exactly into the 53-bit interval. -/
theorem softMulNormalize_bounds (n : Nat) (positive : 0 < n) (bound : n < 2 ^ 53) :
    1 ≤ bitlen n ∧ bitlen n ≤ 53 ∧ softMulNormalizeCount n ≤ 52 ∧
      2 ^ 52 ≤ n * 2 ^ softMulNormalizeCount n ∧
      n * 2 ^ softMulNormalizeCount n < 2 ^ 53 := by
  have lo := bitlen_untere n (by omega : n ≠ 0)
  have hi := bitlen_obere n
  have bp : 1 ≤ bitlen n := by
    by_contra h
    have zero : bitlen n = 0 := by omega
    rw [zero] at hi
    omega
  have bb : bitlen n ≤ 53 := by
    by_contra h
    have power := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show 54 ≤ bitlen n by omega)
    omega
  have cp : softMulNormalizeCount n ≤ 52 := by unfold softMulNormalizeCount; omega
  have lower : 2 ^ (bitlen n - 1) ≤ n := by
    rw [show bitlen n = bitlen n - 1 + 1 by omega, Nat.pow_succ] at lo
    omega
  have low := Nat.mul_le_mul_right (2 ^ softMulNormalizeCount n) lower
  have high := Nat.mul_lt_mul_of_pos_right hi (Nat.two_pow_pos (softMulNormalizeCount n))
  have lp : 2 ^ (bitlen n - 1) * 2 ^ softMulNormalizeCount n = 2 ^ 52 := by
    rw [← Nat.pow_add]
    congr 1
    unfold softMulNormalizeCount
    omega
  have hp : 2 ^ bitlen n * 2 ^ softMulNormalizeCount n = 2 ^ 53 := by
    rw [← Nat.pow_add]
    congr 1
    unfold softMulNormalizeCount
    omega
  rw [lp] at low
  rw [hp] at high
  exact ⟨bp, bb, cp, low, high⟩

variable [Kern] {D : Deklaration} {L : Lay D}

def softMulNormalizeCountL (d : Nat) (a : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wordK 4 d (routineLeadingZerosL d (fun j => routineSigL j a)) 11

def softMulNormalizeL (d : Nat) (a : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wordL 11 d (routineSigL d a) (softMulNormalizeCountL (d + 1) a)

def softMulNormalizeIndexL (d : Nat) (a : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wordL 4 d (wordK 3 d (routineIndexL d a) 64) (softMulNormalizeCountL (d + 1) a)

theorem softMulNormalizeCountL_word {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a : Nat → Option (List II × Nat)} {av : Runner.W}
    (ha : WordCode (L := L) ρ W a av) :
    WordCode (L := L) ρ W (fun d => softMulNormalizeCountL d a)
      (routineLeadingZerosWord (routineSigWord av) - 11) :=
  WordCode.bin (routineLeadingZerosL_word (routineSigL_ok ha)) (WordCode.const 11 (by decide))
    (g := fun x y => some (x - y)) rfl rfl (by decide : 4 < 256)

theorem softMulNormalizeL_word {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a : Nat → Option (List II × Nat)} {av : Runner.W}
    (ha : WordCode (L := L) ρ W a av) :
    WordCode (L := L) ρ W (fun d => softMulNormalizeL d a) (softMulNormalizeWord av) :=
  WordCode.bin (routineSigL_ok ha) (softMulNormalizeCountL_word ha)
    (g := fun x y => some (x <<< (y.toNat % 64))) rfl rfl (by decide : 11 < 256)

theorem softMulNormalizeIndexL_word {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a : Nat → Option (List II × Nat)} {av : Runner.W}
    (ha : WordCode (L := L) ρ W a av) :
    WordCode (L := L) ρ W (fun d => softMulNormalizeIndexL d a)
      (softMulNormalizeIndexWord av) := by
  have index := WordCode.bin (routineIndexL_ok ha) (WordCode.const 64 (by decide))
    (g := fun x y => some (x + y)) rfl rfl (by decide : 3 < 256)
  exact WordCode.bin index (softMulNormalizeCountL_word ha)
    (g := fun x y => some (x - y)) rfl rfl (by decide : 4 < 256)

/-- The actual shift equals multiplication by the exact power of two;
    its count cannot wrap or shift past the machine-word boundary. -/
theorem softMulNormalizeWord_model (a : GFloat) (ha : wf f64 a)
    (positive : 0 < softSig a.bexp a.frac) :
    let n := softSig a.bexp a.frac
    let c := softMulNormalizeCount n
    let word := BitVec.ofNat 64 (zuBits f64 a)
    softMulNormalizeWord word = BitVec.ofNat 64 (n * 2 ^ c) ∧
      softMulNormalizeIndexWord word = BitVec.ofNat 64 (max a.bexp 1 + 64 - c) := by
  dsimp only
  let n := softSig a.bexp a.frac
  let c := softMulNormalizeCount n
  have nb : n < 2 ^ 53 := by
    have fraction := ha.2
    change a.frac < 2 ^ 52 at fraction
    dsimp only [n, softSig]
    split <;> omega
  have bounds := softMulNormalize_bounds n positive nb
  have n64 : n < 2 ^ 64 := by omega
  have c64 : c < 2 ^ 64 := by have := bounds.2.2.1; omega
  have count : routineLeadingZerosWord (BitVec.ofNat 64 n) - 11 = BitVec.ofNat 64 c := by
    rw [routineLeadingZerosWord_model, BitVec.toNat_ofNat, Nat.mod_eq_of_lt n64,
      show (11 : Runner.W) = BitVec.ofNat 64 11 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
    dsimp only [c, softMulNormalizeCount]
    omega
  obtain ⟨sig, index⟩ := routineSigIndex_canonical a ha
  simp only [softMulNormalizeWord, softMulNormalizeIndexWord, sig, index, count]
  constructor
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt c64,
      Nat.mod_eq_of_lt (by have := bounds.2.2.1; omega : c < 64),
      Nat.mod_eq_of_lt n64, Nat.shiftLeft_eq]
  · have ep : 1 ≤ max a.bexp 1 := Nat.le_max_right _ _
    rw [show (64 : Runner.W) = BitVec.ofNat 64 64 from rfl, BitVec.ofNat_add,
      BitVec.ofNat_sub_ofNat_of_le _ _ c64 (by have := bounds.2.2.1; omega)]

/-- Normal inputs require no shift; the least subnormal uses all 52 places. -/
theorem softMulNormalize_zeuge :
    softMulNormalizeCount (2 ^ 52) = 0 ∧ softMulNormalizeCount 1 = 52 ∧
    softMulNormalizeWord 1 = BitVec.ofNat 64 (2 ^ 52) ∧
    softMulNormalizeIndexWord 1 = 13 ∧
    softMulNormalizeIndexWord (BitVec.ofNat 64 4607182418800017408) = 1087 := by
  decide +kernel

#print axioms softMulNormalize_bounds
#print axioms softMulNormalizeL_word
#print axioms softMulNormalizeIndexL_word
#print axioms softMulNormalizeWord_model
#print axioms softMulNormalize_zeuge
end Gabbro.Stage0.Senke
