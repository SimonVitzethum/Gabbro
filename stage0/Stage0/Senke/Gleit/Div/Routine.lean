/- Binary64 division routine with shared unpacking, normalization and packing. -/
module
public import Stage0.Senke.Gleit.Div.Special
public import Stage0.Senke.Gleit.Div.Compress
public import Stage0.Senke.Gleit.Div.Normalize
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- The offset 2278 makes exponent differences unsigned. It is exactly the
    offset expected by the existing scaled round/underflow continuation. -/
def softDivFiniteDirectionalWord (a b : Runner.W) (k : Nat) : Runner.W :=
  softMulRoundWord (unpackSignWord a ^^^ unpackSignWord b)
    (softMulNormalizeIndexWord a + 2278 - softMulNormalizeIndexWord b - BitVec.ofNat 64 k)
    (BitVec.ofNat 64 (softDivJam ((softMulNormalizeWord a).toNat * 2 ^ k)
      (softMulNormalizeWord b).toNat))

def softDivFiniteWord (a b : Runner.W) : Runner.W :=
  if (softMulNormalizeWord a).ult (softMulNormalizeWord b)
  then softDivFiniteDirectionalWord a b 56 else softDivFiniteDirectionalWord a b 55

def softDivRoutineWord (a b : Runner.W) : Runner.W :=
  softDivSpecialWord a b (softDivFiniteWord a b)

def softDivFiniteDirectionalL (d : Nat) (a b : Nat → Option (List II × Nat)) (k : Nat) :
    Option (List II × Nat) :=
  let sign := fun j => xorSignL j (fun v => unpackSignL v a) (fun v => unpackSignL v b)
  let leftIndex := fun j => wordK 3 j (softMulNormalizeIndexL j a) 2278
  let difference := fun j => wordL 4 j (leftIndex j) (softMulNormalizeIndexL (j + 1) b)
  let total := fun j => wordK 4 j (difference j) (Int.ofNat k)
  let magnitude := fun j => softDivQuotientL j
    (fun v => softMulNormalizeL v a) (fun v => softMulNormalizeL v b) k
  softMulRoundL d sign total magnitude

def softDivFiniteL (d : Nat) (a b : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  let left := fun j => softMulNormalizeL j a
  let right := fun j => softMulNormalizeL j b
  routineChooseL d (fun j => routineLessL j left right)
    (fun j => softDivFiniteDirectionalL j a b 56) (fun j => softDivFiniteDirectionalL j a b 55)

def softDivRoutineL (d : Nat) (a b : Nat → Option (List II × Nat)) :
    Option (List II × Nat) := softDivSpecialL d a b (fun j => softDivFiniteL j a b)

/-- Emit the exact restoring quotient, then reuse the complete rounding
    continuation. The numerator-width premise belongs to integer division. -/
theorem softDivFiniteDirectionalL_word {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a b : Nat → Option (List II × Nat)} {av bv : Runner.W}
    (ha : WordCode (L := L) ρ W a av) (hb : WordCode (L := L) ρ W b bv)
    (k : Nat) (count : k = 55 ∨ k = 56)
    (positive : 0 < (softMulNormalizeWord bv).toNat)
    (width : (softMulNormalizeWord av).toNat * 2 ^ k < 2 ^ 128) :
    WordCode (L := L) ρ W (fun d => softDivFiniteDirectionalL d a b k)
      (softDivFiniteDirectionalWord av bv k) := by
  have sign := xorSignL_ok (unpackSignL_ok ha) (unpackSignL_ok hb)
  have leftIndex : WordCode (L := L) ρ W _ _ := WordCode.bin (softMulNormalizeIndexL_word ha) (WordCode.const 2278 (by decide))
    (g := fun x y => some (x + y)) rfl rfl (by decide : 3 < 256)
  have difference : WordCode (L := L) ρ W _ _ := WordCode.bin leftIndex (softMulNormalizeIndexL_word hb)
    (g := fun x y => some (x - y)) rfl rfl (by decide : 4 < 256)
  have literal : lit32 (Int.ofNat k) = true := by rcases count with rfl | rfl <;> decide
  have total : WordCode (L := L) ρ W _ _ := WordCode.bin difference (WordCode.const _ literal)
    (g := fun x y => some (x - y)) rfl rfl (by decide : 4 < 256)
  have left := softMulNormalizeL_word ha
  have right := softMulNormalizeL_word hb
  have encodeA : softMulNormalizeWord av = BitVec.ofNat 64 (softMulNormalizeWord av).toNat := by simp
  have encodeB : softMulNormalizeWord bv = BitVec.ofNat 64 (softMulNormalizeWord bv).toNat := by simp
  rw [encodeA] at left
  rw [encodeB] at right
  have quotient := softDivQuotientL_ok left right (softMulNormalizeWord av).isLt positive
    (softMulNormalizeWord bv).isLt count width
  exact softMulRoundL_word sign total quotient

/-- Both normalization directions fit the restoring loop's two-limb input.
    The comparison selects the shift, not a separate arithmetic operation. -/
theorem softDivFiniteL_word {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a b : Nat → Option (List II × Nat)} {av bv : Runner.W}
    (ha : WordCode (L := L) ρ W a av) (hb : WordCode (L := L) ρ W b bv)
    (positive : 0 < (softMulNormalizeWord bv).toNat)
    (bound : (softMulNormalizeWord av).toNat < 2 ^ 53) :
    WordCode (L := L) ρ W (fun d => softDivFiniteL d a b) (softDivFiniteWord av bv) := by
  have width (k : Nat) (count : k = 55 ∨ k = 56) :
      (softMulNormalizeWord av).toNat * 2 ^ k < 2 ^ 128 := by
    rcases count with rfl | rfl
    · have := Nat.mul_lt_mul_of_pos_right bound (by decide : 0 < 2 ^ 55)
      omega
    · have := Nat.mul_lt_mul_of_pos_right bound (by decide : 0 < 2 ^ 56)
      omega
  exact routineChooseL_ok
    (routineLessL_ok (softMulNormalizeL_word ha) (softMulNormalizeL_word hb))
    (fun _ => softDivFiniteDirectionalL_word ha hb 56 (Or.inr rfl) positive (width 56 (Or.inr rfl)))
    (fun _ => softDivFiniteDirectionalL_word ha hb 55 (Or.inl rfl) positive (width 55 (Or.inl rfl)))

/-- Word fixtures cover normal rounding, gradual underflow and both invalid
    and infinite results. The raw routine admits all binary64 bit patterns. -/
theorem softDivRoutineWord_zeuge :
    softDivRoutineWord (BitVec.ofNat 64 4613937818241073152)
      (BitVec.ofNat 64 4611686018427387904) = BitVec.ofNat 64 4609434218613702656 ∧
    softDivRoutineWord (BitVec.ofNat 64 4607182418800017408)
      (BitVec.ofNat 64 4613937818241073152) = BitVec.ofNat 64 4599676419421066581 ∧
    softDivRoutineWord (BitVec.ofNat 64 4503599627370496)
      (BitVec.ofNat 64 4611686018427387904) = BitVec.ofNat 64 2251799813685248 ∧
    softDivRoutineWord (BitVec.ofNat 64 4607182418800017408) 0 = BitVec.ofNat 64 9218868437227405312 ∧
    softDivRoutineWord 0 0 = BitVec.ofNat 64 9218868437227405313 := by
  decide +kernel

#print axioms softDivFiniteDirectionalL_word
#print axioms softDivFiniteL_word
#print axioms softDivRoutineWord_zeuge
end Gabbro.Stage0.Senke
