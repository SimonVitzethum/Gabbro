/- Complete integer-only binary64 multiplication routine.
   Canonical source correspondence is connected in FiniteModel and Correct. -/
module
public import Stage0.Senke.Gleit.Mul.Normalize
public import Stage0.Senke.Gleit.Mul.Special
public import Stage0.Senke.Gleit.Mul.Round
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- After operand normalization, only product bit 105 decides between the
    two possible guard shifts. The upper limb holds that bit at position 41. -/
def softMulFiniteDirectionalWord (a b : Runner.W) (k : Nat) : Runner.W :=
  softMulRoundWord (unpackSignWord a ^^^ unpackSignWord b)
    (softMulNormalizeIndexWord a + softMulNormalizeIndexWord b + BitVec.ofNat 64 k)
    (softMulCompressWord (softMulNormalizeWord a) (softMulNormalizeWord b) k)

def softMulFiniteWord (a b : Runner.W) : Runner.W :=
  if (mulHiW (softMulNormalizeWord a) (softMulNormalizeWord b)).ult (BitVec.ofNat 64 (2 ^ 41))
  then softMulFiniteDirectionalWord a b 49 else softMulFiniteDirectionalWord a b 50

/-- Dispatch precedes the finite continuation, including for either zero. -/
def softMulRoutineWord (a b : Runner.W) : Runner.W :=
  softMulSpecialWord a b (softMulFiniteWord a b)

def softMulFiniteDirectionalL (d : Nat) (a b : Nat → Option (List II × Nat)) (k : Nat) :
    Option (List II × Nat) :=
  let sign := fun j => xorSignL j (fun v => unpackSignL v a) (fun v => unpackSignL v b)
  let index := fun j => wordL 3 j (softMulNormalizeIndexL j a) (softMulNormalizeIndexL (j + 1) b)
  let total := fun j => wordK 3 j (index j) (Int.ofNat k)
  let magnitude := fun j => softMulCompressL j
    (fun v => softMulNormalizeL v a) (fun v => softMulNormalizeL v b) k
  softMulRoundL d sign total magnitude

def softMulFiniteL (d : Nat) (a b : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  let high := fun j => softMulHighL j (fun v => softMulNormalizeL v a) (fun v => softMulNormalizeL v b)
  let boundary := fun j => some (konstWL 4 (2 ^ 41) j)
  routineChooseL d (fun j => routineLessL j high boundary)
    (fun j => softMulFiniteDirectionalL j a b 49) (fun j => softMulFiniteDirectionalL j a b 50)

def softMulRoutineL (d : Nat) (a b : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  softMulSpecialL d a b (fun j => softMulFiniteL j a b)

/-- Compose the finite fragment from the existing word-code interfaces.
    Neither operand normalization nor compression assumes finite inputs here;
    semantic identification will apply only after the special dispatcher. -/
theorem softMulFiniteDirectionalL_word {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a b : Nat → Option (List II × Nat)} {av bv : Runner.W}
    (ha : WordCode (L := L) ρ W a av) (hb : WordCode (L := L) ρ W b bv)
    (k : Nat) (count : k = 49 ∨ k = 50) :
    WordCode (L := L) ρ W (fun d => softMulFiniteDirectionalL d a b k)
      (softMulFiniteDirectionalWord av bv k) := by
  have sign : WordCode (L := L) ρ W _ _ := xorSignL_ok (unpackSignL_ok ha) (unpackSignL_ok hb)
  have index : WordCode (L := L) ρ W _ _ := WordCode.bin (softMulNormalizeIndexL_word ha) (softMulNormalizeIndexL_word hb)
    (g := fun x y => some (x + y)) rfl rfl (by decide : 3 < 256)
  have literal : lit32 (Int.ofNat k) = true := by rcases count with rfl | rfl <;> decide
  have total : WordCode (L := L) ρ W _ _ := WordCode.bin index (WordCode.const _ literal)
    (g := fun x y => some (x + y)) rfl rfl (by decide : 3 < 256)
  have magnitude : WordCode (L := L) ρ W _ _ :=
    softMulCompressL_word (softMulNormalizeL_word ha) (softMulNormalizeL_word hb) k count
  have result : WordCode (L := L) ρ W _ _ := softMulRoundL_word sign total magnitude
  intro fp K d c top emitted fits m pc pre
  simpa only [softMulFiniteDirectionalL, softMulFiniteDirectionalWord, Int.ofNat_eq_coe,
    BitVec.ofInt_natCast] using
    result (fp := fp) (K := K) (d := d) (c := c) (top := top) emitted fits m pc pre

theorem softMulFiniteL_word {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a b : Nat → Option (List II × Nat)} {av bv : Runner.W}
    (ha : WordCode (L := L) ρ W a av) (hb : WordCode (L := L) ρ W b bv) :
    WordCode (L := L) ρ W (fun d => softMulFiniteL d a b) (softMulFiniteWord av bv) := by
  have high : WordCode (L := L) ρ W _ _ :=
    softMulHighL_word (softMulNormalizeL_word ha) (softMulNormalizeL_word hb)
  have condition : WordCode (L := L) ρ W _ _ :=
    routineLessL_ok high (WordCode.konst (2 ^ 41) (by decide))
  have result : WordCode (L := L) ρ W _ _ := routineChooseL_ok condition
    (fun _ => softMulFiniteDirectionalL_word ha hb 49 (Or.inl rfl))
    (fun _ => softMulFiniteDirectionalL_word ha hb 50 (Or.inr rfl))
  intro fp K d c top emitted fits m pc pre
  exact result (fp := fp) (K := K) (d := d) (c := c) (top := top) emitted fits m pc pre

/-- Execution correctness for the emitted integer instruction stream. -/
theorem softMulRoutineL_word {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a b : Nat → Option (List II × Nat)} {av bv : Runner.W}
    (ha : WordCode (L := L) ρ W a av) (hb : WordCode (L := L) ρ W b bv) :
    WordCode (L := L) ρ W (fun d => softMulRoutineL d a b) (softMulRoutineWord av bv) :=
  softMulSpecialL_word ha hb (softMulFiniteL_word ha hb)

/-- Fixtures cover both product leading-bit positions, retained rounding
    tails, subnormal output, invalid multiplication and signed underflow. -/
theorem softMulRoutineWord_zeuge :
    softMulRoutineWord (BitVec.ofNat 64 4609434218613702656)
      (BitVec.ofNat 64 4611686018427387904) = BitVec.ofNat 64 4613937818241073152 ∧
    softMulRoutineWord (BitVec.ofNat 64 4607182418800017409)
      (BitVec.ofNat 64 4607182418800017409) = BitVec.ofNat 64 4607182418800017410 ∧
    softMulRoutineWord (BitVec.ofNat 64 4503599627370496)
      (BitVec.ofNat 64 4602678819172646912) = BitVec.ofNat 64 2251799813685248 ∧
    softMulRoutineWord 0 (BitVec.ofNat 64 9218868437227405312) = BitVec.ofNat 64 9218868437227405313 ∧
    softMulRoutineWord (BitVec.ofNat 64 9223372036854775809) 1 = BitVec.ofNat 64 (2 ^ 63) := by
  decide +kernel

#print axioms softMulFiniteDirectionalL_word
#print axioms softMulFiniteL_word
#print axioms softMulRoutineL_word
#print axioms softMulRoutineWord_zeuge
end Gabbro.Stage0.Senke
