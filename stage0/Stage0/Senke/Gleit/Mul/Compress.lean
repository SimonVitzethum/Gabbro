/- Compress a normalized 106-bit product to 56 guard/sticky bits.
   The two fixed shifts avoid a variable-width 128-bit operation in the IR. -/
module
public import Stage0.Senke.Gleit.Mul.Product
public import Stage0.Senke.Gleit.Sticky.Round
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR Runner.Mem

/-- Arithmetic characterization of jam, useful when the exact numerator is
    wider than a word. Its quotient's upper bits and its parity are retained. -/
theorem softMulJam_data (n k : Nat) :
    (softShiftJamNat n k) / 2 = (n / 2 ^ k) / 2 ∧
      (softShiftJamNat n k) % 2 =
        if n % 2 ^ k = 0 then (n / 2 ^ k) % 2 else 1 := by
  unfold softShiftJamNat
  rw [Nat.shiftRight_eq_div_pow]
  by_cases tail : n % 2 ^ k = 0
  · simp only [tail, ite_true, Nat.or_zero, and_self]
  · simp only [tail, ite_false]
    constructor
    · rw [Nat.or_div_two]
      simp
    · exact Nat.or_mod_two_eq_one.mpr (Or.inr rfl)

/-- A high limb is an even multiple at either supported rounding position.
    Adding it cannot change whether a discarded low tail sets the sticky bit. -/
theorem softMulJam_split (lo hi k : Nat) (count : k = 49 ∨ k = 50) :
    softShiftJamNat (lo + hi * 2 ^ 64) k =
      softShiftJamNat lo k + hi * 2 ^ (64 - k) := by
  have left := softMulJam_data (lo + hi * 2 ^ 64) k
  have right := softMulJam_data lo k
  have tail : (lo + hi * 2 ^ 64) % 2 ^ k = lo % 2 ^ k := by
    rcases count with rfl | rfl <;> omega
  rw [tail] at left
  by_cases exactTail : lo % 2 ^ k = 0
  · rw [if_pos exactTail] at left right
    rcases count with rfl | rfl <;> omega
  · rw [if_neg exactTail] at left right
    rcases count with rfl | rfl <;> omega

/-- Sticky compression cannot cross either even power-of-two boundary. -/
theorem softMulJam_bounds (n k : Nat) (count : k = 49 ∨ k = 50)
    (low : 2 ^ (k + 55) ≤ n) (high : n < 2 ^ (k + 56)) :
    2 ^ 55 ≤ softShiftJamNat n k ∧ softShiftJamNat n k < 2 ^ 56 := by
  have interval := softShiftJamNat_interval n k
  rcases count with rfl | rfl <;>
    rcases interval with ⟨_, exactValue⟩ | ⟨odd, lo, hi⟩ <;> omega

/-- Reuse the existing saturating shift/jam on the low limb. The high limb
    contributes bits 15..55 or 14..55 by a lossless left shift. -/
def softMulCompressWord (a b : Runner.W) (k : Nat) : Runner.W :=
  floatShiftJamWord (a * b) (BitVec.ofNat 64 k) + (mulHiW a b <<< (64 - k))

variable [Kern] {D : Deklaration} {L : Lay D}

def softMulCompressL (d : Nat) (a b : Nat → Option (List II × Nat)) (k : Nat) :
    Option (List II × Nat) :=
  let low := fun j => wordL 5 j (a j) (b (j + 1))
  let high := fun j => softMulHighL j a b
  let jam := fun j => floatShiftJamL j low
    (fun v => some ([ci 1 v (Int.ofNat k) 0], v + 1))
  wordL 3 d (jam d) (wordK 11 (d + 1) (high (d + 1)) (Int.ofNat (64 - k)))

theorem softMulCompressL_word {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a b : Nat → Option (List II × Nat)} {av bv : Runner.W}
    (ha : WordCode (L := L) ρ W a av) (hb : WordCode (L := L) ρ W b bv)
    (k : Nat) (count : k = 49 ∨ k = 50) :
    WordCode (L := L) ρ W (fun d => softMulCompressL d a b k)
      (softMulCompressWord av bv k) := by
  have low : WordCode (L := L) ρ W _ _ := WordCode.bin ha hb (g := fun x y => some (x * y))
    rfl rfl (by decide : 5 < 256)
  have literal : lit32 (Int.ofNat k) = true := by rcases count with rfl | rfl <;> decide
  have leftLiteral : lit32 (Int.ofNat (64 - k)) = true := by
    rcases count with rfl | rfl <;> decide
  have shift : (BitVec.ofInt 64 (Int.ofNat (64 - k))).toNat % 64 = 64 - k := by
    rcases count with rfl | rfl <;> decide
  have jam := floatShiftJamL_ok low (WordCode.const _ literal)
  have high : WordCode (L := L) ρ W _ _ := WordCode.bin (softMulHighL_word ha hb) (WordCode.const _ leftLiteral)
    (g := fun x y => some (x <<< (y.toNat % 64))) rfl rfl (by decide : 11 < 256)
  rw [shift] at high
  exact WordCode.bin jam high (g := fun x y => some (x + y))
    rfl rfl (by decide : 3 < 256)

/-- Relate the compressed word to the full product, not to its wrapped low
    limb. Every discarded product bit is represented by the sticky bit. -/
theorem softMulCompressWord_model (a b : Runner.W) (k : Nat)
    (count : k = 49 ∨ k = 50)
    (low : 2 ^ (k + 55) ≤ a.toNat * b.toNat)
    (high : a.toNat * b.toNat < 2 ^ (k + 56)) :
    softMulCompressWord a b k =
      BitVec.ofNat 64 (softShiftJamNat (a.toNat * b.toNat) k) := by
  have limbs := softMulProduct_limbs a b
  have bounds := softMulJam_bounds (a.toNat * b.toNat) k count low high
  have split := softMulJam_split (a * b).toNat (mulHiW a b).toNat k count
  rw [limbs] at split
  have k64 : k < 2 ^ 64 := by rcases count with rfl | rfl <;> decide
  have highBound : (mulHiW a b).toNat * 2 ^ (64 - k) < 2 ^ 64 := by
    rcases count with rfl | rfl <;> omega
  apply BitVec.eq_of_toNat_eq
  simp only [softMulCompressWord, BitVec.toNat_add, floatShiftJamWord_nat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt k64, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt highBound]
  rw [← split]

/-- Both possible leading positions exercise a nonzero discarded tail. -/
theorem softMulCompress_zeuge :
    softMulCompressWord (BitVec.ofNat 64 (2 ^ 52 + 1))
      (BitVec.ofNat 64 (2 ^ 52 + 1)) 49 = BitVec.ofNat 64 (2 ^ 55 + 17) ∧
    softMulCompressWord (BitVec.ofNat 64 (2 ^ 53 - 1))
      (BitVec.ofNat 64 (2 ^ 53 - 1)) 50 = BitVec.ofNat 64 (2 ^ 56 - 15) := by
  decide +kernel

#print axioms softMulJam_split
#print axioms softMulJam_bounds
#print axioms softMulCompressL_word
#print axioms softMulCompressWord_model
#print axioms softMulCompress_zeuge
end Gabbro.Stage0.Senke
