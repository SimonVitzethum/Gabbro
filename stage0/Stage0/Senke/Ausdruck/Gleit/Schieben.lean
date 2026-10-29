/- Saturating right shift with sticky information for significand alignment. -/
import Stage0.Senke.Ausdruck.Gleit.Komposition

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Mathematical word alignment: a count at least 64 discards the whole word.
    The low result bit records whether any discarded bit was nonzero. -/
def floatShiftJamWord (a k : Runner.W) : Runner.W :=
  let q := a >>> k.toNat
  q ||| Runner.IR.bool (!(a == (q <<< k.toNat)))

/-- IR shifts mask the count modulo 64. A separate unsigned high-count test
    makes their quotient saturate, even for counts with the sign bit set. -/
def floatShiftQuotL (d : Nat) (a k : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  let q := fun d => wordL 12 d (a d) (k (d + 1))
  let small := fun d => wordK 14 d (wordK 12 d (k d) 6) 0
  wordL 5 d (q d) (small (d + 1))

def floatShiftJamL (d : Nat) (a k : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  let q := fun d => floatShiftQuotL d a k
  let back := fun d => wordL 11 d (q d) (k (d + 1))
  let same := fun d => wordL 14 d (a d) (back (d + 1))
  let lost := fun d => wordL 4 d (some ([ci 1 d 1 0], d + 1)) (same (d + 1))
  wordL 9 d (q d) (lost (d + 1))

theorem floatShiftQuotWord_model (a k : Runner.W) :
    (a >>> (k.toNat % 64)) * Runner.IR.bool ((k >>> 6) == 0) = a >>> k.toNat := by
  have small : ((k >>> 6) == 0) = decide (k.toNat < 64) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, ← BitVec.toNat_inj, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, decide_eq_true_eq, BitVec.ofNat_eq_ofNat,
      BitVec.toNat_ofNat]
    change k.toNat / 64 = 0 ↔ k.toNat < 64
    omega
  rw [small]
  by_cases hk : k.toNat < 64
  · simp only [hk, decide_true, Runner.IR.bool, ↓reduceIte]
    change (a >>> (k.toNat % 64)) * (1#64) = _
    rw [BitVec.mul_one, Nat.mod_eq_of_lt hk]
  · simp only [hk, decide_false, Runner.IR.bool, Bool.false_eq_true, ↓reduceIte]
    change (a >>> (k.toNat % 64)) * (0#64) = _
    rw [BitVec.mul_zero, BitVec.ushiftRight_eq_zero (by omega)]

theorem floatShiftBackWord_model (a k : Runner.W) :
    (a >>> k.toNat) <<< (k.toNat % 64) = (a >>> k.toNat) <<< k.toNat := by
  by_cases hk : k.toNat < 64
  · rw [Nat.mod_eq_of_lt hk]
  · rw [BitVec.ushiftRight_eq_zero (by omega)]
    simp

theorem floatShiftBackWord_toNat (a : Runner.W) (k : Nat) :
    ((a >>> k) <<< k).toNat = a.toNat / 2^k * 2^k := by
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) a.isLt)

/-- The sticky bit is exactly the nonzero remainder of division by the alignment power. -/
theorem floatShiftJamWord_model (a k : Runner.W) :
    floatShiftJamWord a k = (a >>> k.toNat) |||
      Runner.IR.bool (decide (a.toNat % 2^k.toNat ≠ 0)) := by
  have back := floatShiftBackWord_toNat a k.toNat
  have same : (a == ((a >>> k.toNat) <<< k.toNat)) =
      decide (a.toNat % 2^k.toNat = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, ← BitVec.toNat_inj, back, decide_eq_true_eq]
    have := Nat.mod_add_div a.toNat (2^k.toNat)
    rw [Nat.mul_comm (2^k.toNat)] at this
    omega
  dsimp only [floatShiftJamWord]
  rw [same]
  by_cases h : a.toNat % 2^k.toNat = 0 <;> simp [h]

theorem floatShiftQuotL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a k : Nat → Option (List II × Nat)} {av kv : Runner.W}
    (ha : WordCode (L := L) ρ W a av) (hk : WordCode (L := L) ρ W k kv) :
    WordCode (L := L) ρ W (fun d => floatShiftQuotL d a k) (av >>> kv.toNat) := by
  have q : WordCode (L := L) ρ W _ _ := WordCode.bin ha hk
    (g := fun a b => some (a >>> (b.toNat % 64))) rfl rfl (by decide : 12 < 256)
  have high : WordCode (L := L) ρ W _ _ := WordCode.bin hk
    (WordCode.const 6 (by decide)) (g := fun a b => some (a >>> (b.toNat % 64)))
    rfl rfl (by decide : 12 < 256)
  have small : WordCode (L := L) ρ W _ _ := WordCode.bin high
    (WordCode.const 0 (by decide)) (g := fun a b => some (Runner.IR.bool (a == b)))
    rfl rfl (by decide : 14 < 256)
  have result : WordCode (L := L) ρ W _ _ := WordCode.bin q small
    (g := fun a b => some (a * b)) rfl rfl (by decide : 5 < 256)
  intro fp K d c top h hK m pc hp
  have res := result (fp := fp) (K := K) (d := d) (c := c) (top := top) h hK m pc hp
  apply res.mono
  intro w hw
  have eq := floatShiftQuotWord_model av kv
  simpa only [BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat] using hw.trans eq

theorem floatShiftJamL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a k : Nat → Option (List II × Nat)} {av kv : Runner.W}
    (ha : WordCode (L := L) ρ W a av) (hk : WordCode (L := L) ρ W k kv) :
    WordCode (L := L) ρ W (fun d => floatShiftJamL d a k) (floatShiftJamWord av kv) := by
  have q : WordCode (L := L) ρ W _ _ := floatShiftQuotL_ok ha hk
  have back : WordCode (L := L) ρ W _ _ := WordCode.bin q hk
    (g := fun a b => some (a <<< (b.toNat % 64))) rfl rfl (by decide : 11 < 256)
  have same : WordCode (L := L) ρ W _ _ := WordCode.bin ha back
    (g := fun a b => some (Runner.IR.bool (a == b))) rfl rfl (by decide : 14 < 256)
  have lost : WordCode (L := L) ρ W _ _ := WordCode.bin
    (WordCode.const 1 (by decide)) same (g := fun a b => some (a - b))
    rfl rfl (by decide : 4 < 256)
  have result : WordCode (L := L) ρ W _ _ := WordCode.bin q lost
    (g := fun a b => some (a ||| b)) rfl rfl (by decide : 9 < 256)
  intro fp K d c top h hK m pc hp
  have res := result (fp := fp) (K := K) (d := d) (c := c) (top := top) h hK m pc hp
  apply res.mono
  intro w hw
  have hn (b : Bool) : (1 : Runner.W) - Runner.IR.bool b = Runner.IR.bool (!b) := by
    cases b <;> decide
  simp only [BitVec.ofInt_ofNat, ← BitVec.ofNat_eq_ofNat, floatShiftBackWord_model, hn] at hw
  exact hw

/-- Counts at and beyond the word width saturate instead of wrapping. -/
theorem floatShiftJamWord_model_zeuge :
    floatShiftJamWord 11 0 = 11 ∧ floatShiftJamWord 11 1 = 5 ∧
    floatShiftJamWord 13 1 = 7 ∧ floatShiftJamWord 12 1 = 6 ∧
    floatShiftJamWord 0 64 = 0 ∧ floatShiftJamWord 12 64 = 1 ∧
    floatShiftJamWord (BitVec.ofNat 64 (2^63)) 63 = 1 ∧
    floatShiftJamWord 42 (BitVec.ofNat 64 (2^64 - 1)) = 1 := by decide +kernel

theorem floatShiftQuotL_ok_zeuge {Γ : Ctx} (ρ : Env D Γ) (W : Runner.Mem → Prop) :
    WordCode (L := L) ρ W (fun d => floatShiftQuotL d
      (fun j => some ([ci 1 j 13 0], j + 1))
      (fun j => some ([ci 1 j 1 0], j + 1))) 6 ∧
    (floatShiftQuotL 8 (fun j => some ([ci 1 j 13 0], j + 1))
      (fun j => some ([ci 1 j 1 0], j + 1))).isSome = true := by
  constructor
  · intro fp K d c top h hK m pc hp
    have result : WordCode (L := L) ρ W _ _ := floatShiftQuotL_ok
      (WordCode.const 13 (by decide)) (WordCode.const 1 (by decide))
    have hx : BitVec.ofInt 64 13 >>> (BitVec.ofInt 64 1).toNat = 6 := by decide
    rw [hx] at result
    exact result h hK m pc hp
  · decide +kernel

theorem floatShiftJamL_ok_zeuge {Γ : Ctx} (ρ : Env D Γ) (W : Runner.Mem → Prop) :
    WordCode (L := L) ρ W (fun d => floatShiftJamL d
      (fun j => some ([ci 1 j 13 0], j + 1))
      (fun j => some ([ci 1 j 1 0], j + 1))) 7 ∧
    (floatShiftJamL 8 (fun j => some ([ci 1 j 13 0], j + 1))
      (fun j => some ([ci 1 j 1 0], j + 1))).isSome = true := by
  constructor
  · intro fp K d c top h hK m pc hp
    have result : WordCode (L := L) ρ W _ _ := floatShiftJamL_ok
      (WordCode.const 13 (by decide)) (WordCode.const 1 (by decide))
    have hx : floatShiftJamWord (BitVec.ofInt 64 13) (BitVec.ofInt 64 1) = 7 := by decide
    rw [hx] at result
    exact result h hK m pc hp
  · decide +kernel

end Gabbro.Stage0.Senke
