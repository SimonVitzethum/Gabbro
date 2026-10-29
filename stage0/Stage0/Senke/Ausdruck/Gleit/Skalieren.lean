/- Quotient/remainder scaling followed by G's nearest-even rounding. -/
import Stage0.Senke.Ausdruck.Gleit.RundCode
import Stage0.Senke.Ausdruck.Gleit.Schieben

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Round an unsigned magnitude after a binary right shift. The full remainder
    is kept until the shared nearest-even decision; inputs must be pure. -/
def floatRoundShiftL (d : Nat) (a k : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  let q := fun d => floatShiftQuotL d a k
  let back := fun d => wordL 11 d (q d) (k (d + 1))
  let rem := fun d => wordL 4 d (a d) (back (d + 1))
  let den := fun d => wordL 11 d (some ([ci 1 d 1 0], d + 1)) (k (d + 1))
  floatRoundL d q rem den

theorem floatShiftRemainderWord_model (a : Runner.W) (k : Nat) :
    a - ((a >>> k) <<< k) = BitVec.ofNat 64 (a.toNat % 2^k) := by
  have back := floatShiftBackWord_toNat a k
  have hle : ((a >>> k) <<< k) ≤ a := by
    rw [BitVec.le_def, back]
    exact Nat.div_mul_le_self _ _
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le hle, back, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) a.isLt)]
  exact Nat.mod_eq_sub_div_mul.symm

/-- Every unsigned input is allowed. The count bound makes the denominator a
    positive signed word, as required by floatRoundL's proved comparison. -/
theorem floatRoundShiftL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a k : Nat → Option (List II × Nat)} {av : Runner.W} {s : Nat}
    (ha : WordCode (L := L) ρ W a av)
    (hk : WordCode (L := L) ρ W k (BitVec.ofNat 64 s)) (hs : s < 63) :
    WordCode (L := L) ρ W (fun d => floatRoundShiftL d a k)
      (BitVec.ofNat 64 (Gleitkomma.rundeInt (av.toNat / 2^s) (av.toNat % 2^s) (2^s))) := by
  have hkn : (BitVec.ofNat 64 s).toNat = s := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hm : s % 64 = s := Nat.mod_eq_of_lt (by omega)
  have hqv : av >>> s = BitVec.ofNat 64 (av.toNat / 2^s) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) av.isLt)]
  have hdv : (BitVec.ofInt 64 1) <<< s = BitVec.ofNat 64 (2^s) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have q : WordCode (L := L) ρ W _ _ := floatShiftQuotL_ok ha hk
  have back : WordCode (L := L) ρ W _ _ := WordCode.bin q hk
    (g := fun a b => some (a <<< (b.toNat % 64))) rfl rfl (by decide : 11 < 256)
  have rem : WordCode (L := L) ρ W _ _ := WordCode.bin ha back
    (g := fun a b => some (a - b)) rfl rfl (by decide : 4 < 256)
  have den : WordCode (L := L) ρ W _ _ := WordCode.bin
    (WordCode.const 1 (by decide)) hk (g := fun a b => some (a <<< (b.toNat % 64)))
    rfl rfl (by decide : 11 < 256)
  intro fp K d c top h hK m pc hp
  exact floatRoundL_ok (av.toNat / 2^s) (av.toNat % 2^s) (2^s)
    (Nat.mod_lt _ (Nat.pow_pos (by decide)))
    ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr hs)
    (fun he ht m pc hp => (q he ht m pc hp).mono fun w hw => by
      simpa only [hkn, hqv] using hw)
    (fun he ht m pc hp => (rem he ht m pc hp).mono fun w hw => by
      simpa only [hkn, hm, floatShiftRemainderWord_model] using hw)
    (fun he ht m pc hp => (den he ht m pc hp).mono fun w hw => by
      simpa only [hkn, hm, hdv] using hw)
    h hK hp

/-- The normal-path scaling of G, when the exponent requires a right shift. -/
theorem floatNormQ_shift (p : Nat) (E : Int) (n : Nat) (he : (p : Int) - 1 ≤ E) :
    Gleitkomma.normQ p E n 1 =
      Gleitkomma.rundeInt (n / 2^(E - ((p : Int) - 1)).toNat)
        (n % 2^(E - ((p : Int) - 1)).toNat) (2^(E - ((p : Int) - 1)).toNat) := by
  by_cases hz : E = (p : Int) - 1
  · subst E
    simp [Gleitkomma.normQ, Gleitkomma.normQD]
  · have hn : ¬0 ≤ (p : Int) - 1 - E := by omega
    simp only [Gleitkomma.normQ, Gleitkomma.normQD, hn, ↓reduceIte, Nat.one_mul]

/-- Integer magnitudes requiring left scaling have no discarded bits. -/
theorem floatNormQ_left (p : Nat) (E : Int) (n : Nat)
    (he : E ≤ (p : Int) - 1) :
    Gleitkomma.normQ p E n 1 = n * 2^((p : Int) - 1 - E).toNat := by
  have hs : 0 ≤ (p : Int) - 1 - E := by omega
  simp [Gleitkomma.normQ, Gleitkomma.normQD, hs, he, Gleitkomma.rundeInt, Nat.mod_one]

/-- Actual left-shift IR agrees with G's integer normalization. -/
theorem floatLeftShiftL_normQ {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a k : Nat → Option (List II × Nat)} {av : Runner.W} {E : Int}
    (ha : WordCode (L := L) ρ W a av)
    (hk : WordCode (L := L) ρ W k (BitVec.ofNat 64 (52 - E).toNat))
    (he : E ≤ 52) (hs : (52 - E).toNat < 64) :
    WordCode (L := L) ρ W (fun d => wordL 11 d (a d) (k (d + 1)))
      (BitVec.ofNat 64 (Gleitkomma.normQ 53 E av.toNat 1)) := by
  have result : WordCode (L := L) ρ W _ _ := WordCode.bin ha hk
    (g := fun a b => some (a <<< (b.toNat % 64))) rfl rfl (by decide : 11 < 256)
  have hv : av <<< ((BitVec.ofNat 64 (52 - E).toNat).toNat % 64) =
      BitVec.ofNat 64 (Gleitkomma.normQ 53 E av.toNat 1) := by
    rw [floatNormQ_left 53 E av.toNat (by simpa using he)]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt (show (52 - E).toNat < 2^64 by omega)]
  intro fp K d c top h hK m pc hp
  exact (result h hK m pc hp).mono fun w hw => hw.trans hv

/-- This component already agrees with G's normal significand computation;
    exponent selection and packing are still separate obligations. -/
theorem floatRoundShiftL_normQ {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a k : Nat → Option (List II × Nat)} {av : Runner.W} {E : Int}
    (ha : WordCode (L := L) ρ W a av)
    (hk : WordCode (L := L) ρ W k (BitVec.ofNat 64 (E - 52).toNat))
    (he : 52 ≤ E) (hs : (E - 52).toNat < 63) :
    WordCode (L := L) ρ W (fun d => floatRoundShiftL d a k)
      (BitVec.ofNat 64 (Gleitkomma.normQ 53 E av.toNat 1)) := by
  intro fp K d c top h hK m pc hp
  rw [floatNormQ_shift 53 E av.toNat (by simpa using he)]
  exact floatRoundShiftL_ok ha hk hs h hK m pc hp

/-- Rounding can carry out of the retained significand; it is not truncated. -/
theorem floatRoundShiftL_ok_zeuge {Γ : Ctx} (ρ : Env D Γ) (W : Runner.Mem → Prop) :
    WordCode (L := L) ρ W (fun d => floatRoundShiftL d
      (fun j => some (konstWL 4 (2^64 - 1) j))
      (fun j => some (konstWL 4 11 j))) (BitVec.ofNat 64 (2^53)) ∧
    (floatRoundShiftL 8 (fun j => some (konstWL 4 (2^64 - 1) j))
      (fun j => some (konstWL 4 11 j))).isSome = true := by
  constructor
  · intro fp K d c top h hK m pc hp
    have result : WordCode (L := L) ρ W _ _ := floatRoundShiftL_ok
      (WordCode.konst (2^64 - 1) (by decide)) (WordCode.konst 11 (by decide)) (by decide)
    have hx : BitVec.ofNat 64
        (Gleitkomma.rundeInt ((BitVec.ofNat 64 (2^64 - 1)).toNat / 2^11)
          ((BitVec.ofNat 64 (2^64 - 1)).toNat % 2^11) (2^11)) =
        BitVec.ofNat 64 (2^53) := by decide +kernel
    rw [hx] at result
    exact result h hK m pc hp
  · decide +kernel

theorem floatRoundShiftL_normQ_zeuge {Γ : Ctx} (ρ : Env D Γ) (W : Runner.Mem → Prop) :
    WordCode (L := L) ρ W (fun d => floatRoundShiftL d
      (fun j => some (konstWL 4 (2^53 + 3) j))
      (fun j => some (konstWL 4 1 j))) (BitVec.ofNat 64 (2^52 + 2)) ∧
    (floatRoundShiftL 8 (fun j => some (konstWL 4 (2^53 + 3) j))
      (fun j => some (konstWL 4 1 j))).isSome = true := by
  constructor
  · intro fp K d c top h hK m pc hp
    have result : WordCode (L := L) ρ W _ _ := floatRoundShiftL_normQ (E := 53)
      (WordCode.konst (2^53 + 3) (by decide)) (WordCode.konst 1 (by decide))
      (by decide) (by decide)
    have hx : BitVec.ofNat 64
        (Gleitkomma.normQ 53 53 (BitVec.ofNat 64 (2^53 + 3)).toNat 1) =
        BitVec.ofNat 64 (2^52 + 2) := by decide +kernel
    rw [hx] at result
    exact result h hK m pc hp
  · decide +kernel

end Gabbro.Stage0.Senke
