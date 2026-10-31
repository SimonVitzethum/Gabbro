/- Saturating signed alignment with an exact Euclidean quotient and tail. -/
import Stage0.Senke.Ausdruck.Arithmetik.Ausrichtung
import Stage0.Senke.Ausdruck.Gleit.Skalieren

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Preserve the discarded tail independently of the quotient's low bit. -/
def floatShiftTailL (d : Nat) (a k : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  let q := fun j => floatShiftQuotL j a k
  let back := fun j => wordL 11 j (q j) (k (j + 1))
  let rem := fun j => wordL 4 j (a j) (back (j + 1))
  wordL 4 d (some ([ci 1 d 1 0], d + 1)) (wordK 14 (d + 1) (rem (d + 1)) 0)

/-- Unlike a jammed quotient's low bit, this Boolean states exactly whether
    division discarded anything, even for odd quotients and counts above 63. -/
theorem floatShiftTailL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a k : Nat → Option (List II × Nat)} {av kv : Runner.W}
    (ha : WordCode (L := L) ρ W a av) (hk : WordCode (L := L) ρ W k kv) :
    WordCode (L := L) ρ W (fun d => floatShiftTailL d a k)
      (BitVec.ofNat 64 (if av.toNat % 2^kv.toNat = 0 then 0 else 1)) := by
  have q : WordCode (L := L) ρ W _ _ := floatShiftQuotL_ok ha hk
  have back : WordCode (L := L) ρ W _ _ := WordCode.bin q hk
    (g := fun a b => some (a <<< (b.toNat % 64))) rfl rfl (by decide : 11 < 256)
  have rem : WordCode (L := L) ρ W _ _ := WordCode.bin ha back
    (g := fun a b => some (a - b)) rfl rfl (by decide : 4 < 256)
  have zero : WordCode (L := L) ρ W _ _ := WordCode.bin rem
    (WordCode.const 0 (by decide)) (g := fun a b => some (Runner.IR.bool (a == b)))
    rfl rfl (by decide : 14 < 256)
  have result : WordCode (L := L) ρ W _ _ := WordCode.bin
    (WordCode.const 1 (by decide)) zero (g := fun a b => some (a - b))
    rfl rfl (by decide : 4 < 256)
  intro fp K d c top hc hK m pc hp
  have res := result (fp := fp) (K := K) (d := d) (c := c) (top := top)
    (by simpa [floatShiftTailL, wordK, Nat.add_assoc, Int.add_assoc] using hc) hK m pc
    (by simpa [floatShiftTailL, wordK, Nat.add_assoc, Int.add_assoc] using hp)
  apply res.mono
  intro w hw
  rw [floatShiftBackWord_model, floatShiftRemainderWord_model] at hw
  have hrange : av.toNat % 2^kv.toNat < 2^64 :=
    Nat.lt_of_le_of_lt (Nat.mod_le _ _) av.isLt
  have hz : (BitVec.ofNat 64 (av.toNat % 2^kv.toNat) == BitVec.ofInt 64 0) =
      decide (av.toNat % 2^kv.toNat = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hrange, decide_eq_true_eq]
    rfl
  rw [hz] at hw
  by_cases h : av.toNat % 2^kv.toNat = 0 <;> simpa [h, Runner.IR.bool] using hw

/-- Compose the saturating quotient, exact tail and Euclidean borrow. -/
def floatNegativeShiftL (d : Nat) (a k : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  floatNegativeQuotL d (fun j => floatShiftQuotL j a k)
    (fun j => floatShiftTailL j a k)

/-- Actual emitted signed alignment covers every word-sized count, with no
    bound at 63 and no truncation of a negative tail toward zero. -/
theorem floatNegativeShiftL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a k : Nat → Option (List II × Nat)} {av kv : Runner.W}
    (ha : WordCode (L := L) ρ W a av) (hk : WordCode (L := L) ρ W k kv) :
    WordCode (L := L) ρ W (fun d => floatNegativeShiftL d a k)
      (BitVec.ofInt 64 ((-(av.toNat : Int)) / (2^kv.toNat : Nat))) := by
  have q : WordCode (L := L) ρ W _ _ := floatShiftQuotL_ok ha hk
  have hqv : av >>> kv.toNat = BitVec.ofNat 64 (av.toNat / 2^kv.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) av.isLt)]
  apply floatNegativeQuotL_ok av.toNat (2^kv.toNat) (Nat.pow_pos (by decide))
  · intro fp K d c top hc hK m pc hp
    exact (q hc hK m pc hp).mono fun w hw => hw.trans hqv
  · exact floatShiftTailL_ok ha hk

omit [Kern] in
/-- A finite coefficient's negative aligned quotient fits the signed word.
    The discarded tail's borrow cannot make its magnitude exceed the original
    magnitude, even at the minimum signed-word boundary. -/
theorem floatNegativeAlign_range (n den : Nat) (hd : 0 < den) (hn : n ≤ 2^63) :
    -(2^63) ≤ (-(n : Int)) / (den : Int) ∧
      (-(n : Int)) / (den : Int) < 2^63 := by
  rw [floatNegativeAlign_div n den hd]
  have hq := Nat.div_le_self n den
  have hq0 : (0 : Int) ≤ (n / den : Nat) := Int.natCast_nonneg _
  by_cases hz : n % den = 0
  · simp only [hz, ↓reduceIte]
    omega
  · have hn0 : 0 < n := by
      by_cases h : n = 0
      · simp [h] at hz
      · omega
    have hd1 : 1 < den := by
      by_cases h : den = 1
      · simp [h, Nat.mod_one] at hz
      · omega
    have hlt := Nat.div_lt_self hn0 hd1
    simp only [hz, ↓reduceIte]
    omega

omit [Kern] in
/-- Recover the exact signed quotient from its emitted word representation;
    no exponent-distance restriction or positive-only approximation is used. -/
theorem floatNegativeShift_toInt (a k : Runner.W) (ha : a.toNat ≤ 2^63) :
    (BitVec.ofInt 64 ((-(a.toNat : Int)) / (2^k.toNat : Nat))).toInt =
      (-(a.toNat : Int)) / (2^k.toNat : Nat) := by
  have h := floatNegativeAlign_range a.toNat (2^k.toNat)
    (Nat.pow_pos (by decide)) ha
  exact toInt_ofInt_in h.1 h.2

omit [Kern] in
/-- The minimum signed coefficient, cancellation-scale shift, tiny negative
    tail and zero satisfy the range bridge jointly. -/
theorem floatNegativeShift_toInt_zeuge :
    (BitVec.ofInt 64 (-(2^63))).toInt = -(2^63) ∧
    (BitVec.ofInt 64 ((-(13 : Int)) / (2^1074 : Nat))).toInt = -1 ∧
    (BitVec.ofInt 64 ((0 : Int) / (2^1074 : Nat))).toInt = 0 := by
  decide +kernel

#print axioms floatNegativeAlign_range
#print axioms floatNegativeShift_toInt
#print axioms floatNegativeShift_toInt_zeuge
#print axioms floatShiftTailL_ok
#print axioms floatNegativeShiftL_ok
end Gabbro.Stage0.Senke
