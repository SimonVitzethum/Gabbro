/- Binary64 subtraction reuses the total adder after one sign-bit xor.
   The kernel defines sub as add with negation, including NaN propagation. -/
module
public import Stage0.Senke.Gleit.Normal.Inputs
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR Runner.Mem

/-- The model identity is definitional for every triple, including NaNs. -/
theorem floatSub_eq_add_neg (a b : GFloat) :
    sub f64 a b = add f64 a (neg f64 b) := rfl

/-- Flip exactly the sign bit; exponent and payload bits are untouched. -/
def softNegWord (b : Runner.W) : Runner.W := b ^^^ BitVec.ofNat 64 (2 ^ 63)

private theorem xorHighBit (b : Runner.W) :
    b ^^^ BitVec.ofNat 64 (2 ^ 63) = b + BitVec.ofNat 64 (2 ^ 63) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_xor, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 2 ^ 63 < 2 ^ 64)]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow, Nat.testBit_mod_two_pow]
  by_cases low : i < 63
  · rw [Nat.add_comm b.toNat (2 ^ 63), Nat.testBit_two_pow_add_gt low]
    simp [show 63 ≠ i by omega, show i < 64 by omega]
  · by_cases top : i = 63
    · subst i
      rw [Nat.add_comm b.toNat (2 ^ 63), Nat.testBit_two_pow_add_eq]
      simp
    · have high : 64 ≤ i := by omega
      have outside : b.toNat.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le b.isLt
          (Nat.pow_le_pow_right Nat.zero_lt_two high))
      simp [show 63 ≠ i by omega, show ¬i < 64 by omega, outside]

/-- The single xor implements model negation on every well-formed triple. -/
theorem softNegWord_model (b : GFloat) (hb : wf f64 b) :
    softNegWord (BitVec.ofNat 64 (zuBits f64 b)) =
      BitVec.ofNat 64 (zuBits f64 (neg f64 b)) := by
  have mag := floatMag_lt hb
  unfold softNegWord
  rw [xorHighBit]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, float_bits]
  change (((if b.sign then 2 ^ 63 else 0) + floatMag b) % 2 ^ 64 +
    2 ^ 63 % 2 ^ 64) % 2 ^ 64 =
    ((if !b.sign then 2 ^ 63 else 0) + floatMag b) % 2 ^ 64
  cases b.sign <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] <;> omega

/-- Decoding the flipped input agrees with negation, with no finite premise. -/
theorem softNeg_model (b : UInt64) :
    u64ToG (UInt64.ofNat (softNegWord b.toBitVec).toNat) = neg f64 (u64ToG b) := by
  have model := softNegWord_model (u64ToG b) (ausBits_f64_wf _)
  have decoded := routineWord_decode b.toBitVec
  simp only [UInt64.toNat_toBitVec] at decoded
  change BitVec.ofNat 64 (zuBits f64 (u64ToG b)) = b.toBitVec at decoded
  rw [decoded] at model
  have bits := congrArg (fun w : Runner.W => ausBits f64 w.toNat) model
  rw [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (zuBits_f64_lt _ (neg_wf f64 _ (ausBits_f64_wf _))),
    ausBits_zuBits f64 f64_dicht _ (neg_wf f64 _ (ausBits_f64_wf _))] at bits
  change ausBits f64 (UInt64.ofNat (softNegWord b.toBitVec).toNat).toNat = _
  rw [UInt64.toNat_ofNat_of_lt' (show (softNegWord b.toBitVec).toNat < UInt64.size from
    (softNegWord b.toBitVec).isLt)]
  exact bits

/-- Word-level subtraction is sign xor followed by the composed adder. -/
def softSub (a b : UInt64) : UInt64 :=
  softAddComposed a (UInt64.ofNat (softNegWord b.toBitVec).toNat)

/-- All inputs, including NaN payload/sign and signed zeros, match the model. -/
theorem softSub_model (a b : UInt64) :
    u64ToG (softSub a b) = sub f64 (u64ToG a) (u64ToG b) := by
  rw [softSub, softAddComposed_model, softNeg_model, floatSub_eq_add_neg]

/-- The actual integer routine implements the same composition on all words. -/
theorem softSubRoutine_ok (a b : UInt64) :
    softAddRoutineWord a.toBitVec (softNegWord b.toBitVec) = (softSub a b).toBitVec := by
  have input : (UInt64.ofNat (softNegWord b.toBitVec).toNat).toBitVec =
      softNegWord b.toBitVec := by
    apply BitVec.eq_of_toNat_eq
    rw [UInt64.toNat_toBitVec, UInt64.toNat_ofNat_of_lt'
      (show (softNegWord b.toBitVec).toNat < UInt64.size from (softNegWord b.toBitVec).isLt)]
  simpa only [softSub, input] using
    softAddRoutine_ok a (UInt64.ofNat (softNegWord b.toBitVec).toNat)

/-- Adapt only the right producer; its value is still evaluated exactly once
    before the adder retains both inputs. The sign mask uses integer constants. -/
def softAddOperandL (subtract : Bool) (d : Nat)
    (right : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  if subtract then wordL 10 d (right d) (some (konstWL 4 (2 ^ 63) (d + 1)))
  else right d

variable [Kern] {D : Deklaration} {L : Lay D}

/-- The adapter preserves the reserved prefix and transports well-formedness
    from the actual child execution, without assuming it before that run. -/
theorem softAddOperandL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {right : Nat → Option (List II × Nat)} {reserved : Nat} {fp : Runner.W} {K : Nat}
    (subtract : Bool) (b : GFloat)
    (hr : ∀ j c t, right j = some (c, t) → t ≤ K → ∀ m pc,
      Pre L m pc fp K j c ρ W reserved → Ok m pc fp K j c
        (fun w => wf f64 b ∧ w = BitVec.ofNat 64 (zuBits f64 b))) :
    ∀ j c t, softAddOperandL subtract j right = some (c, t) → t ≤ K → ∀ m pc,
      Pre L m pc fp K j c ρ W reserved → Ok m pc fp K j c
        (fun w => wf f64 (floatAddOperand subtract f64 b) ∧
          w = BitVec.ofNat 64 (zuBits f64 (floatAddOperand subtract f64 b))) := by
  cases subtract with
  | false => simpa only [softAddOperandL, floatAddOperand, Bool.false_eq_true, ↓reduceIte] using hr
  | true =>
    intro j c t hc ht m pc pre
    simp only [softAddOperandL, ↓reduceIte] at hc
    refine wordL_ok hc ht (fun ca ta ha hta => hr j ca ta ha hta)
      (Pb := fun w => w = BitVec.ofNat 64 (2 ^ 63)) ?_ ?_ rfl (by decide : 10 < 256) pre
    · intro cb tb hb htb m pc hp
      exact WordCode.konst (L := L) (reserved := reserved) (ρ := ρ) (W := W)
        (2 ^ 63) (by decide) hb htb m pc hp
    · intro wa wb ha hb
      refine ⟨wa ^^^ wb, rfl, neg_wf f64 b ha.1, ?_⟩
      rw [ha.2, hb]
      exact softNegWord_model b ha.1

/-- Cancellation has the positive-zero encoding; the four zero combinations,
    subnormal cancellation, infinity conflict and both NaN priorities agree. -/
theorem softSub_model_zeuge :
    softSub 4607182418800017408 4607182418800017408 = 0 ∧
    softSub 0 0 = 0 ∧
    softSub 0 9223372036854775808 = 0 ∧
    softSub 9223372036854775808 0 = 9223372036854775808 ∧
    softSub 9223372036854775808 9223372036854775808 = 0 ∧
    softSub 1 1 = 0 ∧
    softSub 9218868437227405312 9218868437227405312 = 9218868437227405313 ∧
    softSub 18442240474082181127 9218868437227405321 = 18442240474082181127 ∧
    softSub 0 18442240474082181129 = 9218868437227405321 := by
  decide +kernel

/-- A finite cancellation instantiates the actual routine composition. -/
theorem softSubRoutine_ok_zeuge :
    softAddRoutineWord (4607182418800017408 : UInt64).toBitVec
      (softNegWord (4607182418800017408 : UInt64).toBitVec) = 0 := by
  rw [softSubRoutine_ok]
  decide +kernel

#print axioms floatSub_eq_add_neg
#print axioms softNegWord_model
#print axioms softNeg_model
#print axioms softSub_model
#print axioms softSubRoutine_ok
#print axioms softAddOperandL_ok
#print axioms softSub_model_zeuge
#print axioms softSubRoutine_ok_zeuge
end Gabbro.Stage0.Senke
