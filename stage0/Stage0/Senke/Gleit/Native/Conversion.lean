/- Native conversion primitives and their actual word-code composition. -/
module
public import Stage0.Senke.Gleit.Native.Values
public import Grammatik.Kern.Syntax.Typen.NativeIntConversion
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- Unary FP instructions still perform the IR's second physical slot read. -/
def nativeSignedFloatL (d : Nat) (child : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  nativeFPWordL (.fromInt64 .f64) d (child d) (some ([ci 1 (d + 1) 0 0], d + 2))

theorem nativeSignedFloatL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {child : Nat → Option (List II × Nat)} (z : Int)
    (source : WordCode (L := L) (reserved := reserved) ρ W child (BitVec.ofInt 64 z)) :
    NativeFloatCode (L := L) (reserved := reserved) ρ W
      (fun d => nativeSignedFloatL d child) (Int64.ofBitVec (BitVec.ofInt 64 z)).toFloat := by
  intro fp K d c top emitted fits m pc pre
  refine nativeFPWordL_ok (.fromInt64 .f64) rfl emitted fits
    (fun _ _ hc ht => source hc ht) ?_ ?_ pre
  · intro cb tb hc ht m pc hp
    cases hc
    exact const_ok hp (by decide) (by omega)
  · intro wa wb ha hb
    subst wa
    refine ⟨_, ?_, nativeFloat_read_word _⟩
    change Runner.readFloat _ = _
    exact nativeFloat_read_word _

/-- Signed source bounds are used only to identify the actual native cast.
    They are derived from the existing canonical integer value and type gate. -/
theorem nativeSignedIntegerL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {child : Nat → Option (List II × Nat)} (z : Int)
    (lower : -(2 ^ 63) ≤ z) (upper : z < 2 ^ 63)
    (source : WordCode (L := L) (reserved := reserved) ρ W child (BitVec.ofInt 64 z)) :
    NativeFloatCode (L := L) (reserved := reserved) ρ W
      (fun d => nativeSignedFloatL d child) (gleitAusInt z) := by
  change NativeFloatCode _ _ _ (Float.ofInt z) _
  rw [NativeFloat.ofInt_signed64_bits z lower upper]
  exact nativeSignedFloatL_ok z source

/-- Scaling uses the same physical multiplier and native value relation as
    arithmetic. Neither child has to promise a canonical NaN bit pattern. -/
theorem nativeFloatMulL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a b : Nat → Option (List II × Nat)} {x y : GFloat}
    (left : NativeFloatCode (L := L) (reserved := reserved) ρ W a x)
    (right : NativeFloatCode (L := L) (reserved := reserved) ρ W b y) :
    NativeFloatCode (L := L) (reserved := reserved) ρ W
      (fun d => nativeFPWordL (.mul .f64) d (a d) (b (d + 1))) (Float.mul x y) := by
  intro fp K d c top emitted fits m pc pre
  refine nativeFPWordL_ok (.mul .f64) rfl emitted fits
    (fun _ _ hc ht => left hc ht) (fun _ _ hc ht => right hc ht) ?_ pre
  intro wa wb ha hb
  refine ⟨_, ?_, nativeFloat_read_word _⟩
  simp only [Runner.NativeFPEval, Runner.nativeFP, Runner.NativeFPValue.Matches, ha, hb]
  exact nativeFloat_read_word _

/-- The source integer normalizer supplies a bounded exponent index and sign.
    These instructions construct the exact power-of-two operand's bits only. -/
def nativeFloatScaleL (d : Nat) (sign index : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wordL 9 d (wordK 11 d (wordK 4 d (index d) 55) 52)
    (wordK 11 (d + 1) (sign (d + 1)) 63)

def nativeFloatScaleWord (sign : Bool) (index : Nat) : Runner.W :=
  ((BitVec.ofNat 64 index - 55) <<< 52) ||| (Runner.IR.bool sign <<< 63)

theorem nativeFloatScaleL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {sign index : Nat → Option (List II × Nat)} {s : Bool} {i : Nat}
    (hs : WordCode (L := L) (reserved := reserved) ρ W sign (Runner.IR.bool s))
    (hi : WordCode (L := L) (reserved := reserved) ρ W index (BitVec.ofNat 64 i)) :
    WordCode (L := L) (reserved := reserved) ρ W
      (fun d => nativeFloatScaleL d sign index) (nativeFloatScaleWord s i) := by
  have offset := WordCode.bin hi (WordCode.const 55 (by decide))
    (g := fun a b => some (a - b)) rfl rfl (by decide : 4 < 256)
  have exponent := WordCode.bin offset (WordCode.const 52 (by decide))
    (g := fun a b => some (a <<< (b.toNat % 64))) rfl rfl (by decide : 11 < 256)
  have polarity := WordCode.bin hs (WordCode.const 63 (by decide))
    (g := fun a b => some (a <<< (b.toNat % 64))) rfl rfl (by decide : 11 < 256)
  exact WordCode.bin exponent polarity (g := fun a b => some (a ||| b))
    rfl rfl (by decide : 9 < 256)

/-- The bounded scale fields are exactly the canonical native power operand. -/
theorem nativeFloatScaleWord_eq (sign : Bool) (index : Nat)
    (lower : 55 ≤ index) (upper : index ≤ 2047) :
    nativeFloatScaleWord sign index = BitVec.ofNat 64
      ((if sign then 2 ^ 63 else 0) + (index - 55) * 2 ^ 52) := by
  have exponent : ((BitVec.ofNat 64 index - 55) <<< 52) =
      BitVec.ofNat 64 ((index - 55) * 2 ^ 52) := by
    rw [BitVec.ofNat_sub_ofNat_of_le index 55 (by decide) lower,
      BitVec.shiftLeft_eq_mul_twoPow]
    exact (BitVec.ofNat_mul _ _).symm
  have room : (index - 55) * 2 ^ 52 < 2 ^ 63 := by omega
  have combined := Nat.two_pow_add_eq_or_of_lt room 1
  simp only [Nat.mul_one] at combined
  unfold nativeFloatScaleWord
  rw [exponent]
  cases sign
  · simp only [Runner.IR.bool, Bool.false_eq_true, ↓reduceIte,
      BitVec.zero_shiftLeft, BitVec.or_zero, Nat.zero_add]
  · change BitVec.ofNat 64 ((index - 55) * 2 ^ 52) ||| BitVec.ofNat 64 (2 ^ 63) = _
    rw [← BitVec.ofNat_or, Nat.or_comm, ← combined]

end Gabbro.Stage0.Senke
