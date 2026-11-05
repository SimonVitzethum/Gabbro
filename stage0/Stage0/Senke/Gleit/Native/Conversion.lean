/- Native conversion primitives and their actual word-code composition. -/
module
public import Stage0.Senke.Gleit.Native.Values
public import NativeFloat.Hardware
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- Both integer conversions consume the child once and retain the IR's second
    physical slot read. Unsigned conversion uses the runner's portable sequence. -/
def nativeIntegerFloatL (signed : Bool) (d : Nat) (child : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  nativeFPWordL (if signed then .fromInt64 .f64 else .fromUInt64 .f64)
    d (child d) (some ([ci 1 (d + 1) 0 0], d + 2))

theorem nativeIntegerFloatL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {child : Nat → Option (List II × Nat)} (signed : Bool) (word : Runner.W)
    (source : WordCode (L := L) (reserved := reserved) ρ W child word) :
    NativeFloatCode (L := L) (reserved := reserved) ρ W
      (fun d => nativeIntegerFloatL signed d child)
      (if signed then (Int64.ofBitVec word).hwToFloat else (UInt64.ofBitVec word).hwToFloat) := by
  intro fp K d c top emitted fits m pc pre
  refine nativeFPWordL_ok (L := L) (reserved := reserved)
    (Pa := fun w => w = word) (Pb := fun w => w = (0 : Runner.W))
    (if signed then .fromInt64 .f64 else .fromUInt64 .f64)
    (by cases signed; exact op_fp_fromUInt64 .f64; exact op_fp rfl) emitted fits
    (fun _ _ hc ht => source hc ht) ?_ ?_ pre
  · intro cb tb hc ht m pc hp
    cases hc
    exact const_ok hp (by decide) (by omega)
  · intro wa wb ha hb
    subst wa
    refine ⟨_, ?_, nativeFloat_read_word _⟩
    cases signed <;> change Runner.readFloat _ = _
    all_goals exact nativeFloat_read_word _

/-- Source bounds are used only to identify the actual signed or unsigned cast.
    They are derived from the existing canonical integer value and type gate. -/
theorem nativeIntegerFloatL_source_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {child : Nat → Option (List II × Nat)} (signed : Bool) (z : Int)
    (bounds : if signed then -(2 ^ 63) ≤ z ∧ z < 2 ^ 63 else 0 ≤ z ∧ z < 2 ^ 64)
    (source : WordCode (L := L) (reserved := reserved) ρ W child (BitVec.ofInt 64 z)) :
    NativeFloatCode (L := L) (reserved := reserved) ρ W
      (fun d => nativeIntegerFloatL signed d child) (gleitAusInt z) := by
  have value : (if signed then (Int64.ofBitVec (BitVec.ofInt 64 z)).hwToFloat
      else (UInt64.ofBitVec (BitVec.ofInt 64 z)).hwToFloat) = gleitAusInt z := by
    cases signed
    · change 0 ≤ z ∧ z < 2 ^ 64 at bounds
      have word : UInt64.ofBitVec (BitVec.ofInt 64 z) = UInt64.ofNat z.toNat := by
        apply UInt64.eq_of_toBitVec_eq
        change BitVec.ofInt 64 z = BitVec.ofNat 64 z.toNat
        rw [← BitVec.ofInt_natCast, Int.toNat_of_nonneg bounds.1]
      change (UInt64.ofBitVec (BitVec.ofInt 64 z)).hwToFloat = Float.hwOfInt z
      rw [word]
      exact (RootNativeFloat.ofInt_unsigned64 z bounds.1 bounds.2).symm
    · change -(2 ^ 63) ≤ z ∧ z < 2 ^ 63 at bounds
      exact (RootNativeFloat.ofInt_signed64_bits z bounds.1 bounds.2).symm
  intro fp K d c top emitted fits m pc pre
  have run := nativeIntegerFloatL_ok signed (BitVec.ofInt 64 z) source
    emitted fits m pc pre
  exact run.mono (fun word decoded => decoded.trans value)

/-- Scaling uses the same physical multiplier and native value relation as
    arithmetic. Neither child has to promise a canonical NaN bit pattern. -/
theorem nativeFloatMulL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a b : Nat → Option (List II × Nat)} {x y : GFloat}
    (left : NativeFloatCode (L := L) (reserved := reserved) ρ W a x)
    (right : NativeFloatCode (L := L) (reserved := reserved) ρ W b y) :
    NativeFloatCode (L := L) (reserved := reserved) ρ W
      (fun d => nativeFPWordL (.mul .f64) d (a d) (b (d + 1))) (Float.hwMul x y) := by
  intro fp K d c top emitted fits m pc pre
  refine nativeFPWordL_ok (.mul .f64) (op_fp rfl) emitted fits
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
  have offset : WordCode (L := L) (reserved := reserved) ρ W
      (fun d => wordK 4 d (index d) 55)
      (BitVec.ofNat 64 i - BitVec.ofInt 64 55) :=
    WordCode.bin (L := L) (reserved := reserved) hi
      (WordCode.const (L := L) (reserved := reserved) (ρ := ρ) (W := W) 55 (by decide))
      (g := fun a b => some (a - b)) rfl rfl (by decide : 4 < 256)
  have exponent : WordCode (L := L) (reserved := reserved) ρ W
      (fun d => wordK 11 d (wordK 4 d (index d) 55) 52)
      ((BitVec.ofNat 64 i - BitVec.ofInt 64 55) <<< (52 : Nat)) :=
    WordCode.bin (L := L) (reserved := reserved) offset
      (WordCode.const (L := L) (reserved := reserved) (ρ := ρ) (W := W) 52 (by decide))
      (g := fun a b => some (a <<< (b.toNat % 64))) rfl rfl (by decide : 11 < 256)
  have polarity : WordCode (L := L) (reserved := reserved) ρ W
      (fun d => wordK 11 d (sign d) 63) (Runner.IR.bool s <<< (63 : Nat)) :=
    WordCode.bin (L := L) (reserved := reserved) hs
      (WordCode.const (L := L) (reserved := reserved) (ρ := ρ) (W := W) 63 (by decide))
      (g := fun a b => some (a <<< (b.toNat % 64))) rfl rfl (by decide : 11 < 256)
  have combined : WordCode (L := L) (reserved := reserved) ρ W
      (fun d => nativeFloatScaleL d sign index)
      (((BitVec.ofNat 64 i - BitVec.ofInt 64 55) <<< (52 : Nat)) |||
        (Runner.IR.bool s <<< (63 : Nat))) :=
    WordCode.bin (L := L) (reserved := reserved) exponent polarity
      (g := fun a b => some (a ||| b)) rfl rfl (by decide : 9 < 256)
  intro fp K d c top emitted fits m pc pre
  have run := combined (fp := fp) (K := K) (d := d) (c := c) (top := top)
    emitted fits m pc pre
  simpa only [nativeFloatScaleWord, BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat] using run

/-- The bounded scale fields are exactly the canonical native power operand. -/
theorem nativeFloatScaleWord_eq (sign : Bool) (index : Nat)
    (lower : 55 ≤ index) (upper : index ≤ 2047) :
    nativeFloatScaleWord sign index = BitVec.ofNat 64
      ((if sign then 2 ^ 63 else 0) + (index - 55) * 2 ^ 52) := by
  have exponent : ((BitVec.ofNat 64 index - 55) <<< 52) =
      BitVec.ofNat 64 ((index - 55) * 2 ^ 52) := by
    change ((BitVec.ofNat 64 index - BitVec.ofNat 64 55) <<< (52 : Nat)) = _
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) index 55 (by decide) lower,
      BitVec.shiftLeft_eq_mul_twoPow]
    exact (BitVec.ofNat_mul _ _).symm
  have room : (index - 55) * 2 ^ 52 < 2 ^ 63 := by omega
  have combined := Nat.two_pow_add_eq_or_of_lt room 1
  simp only [Nat.mul_one] at combined
  unfold nativeFloatScaleWord
  rw [exponent]
  cases sign
  · simp only [Runner.IR.bool, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    change BitVec.ofNat 64 ((index - 55) * 2 ^ 52) ||| (0#64 <<< (63 : Nat)) =
      BitVec.ofNat 64 ((index - 55) * 2 ^ 52)
    rw [BitVec.zero_shiftLeft, BitVec.or_zero]
  · change BitVec.ofNat 64 ((index - 55) * 2 ^ 52) ||| BitVec.ofNat 64 (2 ^ 63) =
      BitVec.ofNat 64 (2 ^ 63 + (index - 55) * 2 ^ 52)
    rw [← BitVec.ofNat_or, Nat.or_comm, ← combined]

end Gabbro.Stage0.Senke
