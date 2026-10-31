/- Signed magnitude extraction without signed overflow, including -2^63. -/
import Stage0.Senke.Ausdruck.Gleit.Komposition
import Stage0.Senke.Ausdruck.Eng

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- The magnitude is an unsigned word; the minimum signed input needs its high bit. -/
def floatMagnitudeWord (x : Runner.W) : Runner.W :=
  x * (1 - 2 * Runner.IR.bool (x.slt 0))

/-- Extract a magnitude using only signed comparison and modular integer operations.
    The operand is pure and is reread to compute its sign. -/
def floatMagnitudeL (d : Nat) (e : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  let sign := fun d => wordK 13 d (e d) 0
  let twice := fun d => wordL 5 d (some ([ci 1 d 2 0], d + 1)) (sign (d + 1))
  let factor := fun d => wordL 4 d (some ([ci 1 d 1 0], d + 1)) (twice (d + 1))
  wordL 5 d (e d) (factor (d + 1))

/-- The emitted signed comparison consumes concrete reads, with no producer
    assumption for the retained input. This is the sign instruction of magnitude. -/
theorem floatMagnitude_sign_instruction {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K d reserved : Nat} {v : Runner.W}
    (hp : Pre L m pc fp K d [ci 13 d d (d + 1)] ρ W reserved)
    (hk : d + 1 < K)
    (hv : m.rd64 (slot fp (BitVec.ofNat 64 d)) = some v)
    (hz : m.rd64 (slot fp (BitVec.ofNat 64 (d + 1))) = some 0) :
    Ok m pc fp K d [ci 13 d d (d + 1)]
      (· = Runner.IR.bool (v.slt 0)) := by
  exact eng_bin_ok hp (by omega) (by omega) hk hv hz
    (g := fun x y => some (Runner.IR.bool (x.slt y))) rfl (by decide) rfl

/-- The signed minimum is handled with modular negation, not a signed absolute value. -/
theorem floatMagnitudeWord_model (z : Int) (hz : -2^63 ≤ z ∧ z < 2^63) :
    floatMagnitudeWord (BitVec.ofInt 64 z) = BitVec.ofNat 64 z.natAbs := by
  unfold floatMagnitudeWord
  rw [show (0 : Runner.W) = BitVec.ofInt 64 0 from rfl, slt_in hz (by decide)]
  by_cases hn : z < 0
  · simp only [hn, decide_true, Runner.IR.bool, ↓reduceIte]
    have hf : (1 : Runner.W) - 2 * 1 = BitVec.ofInt 64 (-1) := by decide
    rw [hf, ← BitVec.ofInt_mul]
    rw [← BitVec.ofInt_natCast]
    congr 1
    rw [Int.ofNat_natAbs_of_nonpos (by omega)]
    omega
  · simp only [hn, decide_false, Runner.IR.bool, Bool.false_eq_true, ↓reduceIte,
      BitVec.mul_zero, BitVec.sub_zero, BitVec.mul_one]
    have hf : (1 : Runner.W) - 2 * 0 = 1 := by decide
    rw [hf]
    change BitVec.ofInt 64 z * (1#64) = _
    rw [BitVec.mul_one]
    rw [← BitVec.ofInt_natCast, Int.natAbs_of_nonneg (by omega)]

/-- Compositional IR simulation; the only code premise is the input expression. -/
theorem floatMagnitudeL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {e : Nat → Option (List II × Nat)} {x : Runner.W}
    (he : WordCode (L := L) ρ W e x) :
    WordCode (L := L) ρ W (fun d => floatMagnitudeL d e) (floatMagnitudeWord x) := by
  have sign : WordCode (L := L) ρ W _ _ := WordCode.bin he
    (WordCode.const 0 (by decide))
    (g := fun a b => some (Runner.IR.bool (a.slt b))) rfl rfl (by decide : 13 < 256)
  have twice : WordCode (L := L) ρ W _ _ := WordCode.bin
    (WordCode.const 2 (by decide)) sign (g := fun a b => some (a * b))
    rfl rfl (by decide : 5 < 256)
  have factor : WordCode (L := L) ρ W _ _ := WordCode.bin
    (WordCode.const 1 (by decide)) twice (g := fun a b => some (a - b))
    rfl rfl (by decide : 4 < 256)
  have result : WordCode (L := L) ρ W _ _ := WordCode.bin he factor
    (g := fun a b => some (a * b)) rfl rfl (by decide : 5 < 256)
  intro fp K d c top h hK m pc hp
  simpa only [BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat, floatMagnitudeWord] using
    result (fp := fp) (K := K) (d := d) (c := c) (top := top) h hK m pc hp

/-- Includes the word boundary that cannot be represented as a positive signed integer. -/
theorem floatMagnitudeWord_model_zeuge :
    floatMagnitudeWord (BitVec.ofInt 64 (-2^63)) = BitVec.ofNat 64 (2^63) ∧
    floatMagnitudeWord (BitVec.ofInt 64 (-42)) = 42 ∧
    floatMagnitudeWord 0 = 0 ∧ floatMagnitudeWord 42 = 42 := by decide +kernel

/-- An inhabited input-code premise and a concrete successful lowering. -/
theorem floatMagnitudeL_ok_zeuge {Γ : Ctx} (ρ : Env D Γ) (W : Runner.Mem → Prop) :
    WordCode (L := L) ρ W
      (fun d => floatMagnitudeL d (fun j => some ([ci 1 j (-42) 0], j + 1))) 42 ∧
    (floatMagnitudeL 8 (fun j => some ([ci 1 j (-42) 0], j + 1))).isSome = true := by
  constructor
  · intro fp K d c top h hK m pc hp
    have result : WordCode (L := L) ρ W _ _ := floatMagnitudeL_ok (L := L) (ρ := ρ) (W := W)
      (WordCode.const (-42) (by decide))
    have hx : floatMagnitudeWord (BitVec.ofInt 64 (-42)) = 42 := by decide
    rw [hx] at result
    exact result h hK m pc hp
  · decide +kernel

end Gabbro.Stage0.Senke
