/- Exact post-cancellation magnitude extraction from a signed quotient and tail. -/
import Stage0.Senke.Ausdruck.Arithmetik.Output
import Mathlib.Tactic.Ring

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem Gleitkomma

/-- The integer part of the magnitude borrows from a negative quotient when
    its Euclidean tail is nonzero. The tail itself must stay exact. -/
def floatSumMagnitude (z r : Int) : Int :=
  if z < 0 then -z - (if r = 0 then 0 else 1) else z

/-- Canonical reconstruction after cancellation, including a quotient of zero.
    A negative result complements its remainder; sticky alone is never used
    as the exact remainder. -/
theorem floatSumMagnitude_reconstruct (z r den : Int)
    (hd : 0 < den) (hr : 0 ≤ r ∧ r < den) :
    ((z * den + r).natAbs : Int) =
      floatSumMagnitude z r * den +
        (if z < 0 then if r = 0 then 0 else den - r else r) := by
  unfold floatSumMagnitude
  by_cases hz : z < 0
  · have hb := Int.mul_le_mul_of_nonneg_right (show z ≤ -1 by omega) (show 0 ≤ den by omega)
    have hn : z * den + r ≤ 0 := by omega
    rw [Int.ofNat_natAbs_of_nonpos hn]
    by_cases h : r = 0 <;> simp [hz, h] <;> ring
  · have hb := Int.mul_nonneg (show 0 ≤ z by omega) (show 0 ≤ den by omega)
    have hn : 0 ≤ z * den + r := by omega
    rw [Int.natAbs_of_nonneg hn]
    simp [hz]

/-- Emitted magnitude normalization consumes the actual signed sum and its
    exact-tail indicator. Both producers can be arbitrary pure fragments. -/
def floatSumMagnitudeL (dst : Nat)
    (sum sticky : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  let sign := fun j => wordK 13 j (sum j) 0
  let borrow := fun j => wordL 5 j (sign j) (sticky (j + 1))
  wordL 4 dst (floatMagnitudeL dst sum) (borrow (dst + 1))

variable [Kern] {D : Deklaration} {L : Lay D}

/-- The connected integer fragment computes the canonical magnitude quotient,
    under the shared word-code frame and footprint discipline. -/
theorem floatSumMagnitudeL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {sum sticky : Nat → Option (List II × Nat)} (z r : Int)
    (hz : -2^63 ≤ z ∧ z < 2^63)
    (hs : WordCode (L := L) ρ W sum (BitVec.ofInt 64 z))
    (ht : WordCode (L := L) ρ W sticky
      (BitVec.ofInt 64 (if r = 0 then 0 else 1))) :
    WordCode (L := L) ρ W (fun dst => floatSumMagnitudeL dst sum sticky)
      (BitVec.ofInt 64 (floatSumMagnitude z r)) := by
  have sign : WordCode (L := L) ρ W
      (fun j => wordK 13 j (sum j) 0) (Runner.IR.bool ((BitVec.ofInt 64 z).slt 0)) :=
    WordCode.bin hs (WordCode.const 0 (by decide))
      (g := fun a b => some (Runner.IR.bool (a.slt b))) rfl rfl (by decide : 13 < 256)
  have borrow : WordCode (L := L) ρ W _ _ := WordCode.bin sign ht
    (g := fun a b => some (a * b)) rfl rfl (by decide : 5 < 256)
  have result : WordCode (L := L) ρ W _ _ := WordCode.bin
    (floatMagnitudeL_ok hs) borrow (g := fun a b => some (a - b))
    rfl rfl (by decide : 4 < 256)
  intro fp K dst code top hc hK m pc hp
  exact (result hc hK m pc hp).mono fun w hw => by
    rw [floatMagnitudeWord_model z hz] at hw
    rw [show (0 : Runner.W) = BitVec.ofInt 64 0 from rfl, slt_in hz (by decide)] at hw
    by_cases hn : z < 0
    · simp only [hn, decide_true, Runner.IR.bool, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.one_mul] at hw
      rw [← BitVec.ofInt_natCast, Int.ofNat_natAbs_of_nonpos (by omega),
        BitVec.sub_eq_add_neg, ← BitVec.ofInt_neg, ← BitVec.ofInt_add] at hw
      simpa [floatSumMagnitude, hn, Int.sub_eq_add_neg] using hw
    · simp only [hn, decide_false, Runner.IR.bool, Bool.false_eq_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.zero_mul, BitVec.sub_zero] at hw
      rw [← BitVec.ofInt_natCast, Int.natAbs_of_nonneg (by omega)] at hw
      simpa [floatSumMagnitude, hn, Int.sub_eq_add_neg] using hw

/-- Actual encoded operands feed coefficient decoding, exact alignment and
    magnitude extraction without an assumed intermediate sum. This finite
    fragment covers exact word-sized alignment, including cancellation. -/
theorem floatCoefficientAlignMagnitudeL_ok {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop}
    {lo hi distance : Nat → Option (List II × Nat)}
    (a b : GFloat) (k : Nat)
    (ha : wf f64 a) (hb : wf f64 b) (hk : k < 64)
    (hr : -(2^63) ≤ floatCoefficient a + floatCoefficient b * (2^k : Nat) ∧
      floatCoefficient a + floatCoefficient b * (2^k : Nat) < 2^63)
    (hlo : WordCode (L := L) ρ W lo (BitVec.ofNat 64 (zuBits f64 a)))
    (hhi : WordCode (L := L) ρ W hi (BitVec.ofNat 64 (zuBits f64 b)))
    (hd : WordCode (L := L) ρ W distance (BitVec.ofNat 64 k)) :
    WordCode (L := L) ρ W
      (fun dst => floatSumMagnitudeL dst
        (fun j => floatAlignSumL j
          (fun n => floatCoefficientL n lo)
          (fun n => floatCoefficientL n hi) distance)
        (fun j => some ([ci 1 j 0 0], j+1)))
      (BitVec.ofInt 64
        (floatSumMagnitude (floatCoefficient a + floatCoefficient b * (2^k : Nat)) 0)) := by
  have sum : WordCode (L := L) ρ W
      (fun j => floatAlignSumL j (fun n => floatCoefficientL n lo)
        (fun n => floatCoefficientL n hi) distance)
      (floatAlignSumWord (floatCoefficientWord (BitVec.ofNat 64 (zuBits f64 a)))
        (floatCoefficientWord (BitVec.ofNat 64 (zuBits f64 b))) (BitVec.ofNat 64 k)) :=
    floatCoefficientAlignSumL_ok hlo hhi hd
  rw [floatCoefficientWord_canonical a ha, floatCoefficientWord_canonical b hb,
    floatAlignSumWord_model _ _ _ hk] at sum
  have zero : WordCode (L := L) ρ W
      (fun j => some ([ci 1 j 0 0], j+1)) (BitVec.ofInt 64 0) := by
    intro fp K dst code top hc hK m pc hp
    exact WordCode.const 0 (by decide) hc hK m pc hp
  intro fp K dst code top hc hK m pc hp
  exact floatSumMagnitudeL_ok _ 0 hr sum zero hc hK m pc hp

/-- Opposite signs cancel to one smallest-subnormal unit through the
    same encoded-operand fragment; all generic premises hold jointly. -/
theorem floatCoefficientAlignMagnitudeL_ok_zeuge {D : Deklaration} (L : Lay D) :
    let a : GFloat := ⟨true, 0, 2^52-1⟩
    let b : GFloat := ⟨false, 1, 0⟩
    let lit := fun n j => some (konstWL 4 n j)
    WordCode (L := L) (Env.nil : Env D []) (fun _ => True)
      (fun dst => floatSumMagnitudeL dst
        (fun j => floatAlignSumL j
          (fun n => floatCoefficientL n (lit (zuBits f64 a)))
          (fun n => floatCoefficientL n (lit (zuBits f64 b))) (lit 0))
        (fun j => some ([ci 1 j 0 0], j+1))) (BitVec.ofInt 64 1) := by
  dsimp only
  intro fp K dst code top hc hK m pc hp
  exact floatCoefficientAlignMagnitudeL_ok (L := L)
    (ρ := (Env.nil : Env D [])) (W := fun _ => True)
    (⟨true, 0, 2^52-1⟩ : GFloat) (⟨false, 1, 0⟩ : GFloat) 0
    (by decide) (by decide) (by decide) (by decide +kernel)
    (WordCode.konst _ (by decide)) (WordCode.konst _ (by decide))
    (WordCode.konst 0 (by decide)) hc hK m pc hp

#print axioms floatCoefficientAlignMagnitudeL_ok_zeuge

#print axioms floatCoefficientAlignMagnitudeL_ok

/-- Alignment, signed addition and magnitude extraction are one computation;
    no hypothesis supplies the sum's value or a magnitude routine's result. -/
theorem floatNegativeSumMagnitudeL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {hi magnitude distance sticky : Nat → Option (List II × Nat)}
    (h : Int) (a k : Runner.W)
    (hh : -(2^61) ≤ h ∧ h ≤ 2^61) (ha : a.toNat ≤ 2^61)
    (hhi : WordCode (L := L) ρ W hi (BitVec.ofInt 64 h))
    (hmag : WordCode (L := L) ρ W magnitude a)
    (hk : WordCode (L := L) ρ W distance k)
    (ht : WordCode (L := L) ρ W sticky (BitVec.ofInt 64
      (if (-(a.toNat : Int)) % (2^k.toNat : Nat) = 0 then 0 else 1))) :
    WordCode (L := L) ρ W
      (fun dst => floatSumMagnitudeL dst
        (fun j => floatNegativeSumL j hi magnitude distance) sticky)
      (BitVec.ofInt 64 (floatSumMagnitude
        (h + (-(a.toNat : Int)) / (2^k.toNat : Nat))
        ((-(a.toNat : Int)) % (2^k.toNat : Nat)))) := by
  have hb := floatNegativeAlign_bounds a.toNat (2^k.toNat)
    (Nat.pow_pos (by decide))
  intro fp K dst code top hc hK m pc hp
  exact floatSumMagnitudeL_ok _ _ (by constructor <;> omega)
    (floatNegativeSumL_ok hhi hmag hk) ht hc hK m pc hp

omit [Kern] in
/-- The magnitude bridge applies directly to the exact numerator of aligned
    subtraction. All remainder bounds follow from Euclidean division. -/
theorem floatNegativeSumMagnitude_reconstruct (h : Int) (a k : Runner.W) :
    let den : Int := (2^k.toNat : Nat)
    let z := h + (-(a.toNat : Int)) / den
    let r := (-(a.toNat : Int)) % den
    ((h * den - (a.toNat : Int)).natAbs : Int) =
      floatSumMagnitude z r * den +
        (if z < 0 then if r = 0 then 0 else den - r else r) := by
  dsimp only
  have hd : (0 : Int) < (2^k.toNat : Nat) := by
    exact_mod_cast Nat.pow_pos (by decide : 0 < 2) (n := k.toNat)
  rw [Int.sub_eq_add_neg, floatSignedAlign_reconstruct h (-(a.toNat : Int)) (2^k.toNat)]
  exact floatSumMagnitude_reconstruct _ _ _ hd
    ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hd⟩

/-- All producer and signed-range premises hold jointly on nonzero negative
    cancellation with an inexact tail. -/
theorem floatNegativeSumMagnitudeL_ok_zeuge {Γ : Ctx}
    (ρ : Env D Γ) (W : Runner.Mem → Prop) :
    WordCode (L := L) ρ W
      (fun dst => floatSumMagnitudeL dst
        (fun j => floatNegativeSumL j
          (fun j => some ([ci 1 j (-10) 0], j+1))
          (fun j => some ([ci 1 j 13 0], j+1))
          (fun j => some ([ci 1 j 2 0], j+1)))
        (fun j => some ([ci 1 j 1 0], j+1))) (BitVec.ofInt 64 13) := by
  intro fp K dst code top hc hK m pc hp
  exact floatNegativeSumMagnitudeL_ok (-10) 13 2 (by decide) (by decide)
    (WordCode.const (-10) (by decide)) (WordCode.const 13 (by decide))
    (WordCode.const 2 (by decide)) (WordCode.const 1 (by decide)) hc hK m pc hp

omit [Kern] in
/-- Joint non-degenerate cancellation and tail boundaries of the canonical
    bridge: exact cancellation, a tiny negative result, and both signs. -/
theorem floatSumMagnitude_reconstruct_zeuge :
    floatSumMagnitude (-1) (2^1074-13) = 0 ∧
    floatSumMagnitude (-7) 3 = 6 ∧
    floatSumMagnitude 7 3 = 7 ∧
    floatSumMagnitude 0 0 = 0 ∧
    (((-1 : Int) * 2^1074 + (2^1074-13)).natAbs : Int) = 13 := by
  decide +kernel

#print axioms floatNegativeSumMagnitude_reconstruct
#print axioms floatNegativeSumMagnitudeL_ok_zeuge
#print axioms floatSumMagnitude_reconstruct
#print axioms floatSumMagnitudeL_ok
#print axioms floatNegativeSumMagnitudeL_ok
#print axioms floatSumMagnitude_reconstruct_zeuge
end Gabbro.Stage0.Senke
