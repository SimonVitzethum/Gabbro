/- Shared nearest-even rounding for software floating-point routines.
   Comparing the remainder with its complement avoids doubling a word. -/
import Stage0.Senke.Ausdruck.Aggregat.Wort

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

/-- The increment is one exactly above half, or at half with an odd quotient. -/
def floatRoundUp (q r den : Nat) : Bool :=
  decide (den - r < r) || (decide (r = den - r) && decide (q % 2 = 1))

/-- This overflow-free decision is exactly the rounding decision of G. -/
theorem floatRoundUp_model (q r den : Nat) (hr : r < den) :
    Gleitkomma.rundeInt q r den = q + (if floatRoundUp q r den then 1 else 0) := by
  unfold Gleitkomma.rundeInt floatRoundUp
  by_cases ha : den < 2 * r
  · have hc : den - r < r := by omega
    simp [ha, hc]
  · have hc : ¬den - r < r := by omega
    by_cases hb : 2 * r < den
    · have hd : r ≠ den - r := by omega
      simp [ha, hb, hc, hd]
    · have hd : r = den - r := by omega
      have hd' : decide (r = den - r) = true := decide_eq_true hd
      simp only [ha, hb, hc, hd', ↓reduceIte, decide_true, decide_false,
        Bool.false_or, Bool.true_and, Bool.beq_eq_decide_eq]
      split <;> rename_i h <;> simp only [h, ↓reduceIte, Nat.add_zero]

/-- The word computation after the three inputs have been evaluated. -/
def floatRoundWord (q r den : Runner.W) : Runner.W :=
  q + (Runner.IR.bool ((den - r).slt r) |||
    (Runner.IR.bool (r == den - r) &&& Runner.IR.bool (q % 2 == 1)))

/-- Generic word-to-model bridge; no input enumeration or program-specific premise.
    The remainder and denominator fit signed words; the quotient uses all 64 bits.
    The result is a word, so its addition intentionally has the IR's modular meaning. -/
theorem floatRoundWord_model (q r den : Nat) (hr : r < den) (hd : den < 2 ^ 63) :
    floatRoundWord (BitVec.ofNat 64 q) (BitVec.ofNat 64 r) (BitVec.ofNat 64 den) =
      BitVec.ofNat 64 (Gleitkomma.rundeInt q r den) := by
  have hsub : BitVec.ofNat 64 den - BitVec.ofNat 64 r = BitVec.ofNat 64 (den - r) := by
    exact BitVec.ofNat_sub_ofNat_of_le den r (by omega) (by omega)
  have hs : (BitVec.ofNat 64 (den - r)).slt (BitVec.ofNat 64 r) = decide (den - r < r) := by
    rw [← BitVec.ofInt_natCast, ← BitVec.ofInt_natCast, slt_in (by omega) (by omega)]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  have he : (BitVec.ofNat 64 r == BitVec.ofNat 64 (den - r)) = decide (r = den - r) := by
    rw [← BitVec.ofInt_natCast, ← BitVec.ofInt_natCast, beq_in (by omega) (by omega)]
    simp only [Int.natCast_inj]
  have hp : (BitVec.ofNat 64 q % 2 == 1) = decide (q % 2 = 1) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj,
      BitVec.toNat_umod, BitVec.toNat_ofNat]
    change (q % 2^64 % 2 = 1 ↔ q % 2 = 1)
    have : q % 2 ^ 64 % 2 = q % 2 := Nat.mod_mod_of_dvd q (by decide)
    omega
  unfold floatRoundWord
  rw [hsub, hs, he, hp, bool_word, bool_word, bool_word, and_word, or_word,
    floatRoundUp_model q r den hr]
  unfold floatRoundUp
  split
  · exact (BitVec.ofNat_add q 1).symm
  · simp

/-- Both tie directions, the carry, and a remainder whose double would overflow signed 64 bits. -/
theorem floatRoundWord_model_zeuge :
    Gleitkomma.rundeInt 4 1 2 = 4 ∧ Gleitkomma.rundeInt 5 1 2 = 6 ∧
    Gleitkomma.rundeInt (2^53 - 1) 3 4 = 2^53 ∧
    floatRoundWord 7 (BitVec.ofNat 64 (2^63 - 2)) (BitVec.ofNat 64 (2^63 - 1)) = 8 := by
  decide +kernel

end Gabbro.Stage0.Senke
