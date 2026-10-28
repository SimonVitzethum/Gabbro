/-
  File:      stage0/Stage0/Senke/Ausdruck/Wort.lean
  Subject:   The IR's word operations against G's integer operations: division and remainder (`sdiv`, `srem` of
             `Runner.IR`), the bitwise operations and the shifts, on words that hold their value exactly.
-/
import Stage0.Senke.Ausdruck

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration}

/-! ## Words of values -/

theorem toInt_ofInt_in {x : Int} (h1 : -2 ^ 63 ≤ x) (h2 : x < 2 ^ 63) : (BitVec.ofInt 64 x).toInt = x := by
  rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]

theorem slt_in {x y : Int} (hx : -2 ^ 63 ≤ x ∧ x < 2 ^ 63) (hy : -2 ^ 63 ≤ y ∧ y < 2 ^ 63) :
    (BitVec.ofInt 64 x).slt (BitVec.ofInt 64 y) = decide (x < y) := by
  rw [BitVec.slt_eq_decide, toInt_ofInt_in hx.1 hx.2, toInt_ofInt_in hy.1 hy.2]

theorem beq_in {x y : Int} (hx : -2 ^ 63 ≤ x ∧ x < 2 ^ 63) (hy : -2 ^ 63 ≤ y ∧ y < 2 ^ 63) :
    (BitVec.ofInt 64 x == BitVec.ofInt 64 y) = decide (x = y) := by
  by_cases h : x = y
  · subst h; simp
  · have : BitVec.ofInt 64 x ≠ BitVec.ofInt 64 y := fun he => h (by
      have := congrArg BitVec.toInt he
      rwa [toInt_ofInt_in hx.1 hx.2, toInt_ofInt_in hy.1 hy.2] at this)
    simp [h, this]

theorem inW_spec {lo hi : Int} (h : inW lo hi = true) {x : Int} (h1 : lo ≤ x) (h2 : x ≤ hi) :
    -2 ^ 63 ≤ x ∧ x < 2 ^ 63 := by
  simp only [inW, Bool.and_eq_true, decide_eq_true_eq] at h; omega

theorem ofInt_sub' (x y : Int) : BitVec.ofInt 64 (x - y) = BitVec.ofInt 64 x - BitVec.ofInt 64 y := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

theorem and_word (x y : Bool) : ((if x = true then (1 : Runner.W) else 0) &&& (if y = true then 1 else 0)) =
    if (x && y) = true then 1 else 0 := by cases x <;> cases y <;> decide

theorem or_word (x y : Bool) : ((if x = true then (1 : Runner.W) else 0) ||| (if y = true then 1 else 0)) =
    if (x || y) = true then 1 else 0 := by cases x <;> cases y <;> decide

theorem not_word (x : Bool) : ((if x = true then (1 : Runner.W) else 0) ^^^ BitVec.ofInt 64 1) =
    if (!x) = true then 1 else 0 := by cases x <;> decide

theorem bool_word (b : Bool) : Runner.IR.bool b = (if b = true then 1 else 0) := by cases b <;> rfl

theorem sdiv_w {a b : Int} (ha1 : -2 ^ 63 < a) (ha2 : a < 2 ^ 63) (hb1 : -2 ^ 63 ≤ b) (hb2 : b < 2 ^ 63)
    (hb : b ≠ 0) : sdiv (BitVec.ofInt 64 a) (BitVec.ofInt 64 b) = some (BitVec.ofInt 64 (a.tdiv b)) := by
  have hq : (a.tdiv b).natAbs ≤ a.natAbs := by rw [Int.natAbs_tdiv]; exact Nat.div_le_self _ _
  simp only [sdiv, toInt_ofInt_in (by omega : -2 ^ 63 ≤ a) ha2, toInt_ofInt_in hb1 hb2, hb, ↓reduceIte]
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]

theorem srem_w {a b : Int} (ha1 : -2 ^ 63 < a) (ha2 : a < 2 ^ 63) (hb1 : -2 ^ 63 ≤ b) (hb2 : b < 2 ^ 63)
    (hb : b ≠ 0) : srem (BitVec.ofInt 64 a) (BitVec.ofInt 64 b) = some (BitVec.ofInt 64 (a.tmod b)) := by
  have hq : (a.tdiv b).natAbs ≤ a.natAbs := by rw [Int.natAbs_tdiv]; exact Nat.div_le_self _ _
  simp only [srem, toInt_ofInt_in (by omega : -2 ^ 63 ≤ a) ha2, toInt_ofInt_in hb1 hb2, hb, ↓reduceIte]
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]

/-- A nonnegative value below `2^63` is the word of its natural number. -/
theorem ofInt_nat {x : Int} (h0 : 0 ≤ x) (h1 : x < 2 ^ 63) : (BitVec.ofInt 64 x).toNat = x.toNat := by
  rw [BitVec.toNat_ofInt]; omega

theorem ofInt_natCast (n : Nat) (h : n < 2 ^ 64) : (BitVec.ofInt 64 (n : Int)).toNat = n := by
  rw [BitVec.toNat_ofInt]; omega

theorem and_w {a b : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ 63) (hb0 : 0 ≤ b) (hb1 : b < 2 ^ 63) :
    BitVec.ofInt 64 a &&& BitVec.ofInt 64 b = BitVec.ofInt 64 ((a.toNat &&& b.toNat : Nat) : Int) := by
  apply BitVec.eq_of_toNat_eq
  have hl : a.toNat &&& b.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt Nat.and_le_left (by omega)
  rw [BitVec.toNat_and, ofInt_nat ha0 ha1, ofInt_nat hb0 hb1, ofInt_natCast _ hl]

theorem or_w {a b : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ 63) (hb0 : 0 ≤ b) (hb1 : b < 2 ^ 63) :
    BitVec.ofInt 64 a ||| BitVec.ofInt 64 b = BitVec.ofInt 64 ((a.toNat ||| b.toNat : Nat) : Int) := by
  apply BitVec.eq_of_toNat_eq
  have hl : a.toNat ||| b.toNat < 2 ^ 64 := Nat.or_lt_two_pow (by omega) (by omega)
  rw [BitVec.toNat_or, ofInt_nat ha0 ha1, ofInt_nat hb0 hb1, ofInt_natCast _ hl]

theorem xor_w {a b : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ 63) (hb0 : 0 ≤ b) (hb1 : b < 2 ^ 63) :
    BitVec.ofInt 64 a ^^^ BitVec.ofInt 64 b = BitVec.ofInt 64 ((a.toNat ^^^ b.toNat : Nat) : Int) := by
  apply BitVec.eq_of_toNat_eq
  have hl : a.toNat ^^^ b.toNat < 2 ^ 64 := Nat.xor_lt_two_pow (by omega) (by omega)
  rw [BitVec.toNat_xor, ofInt_nat ha0 ha1, ofInt_nat hb0 hb1, ofInt_natCast _ hl]

/-- `shl` modulo `2^64`: the word of `a · 2^b` for every `a`, a shift count below 64. -/
theorem shl_w (a : Int) {b : Int} (hb0 : 0 ≤ b) (hb1 : b < 64) :
    BitVec.ofInt 64 a <<< ((BitVec.ofInt 64 b).toNat % 64) = BitVec.ofInt 64 (a * 2 ^ b.toNat) := by
  rw [ofInt_nat hb0 (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.ofInt_mul]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have e : ((2 : Int) ^ b.toNat) = ((2 ^ b.toNat : Nat) : Int) := by simp
  rw [BitVec.toNat_twoPow, e, BitVec.toNat_ofInt]
  omega

theorem shr_w {a b : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ 63) (hb0 : 0 ≤ b) (hb1 : b < 64) :
    BitVec.ofInt 64 a >>> ((BitVec.ofInt 64 b).toNat % 64) = BitVec.ofInt 64 (a / 2 ^ b.toNat) := by
  rw [ofInt_nat hb0 (by omega), Nat.mod_eq_of_lt (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, ofInt_nat ha0 ha1]
  have h2 : (0 : Int) ≤ a / 2 ^ b.toNat := Int.ediv_nonneg ha0 (Int.pow_nonneg (by decide))
  rw [ofInt_nat h2 (by
    have := Int.ediv_le_self (2 ^ b.toNat) ha0
    omega)]
  rw [Nat.shiftRight_eq_div_pow]
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha0
  have e : ((2 : Int) ^ b.toNat) = ((2 ^ b.toNat : Nat) : Int) := by simp
  rw [e, ← Int.natCast_ediv, Int.toNat_natCast, Int.toNat_natCast]

end Gabbro.Stage0.Senke
