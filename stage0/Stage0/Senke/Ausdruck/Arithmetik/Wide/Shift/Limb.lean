/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Shift/Limb.lean
  Subject:   Limbs of shifted natural numbers.

  The limbs of `X * 2^(64c)` and `X / 2^(64c)` are the limbs of `X` moved by `c` positions, and the
  limbs of `X * 2^r` and `X / 2^r` for a bit count `r < 64` combine the limb with its neighbour:
  `(L_j << r) | ((L_(j-1) >> 1) >> (63 - r))` resp. `(L_j >> r) | ((L_(j+1) << 1) << (63 - r))`.
  The double shift keeps the word operations total at `r = 0`, where a shift by 64 would wrap.
-/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Shift.Piece
@[expose] public section


namespace Gabbro.Stage0.Senke
open Runner.IR

theorem lmb_testBit (X j i : Nat) :
    (lmb (X : Int) j).toNat.testBit i = (decide (i < 64) && X.testBit (i + 64 * j)) := by
  rw [lmb_natCast_toNat, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]

/-- A limb of a number below `2^(64k)` beyond the `k` limbs is zero. -/
theorem lmb_high (X k j : Nat) (hX : X < 2 ^ (64 * k)) (hj : k ≤ j) : lmb (X : Int) j = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [lmb_natCast_toNat]
  have : X / 2 ^ (64 * j) = 0 :=
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hX (Nat.pow_le_pow_right (by decide) (by omega)))
  simp [this]

theorem lmb_shl_limbs (X c j : Nat) :
    lmb ((X * 2 ^ (64 * c) : Nat) : Int) j = if c ≤ j then lmb (X : Int) (j - c) else 0 := by
  apply BitVec.eq_of_toNat_eq
  split
  · rename_i h
    rw [lmb_natCast_toNat, lmb_natCast_toNat]
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_sub_cancel_left, Nat.mul_add, Nat.pow_add, Nat.mul_comm X, Nat.mul_div_mul_left _ _ (by positivity)]
  · rename_i h
    rw [lmb_natCast_toNat]
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt (Nat.lt_of_not_le h)
    have hp : 2 ^ (64 * (j + e + 1)) = 2 ^ (64 * j) * (2 ^ 64 * 2 ^ (64 * e)) := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
    rw [hp, show X * (2 ^ (64 * j) * (2 ^ 64 * 2 ^ (64 * e))) = 2 ^ (64 * j) * (2 ^ 64 * (X * 2 ^ (64 * e))) by
      simp only [Nat.mul_left_comm, Nat.mul_comm],
      Nat.mul_div_cancel_left _ (by positivity), Nat.mul_mod_right]
    rfl

theorem lmb_shr_limbs (X c j : Nat) :
    lmb ((X / 2 ^ (64 * c) : Nat) : Int) j = lmb (X : Int) (j + c) := by
  apply BitVec.eq_of_toNat_eq
  rw [lmb_natCast_toNat, lmb_natCast_toNat, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 3
  omega

/-! ## Bit shifts with a neighbouring limb -/

theorem shlBit_word (X r j : Nat) (hr : r < 64) (rw' o w prev : Runner.W) (hrw : rw'.toNat = r)
    (ho : o.toNat = 1) (hw : w.toNat = 63 - r)
    (hp : prev = if j = 0 then 0 else lmb (X : Int) (j - 1)) :
    lmb ((X * 2 ^ r : Nat) : Int) j =
      (lmb (X : Int) j <<< (rw'.toNat % 64)) ||| ((prev >>> (o.toNat % 64)) >>> (w.toNat % 64)) := by
  apply BitVec.eq_of_toNat_eq
  apply Nat.eq_of_testBit_eq
  intro i
  have h1 : o.toNat % 64 = 1 := by omega
  have h2 : rw'.toNat % 64 = r := by omega
  have h3 : w.toNat % 64 = 63 - r := by omega
  rw [h1, h2, h3]
  subst hp
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.testBit_or,
      Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, lmb_testBit,
      Nat.testBit_mul_two_pow, ite_true]
    have z : BitVec.toNat (0 : Runner.W) = 0 := rfl
    rw [z, Nat.zero_testBit]
    by_cases h4 : i < 64
    · by_cases h5 : r ≤ i
      · have h6 : i - r < 64 := by omega
        simp [h4, h5, h6]
      · simp [h4, h5]
    · simp [h4]
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.testBit_or,
      Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, lmb_testBit,
      Nat.testBit_mul_two_pow, Nat.add_one_ne_zero, ite_false]
    have e0 : j' + 1 - 1 = j' := by omega
    rw [e0]
    by_cases h4 : i < 64
    · by_cases h5 : r ≤ i
      · have e1 : i + 64 * (j' + 1) - r = i - r + 64 * (j' + 1) := by omega
        have h6 : i - r < 64 := by omega
        have h7 : ¬ (1 + (63 - r + i) < 64) := by omega
        have h8 : r ≤ i + 64 * (j' + 1) := by omega
        simp [h4, h5, h6, h7, h8, e1]
      · have e2 : 1 + (63 - r + i) + 64 * j' = i + 64 * (j' + 1) - r := by omega
        have h7 : 1 + (63 - r + i) < 64 := by omega
        have h8 : r ≤ i + 64 * (j' + 1) := by omega
        simp [h4, h5, h7, h8, e2]
    · have h7 : ¬ (1 + (63 - r + i) < 64) := by omega
      simp [h4, h7]

theorem shrBit_word (X r j : Nat) (hr : r < 64) (rw' o w : Runner.W) (hrw : rw'.toNat = r)
    (ho : o.toNat = 1) (hw : w.toNat = 63 - r) :
    lmb ((X / 2 ^ r : Nat) : Int) j =
      (lmb (X : Int) j >>> (rw'.toNat % 64)) |||
        ((lmb (X : Int) (j + 1) <<< (o.toNat % 64)) <<< (w.toNat % 64)) := by
  apply BitVec.eq_of_toNat_eq
  apply Nat.eq_of_testBit_eq
  intro i
  have h1 : o.toNat % 64 = 1 := by omega
  have h2 : rw'.toNat % 64 = r := by omega
  have h3 : w.toNat % 64 = 63 - r := by omega
  rw [h1, h2, h3]
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.testBit_or,
    Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, lmb_testBit,
    Nat.shiftRight_eq_div_pow, Nat.testBit_div_two_pow]
  have e1 : r + i + 64 * j = i + 64 * j + r := by omega
  have e1' : i + r + 64 * j = i + 64 * j + r := by omega
  by_cases h4 : i < 64
  · by_cases h5 : r + i < 64
    · have h5' : i + r < 64 := by omega
      have h6 : ¬ (1 ≤ i - (63 - r)) := by omega
      simp [h4, h5', h6, e1']
    · have h5' : ¬ (i + r < 64) := by omega
      have e2 : i - (63 - r) - 1 + 64 * (j + 1) = i + 64 * j + r := by omega
      have h6 : i ≥ 63 - r := by omega
      have h7 : i - (63 - r) < 64 := by omega
      have h8 : 1 ≤ i - (63 - r) := by omega
      have h9 : i - (63 - r) - 1 < 64 := by omega
      simp [h4, h5', h6, h7, h8, h9, e2]
  · have h5' : ¬ (i + r < 64) := by omega
    simp [h4, h5']

end Gabbro.Stage0.Senke
