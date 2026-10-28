import Grammatik.Code.Refine.Frag

/-
  File:      Grammatik/Code/Refine/Bits/Ops.lean
  Subject:   TRACK L, PHASE L1 -- THE INSTRUCTIONS OF THE SIGNED AND BITWISE OPERATIONS on encodings:
             what `Val.bin` does for `sdiv`, `srem`, `and`, `or`, `xor`, `shl`, `lshr`, each with the
             PRECONDITION of the instruction (`BinOp.ap` is stuck there) as a hypothesis on the numbers.

    * `sdiv`/`srem` -- the divisor is not zero and the dividend is not the least number of the width
      (`INT_MIN / -1` has no result on x86-64 and is a trap there; AArch64 and RISC-V differ), both
      operands are signed numbers of the width;
    * `and`/`or`/`xor` -- non-negative operands below `2^w`: the result is the bitwise result of the
      natural numbers;
    * `shl`/`lshr` -- the shift amount is below the width (an amount at or above it is stuck in `Code`),
      the shifted number is below `2^w`.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (tdiv_natAbs_le tmod_natAbs_lt)

theorem toInt_ofInt_sgn {w : Nat} (hw : 0 < w) {n : Int} (h1 : -(2 ^ (w - 1)) ≤ n) (h2 : n < 2 ^ (w - 1)) :
    (BitVec.ofInt w n).toInt = n := BitVec.toInt_ofInt_eq_self hw h1 h2

theorem val_bin_sdiv (W : Nat) (a b : Int) (hW : 0 < W) (ha1 : -(2 ^ (W - 1)) < a) (ha2 : a < 2 ^ (W - 1))
    (hb1 : -(2 ^ (W - 1)) ≤ b) (hb2 : b < 2 ^ (W - 1)) (hb0 : b ≠ 0) :
    Val.bin .sdiv W (Val.ofInt W a) (Val.ofInt W b) = some (Val.ofInt W (Int.tdiv a b)) := by
  have ea : (BitVec.ofInt W a).toInt = a := toInt_ofInt_sgn hW (by omega) ha2
  have eb : (BitVec.ofInt W b).toInt = b := toInt_ofInt_sgn hW hb1 hb2
  have hb' : BitVec.ofInt W b ≠ 0 := by
    intro h
    have := congrArg BitVec.toInt h
    rw [eb] at this
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toInt_zero] at this
    exact hb0 this
  have hne : ¬ ((BitVec.ofInt W b = 0) ∨
      ((BitVec.ofInt W a).toInt = -((2 : Int) ^ (W - 1)) ∧ (BitVec.ofInt W b).toInt = -1)) := by
    rw [ea]
    intro h
    rcases h with h | h
    · exact hb' h
    · omega
  simp only [Val.bin, BinOp.ap, Val.ofInt, if_neg hne, Option.map_some, dite_true]
  congr 2
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sdiv, ea, eb, BitVec.toInt_ofInt]

theorem val_bin_srem (W : Nat) (a b : Int) (hW : 0 < W) (ha1 : -(2 ^ (W - 1)) < a) (ha2 : a < 2 ^ (W - 1))
    (hb1 : -(2 ^ (W - 1)) ≤ b) (hb2 : b < 2 ^ (W - 1)) (hb0 : b ≠ 0) :
    Val.bin .srem W (Val.ofInt W a) (Val.ofInt W b) = some (Val.ofInt W (Int.tmod a b)) := by
  have ea : (BitVec.ofInt W a).toInt = a := toInt_ofInt_sgn hW (by omega) ha2
  have eb : (BitVec.ofInt W b).toInt = b := toInt_ofInt_sgn hW hb1 hb2
  have hb' : BitVec.ofInt W b ≠ 0 := by
    intro h
    have := congrArg BitVec.toInt h
    rw [eb] at this
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toInt_zero] at this
    exact hb0 this
  have hne : ¬ ((BitVec.ofInt W b = 0) ∨
      ((BitVec.ofInt W a).toInt = -((2 : Int) ^ (W - 1)) ∧ (BitVec.ofInt W b).toInt = -1)) := by
    rw [ea]
    intro h
    rcases h with h | h
    · exact hb' h
    · omega
  have hq : -(2 ^ (W - 1)) ≤ Int.tmod a b ∧ Int.tmod a b < 2 ^ (W - 1) := by
    have h1 := tmod_natAbs_lt a b hb0
    omega
  simp only [Val.bin, BinOp.ap, Val.ofInt, if_neg hne, Option.map_some, dite_true]
  congr 2
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_srem, ea, eb, toInt_ofInt_sgn hW hq.1 hq.2]

/-! ## Bitwise operations -/

theorem toNat_ofInt_nn {w : Nat} {a : Int} (h0 : 0 ≤ a) (h1 : a < 2 ^ w) :
    (BitVec.ofInt w a).toNat = a.toNat := Ar.toNat_ofInt_lt h0 h1

theorem toNat_lt_pow {w : Nat} {a : Int} (h0 : 0 ≤ a) (h1 : a < 2 ^ w) : a.toNat < 2 ^ w := by
  have h : (a.toNat : Int) < ((2 ^ w : Nat) : Int) := by
    rw [Int.toNat_of_nonneg h0]; exact_mod_cast h1
  exact_mod_cast h

theorem val_bin_andN (W : Nat) (a b : Int) (ha0 : 0 ≤ a) (ha1 : a < 2 ^ W) (hb0 : 0 ≤ b) (hb1 : b < 2 ^ W) :
    Val.bin .and W (Val.ofInt W a) (Val.ofInt W b) = some (Val.ofInt W ((a.toNat &&& b.toNat : Nat) : Int)) := by
  have hlt : ((a.toNat &&& b.toNat : Nat) : Int) < 2 ^ W := by
    have h := Nat.and_lt_two_pow a.toNat (y := b.toNat) (n := W) (toNat_lt_pow hb0 hb1)
    exact_mod_cast h
  simp only [Val.bin, BinOp.ap, Val.ofInt, Option.map_some, dite_true]
  congr 2
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofInt_nn ha0 ha1, toNat_ofInt_nn hb0 hb1, toNat_ofInt_nn (Int.natCast_nonneg _) hlt]
  simp only [Int.toNat_natCast]

theorem val_bin_orN (W : Nat) (a b : Int) (ha0 : 0 ≤ a) (ha1 : a < 2 ^ W) (hb0 : 0 ≤ b) (hb1 : b < 2 ^ W) :
    Val.bin .or W (Val.ofInt W a) (Val.ofInt W b) = some (Val.ofInt W ((a.toNat ||| b.toNat : Nat) : Int)) := by
  have hlt : ((a.toNat ||| b.toNat : Nat) : Int) < 2 ^ W := by
    have h := Nat.or_lt_two_pow (x := a.toNat) (y := b.toNat) (n := W) (toNat_lt_pow ha0 ha1) (toNat_lt_pow hb0 hb1)
    exact_mod_cast h
  simp only [Val.bin, BinOp.ap, Val.ofInt, Option.map_some, dite_true]
  congr 2
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, toNat_ofInt_nn ha0 ha1, toNat_ofInt_nn hb0 hb1, toNat_ofInt_nn (Int.natCast_nonneg _) hlt]
  simp only [Int.toNat_natCast]

theorem val_bin_xorN (W : Nat) (a b : Int) (ha0 : 0 ≤ a) (ha1 : a < 2 ^ W) (hb0 : 0 ≤ b) (hb1 : b < 2 ^ W) :
    Val.bin .xor W (Val.ofInt W a) (Val.ofInt W b) = some (Val.ofInt W ((a.toNat ^^^ b.toNat : Nat) : Int)) := by
  have hlt : ((a.toNat ^^^ b.toNat : Nat) : Int) < 2 ^ W := by
    have h := Nat.xor_lt_two_pow (x := a.toNat) (y := b.toNat) (n := W) (toNat_lt_pow ha0 ha1) (toNat_lt_pow hb0 hb1)
    exact_mod_cast h
  simp only [Val.bin, BinOp.ap, Val.ofInt, Option.map_some, dite_true]
  congr 2
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, toNat_ofInt_nn ha0 ha1, toNat_ofInt_nn hb0 hb1, toNat_ofInt_nn (Int.natCast_nonneg _) hlt]
  simp only [Int.toNat_natCast]

/-! ## Shifts -/

theorem shift_amount {W : Nat} {b : Int} (hb0 : 0 ≤ b) (hbW : b < (W : Int)) :
    (BitVec.ofInt W b).toNat = b.toNat ∧ b.toNat < W := by
  have hbl : b < 2 ^ W := Int.lt_of_lt_of_le hbW (by
    have := Nat.lt_two_pow_self (n := W)
    exact_mod_cast Nat.le_of_lt this)
  exact ⟨toNat_ofInt_nn hb0 hbl, by omega⟩

theorem val_bin_shl (W : Nat) (a b : Int) (ha0 : 0 ≤ a) (ha1 : a < 2 ^ W) (hb0 : 0 ≤ b) (hbW : b < (W : Int)) :
    Val.bin .shl W (Val.ofInt W a) (Val.ofInt W b) = some (Val.ofInt W (a * 2 ^ b.toNat)) := by
  obtain ⟨hbn, hlt⟩ := shift_amount hb0 hbW
  simp only [Val.bin, BinOp.ap, Val.ofInt, hbn, if_pos hlt, Option.map_some, dite_true]
  congr 2
  obtain ⟨a', rfl⟩ := Int.eq_ofNat_of_zero_le ha0
  have ea : ((a' : Int) * 2 ^ b.toNat) = ((a' * 2 ^ b.toNat : Nat) : Int) := by push_cast; rfl
  rw [ea, BitVec.ofInt_natCast, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft]
  simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_mul_mod]

theorem val_bin_lshr (W : Nat) (a b : Int) (ha0 : 0 ≤ a) (ha1 : a < 2 ^ W) (hb0 : 0 ≤ b) (hbW : b < (W : Int)) :
    Val.bin .lshr W (Val.ofInt W a) (Val.ofInt W b) = some (Val.ofInt W (a / 2 ^ b.toNat)) := by
  obtain ⟨hbn, hlt⟩ := shift_amount hb0 hbW
  simp only [Val.bin, BinOp.ap, Val.ofInt, hbn, if_pos hlt, Option.map_some, dite_true]
  congr 2
  obtain ⟨a', rfl⟩ := Int.eq_ofNat_of_zero_le ha0
  have ea : ((a' : Int) / 2 ^ b.toNat) = ((a' / 2 ^ b.toNat : Nat) : Int) := by push_cast; rfl
  rw [ea, BitVec.ofInt_natCast, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight]
  simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have h1 : a' < 2 ^ W := by exact_mod_cast ha1
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h1)]

end Gabbro.Code.Lower
