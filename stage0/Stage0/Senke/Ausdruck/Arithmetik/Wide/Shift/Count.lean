/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Shift/Count.lean
  Subject:   Splitting a runtime shift count into limbs and bits, and the constant slots.

  From the count `n` in slot `a+k` the prelude computes `q = n / 64` (slot `+1`), `r = n % 64`
  (`+2`), `63 - r` (`+3`) and installs the constants one (`+4`) and zero (`+5`).
-/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Shift.Bit
@[expose] public section


namespace Gabbro.Stage0.Senke
open Runner.IR

@[simp] theorem shPre_length (k a : Nat) : (shPre k a).length = 7 := by rfl

theorem count_q (n : Nat) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> 6 = BitVec.ofNat 64 (n / 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow]
  omega

theorem count_r (n : Nat) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& 63#64 = BitVec.ofNat 64 (n % 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    show 63 % 2 ^ 64 = 2 ^ 6 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem count_w (n : Nat) (hn : n < 2 ^ 64) :
    63#64 - (BitVec.ofNat 64 n &&& 63#64) = BitVec.ofNat 64 (63 - n % 64) := by
  rw [count_r n hn]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hr : n % 64 < 64 := Nat.mod_lt _ (by decide)
  omega

theorem shPre_run (k a n : Nat) (hn : n < 2 ^ 64) (s : Nat → Runner.W) (hN : s (a + k) = BitVec.ofNat 64 n) :
    aluRun (shPre k a) s (a + k + 1) = BitVec.ofNat 64 (n / 64) ∧
    aluRun (shPre k a) s (a + k + 2) = BitVec.ofNat 64 (n % 64) ∧
    aluRun (shPre k a) s (a + k + 3) = BitVec.ofNat 64 (63 - n % 64) ∧
    aluRun (shPre k a) s (a + k + 4) = 1 ∧ aluRun (shPre k a) s (a + k + 5) = 0 ∧
    ∀ i, (i < a + k + 1 ∨ a + k + 9 ≤ i ∨ i = a + k + 6) → aluRun (shPre k a) s i = s i := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [shPre, aluRun_cons, aluRun_nil, aluStep_const, aluStep_shr, aluStep_and, aluStep_sub, slotUpd]
    simp [hN]
    exact count_q n hn
  · simp only [shPre, aluRun_cons, aluRun_nil, aluStep_const, aluStep_shr, aluStep_and, aluStep_sub, slotUpd]
    simp [hN]
    exact count_r n hn
  · simp only [shPre, aluRun_cons, aluRun_nil, aluStep_const, aluStep_shr, aluStep_and, aluStep_sub, slotUpd]
    simp [hN]
    exact count_w n hn
  · simp only [shPre, aluRun_cons, aluRun_nil, aluStep_const, aluStep_shr, aluStep_and, aluStep_sub, slotUpd]
    simp
  · simp only [shPre, aluRun_cons, aluRun_nil, aluStep_const, aluStep_shr, aluStep_and, aluStep_sub, slotUpd]
    simp
  · intro i hi
    simp only [shPre, aluRun_cons, aluRun_nil, aluStep_const, aluStep_shr, aluStep_and, aluStep_sub, slotUpd]
    have h1 : i ≠ a + k + 1 := by omega
    have h2 : i ≠ a + k + 2 := by omega
    have h3 : i ≠ a + k + 3 := by omega
    have h4 : i ≠ a + k + 4 := by omega
    have h5 : i ≠ a + k + 5 := by omega
    have h7 : i ≠ a + k + 7 := by omega
    have h8 : i ≠ a + k + 8 := by omega
    simp [h1, h2, h3, h4, h5, h7, h8]

end Gabbro.Stage0.Senke
