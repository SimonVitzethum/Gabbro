/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Divide/Parts.lean
  Subject:   The parts of one restoring-division step: the top bit, the flag and mask, the selection.

  The dividend register's top bit is limb `k-1` shifted right by 63. The flag is `1 - sign` of the
  subtraction's top limb, the mask `0 - flag`; the selection keeps the remainder register or takes
  the difference limb by limb under the mask.
-/
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Divide.Shl1
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Neg
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Compare

namespace Gabbro.Stage0.Senke
open Runner.IR

/-- Limbs below the width ignore a reduction modulo `2^(64 k)`. -/
theorem lmb_mod (V k j : Nat) (hj : j < k) : lmb ((V % 2 ^ (64 * k) : Nat) : Int) j = lmb (V : Int) j := by
  apply BitVec.eq_of_toNat_eq
  rw [lmb_natCast_toNat, lmb_natCast_toNat]
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt hj
  have hp : 2 ^ (64 * (j + e + 1)) = 2 ^ (64 * j) * (2 ^ 64 * 2 ^ (64 * e)) := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
  rw [hp, Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod]

/-- The top bit of the top limb of a number below `2^(64 k)`. -/
theorem topbit_word (V k : Nat) (hk : 1 ≤ k) :
    lmb (V : Int) (k - 1) >>> ((BitVec.ofInt 64 63).toNat % 64) = BitVec.ofNat 64 (V / 2 ^ (64 * k - 1) % 2) := by
  apply BitVec.eq_of_toNat_eq
  have e63 : (BitVec.ofInt 64 63).toNat % 64 = 63 := by decide
  rw [e63, BitVec.toNat_ushiftRight, lmb_natCast_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  have hp : 2 ^ 64 = 2 ^ 63 * 2 := by norm_num
  rw [hp, Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have : 64 * (k - 1) + 63 = 64 * k - 1 := by omega
  rw [this]
  have h2 : V / 2 ^ (64 * k - 1) % 2 < 2 := Nat.mod_lt _ (by decide)
  exact (Nat.mod_eq_of_lt (by omega)).symm

/-! ## Flag and mask -/

theorem flagC_run (c Tk k : Nat) (h1 : Tk ≠ c + 4) (h2 : Tk ≠ c + 5) (s : Nat → Runner.W) (v : Int)
    (hTk : s Tk = lmb v k) (hr1 : -(2 ^ 63 * 2 ^ (64 * k)) ≤ v) (hr2 : v < 2 ^ 63 * 2 ^ (64 * k))
    (hC : s (c + 3) = BitVec.ofInt 64 63) (hO : s (c + 1) = 1) (hZ : s c = 0) :
    aluRun (flagC c Tk) s (c + 4) = (if 0 ≤ v then 1 else 0) ∧
    aluRun (flagC c Tk) s (c + 5) = (if 0 ≤ v then BitVec.allOnes 64 else 0) ∧
    ∀ i, i ≠ c + 4 → i ≠ c + 5 → aluRun (flagC c Tk) s i = s i := by
  have w1 : s Tk >>> ((s (c + 3)).toNat % 64) = Runner.IR.bool (decide (v < 0)) := by
    rw [hTk, hC]; exact sign_limb k v hr1 hr2
  have e : aluRun (flagC c Tk) s =
      slotUpd (slotUpd (slotUpd s (c + 4) (s Tk >>> ((s (c + 3)).toNat % 64))) (c + 4)
        (1 - s Tk >>> ((s (c + 3)).toNat % 64))) (c + 5) (0 - (1 - s Tk >>> ((s (c + 3)).toNat % 64))) := by
    funext i
    simp only [flagC, aluRun_cons, aluRun_nil, aluStep_shr, aluStep_sub, slotUpd]
    by_cases h3 : i = c + 5 <;> by_cases h4 : i = c + 4 <;> simp [h3, h4, hO, hZ]
  rw [e, w1]
  refine ⟨?_, ?_, fun i h3 h4 => ?_⟩
  · simp only [slotUpd]
    by_cases hv : 0 ≤ v
    · have hv' : ¬ v < 0 := by omega
      simp [hv, hv', Runner.IR.bool]
    · have hv' : v < 0 := by omega
      simp [hv, hv', Runner.IR.bool]
  · simp only [slotUpd]
    by_cases hv : 0 ≤ v
    · have hv' : ¬ v < 0 := by omega
      simp [hv, hv', Runner.IR.bool]
    · have hv' : v < 0 := by omega
      simp [hv, hv', Runner.IR.bool]
  · simp [slotUpd, h3, h4]

/-! ## Selection under the mask -/

theorem selSeq_value (R T MS TA n : Nat)
    (hd : R + n ≤ T ∧ T + n ≤ MS ∧ T + n ≤ TA ∧ MS ≠ TA) (s : Nat → Runner.W) :
    (∀ j, j < n → aluRun (selSeq R T MS TA n) s (R + j) =
      s (R + j) ^^^ ((s (R + j) ^^^ s (T + j)) &&& s MS)) ∧
    (∀ i, i ≠ TA → (i < R ∨ R + n ≤ i) → aluRun (selSeq R T MS TA n) s i = s i) := by
  have hpw : (List.range n).reverse.Pairwise (fun j' j => ¬ (R + j' = R + j ∨ R + j' = T + j ∨ R + j' = MS)) := by
    rw [List.pairwise_reverse]
    refine (List.pairwise_lt_range (n := n)).imp_of_mem (fun {x y} hx hy h => ?_)
    have hy' := List.mem_range.mp hy
    omega
  have hnd : (List.range n).reverse.Nodup := hpw.imp (fun {j' j} h e => h (Or.inl (by rw [e])))
  obtain ⟨v1, v2⟩ := seqC_value (fun j => selP (T + j) MS TA R j)
    (fun j s => s (R + j) ^^^ ((s (R + j) ^^^ s (T + j)) &&& s MS))
    (fun j i => i = R + j ∨ i = T + j ∨ i = MS) (fun i => i = TA) (fun j => j < n) R
    (fun j hj s => (selP_run (T + j) MS TA R j (by omega) (by omega) s).1)
    (fun j hj s i h1 h2 => (selP_run (T + j) MS TA R j (by omega) (by omega) s).2 i h1 h2)
    (fun j hj s s' h => by
      have h' : ∀ i, (i = R + j ∨ i = T + j ∨ i = MS) → s i = s' i := h
      beta_reduce
      rw [h' (R + j) (by omega), h' (T + j) (by omega), h' MS (by omega)])
    (fun j hj i h => by omega) (fun j hj => by omega) (List.range n).reverse
    (fun j hj => by simpa using hj) hnd hpw s
  refine ⟨fun j hj => v1 j (by simpa using hj), fun i h1 h2 => v2 i h1 (fun j hj => ?_)⟩
  have := List.mem_range.mp (List.mem_reverse.mp hj)
  omega

end Gabbro.Stage0.Senke
