/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Neg.lean
  Subject:   Multiword negation as `0 - x`.

  The operand is copied to the second operand region, the first region is zeroed and the
  subtraction chain computes `0 - x` in place. Two's complement makes this exact modulo
  `2^(64k)`; the result type of `neg` always fits the limbs of its range.
-/
import Stage0.Senke.Ausdruck.Arithmetik.Wide.MulRun

namespace Gabbro.Stage0.Senke
open Runner.IR Runner.Mem

theorem copyUp_value : ∀ (n dst src : Nat) (s : Nat → Runner.W), src + n ≤ dst →
    (∀ j, j < n → aluRun (copyWords n dst src) s (dst + j) = s (src + j)) ∧
    (∀ j, (j < dst ∨ dst + n ≤ j) → aluRun (copyWords n dst src) s j = s j)
  | 0, dst, src, s, _ => ⟨fun j hj => absurd hj (by omega), fun j _ => rfl⟩
  | n + 1, dst, src, s, h => by
    obtain ⟨i1, i2⟩ := copyUp_value n (dst + 1) (src + 1) (aluStep ⟨2, dst, src, 0⟩ s) (by omega)
    have st : ∀ j, j ≠ dst → aluStep ⟨2, dst, src, 0⟩ s j = s j := fun j hj => slotUpd_other _ _ hj
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · simp only [copyWords, aluRun_cons]
      cases j with
      | zero =>
        show aluRun (copyWords n (dst + 1) (src + 1)) (aluStep ⟨2, dst, src, 0⟩ s) dst = s src
        rw [i2 dst (by omega)]
        show slotUpd s dst (s src) dst = s src
        rw [slotUpd_same]
      | succ j =>
        rw [show dst + (j + 1) = dst + 1 + j by omega, i1 j (by omega), st _ (by omega)]
        rw [show src + (j + 1) = src + 1 + j by omega]
    · simp only [copyWords, aluRun_cons]
      rw [i2 j (by omega), st j (by omega)]

def wideNegC (k a : Nat) : List II :=
  copyWords k (a + k) a ++ zeroSlotsC k a ++ wideAddC k a (-1) 1

theorem lmb_zero (j : Nat) : lmb 0 j = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [lmb]

theorem wideNeg_value (k a : Nat) (s : Nat → Runner.W) (x : Int)
    (hx : ∀ j, j < k → s (a + j) = lmb x j) :
    ∀ j, j < k → aluRun (wideNegC k a) s (a + j) = lmb (-x) j := by
  obtain ⟨c1, c2⟩ := copyUp_value k (a + k) a s (by omega)
  generalize hs1 : aluRun (copyWords k (a + k) a) s = s1 at c1 c2
  obtain ⟨z1, z2⟩ := zeroSlots_value k a s1
  generalize hs2 : aluRun (zeroSlotsC k a) s1 = s2 at z1 z2
  have hx2 : ∀ j, j < k → s2 (a + j) = lmb 0 j := fun j hj => by rw [lmb_zero]; exact z1 j hj
  have hy2 : ∀ j, j < k → s2 (a + k + j) = lmb x j := fun j hj => by
    rw [z2 _ (Or.inr (by omega)), c1 j hj, hx j hj]
  obtain ⟨v1, v2⟩ := wideSub_value k a s2 0 x hx2 hy2
  intro j hj
  have run : aluRun (wideNegC k a) s = aluRun (wideAddC k a (-1) 1) s2 := by
    simp only [wideNegC, aluRun_append, hs1, hs2]
  rw [run, v1 j hj]
  simp only [Int.zero_sub]

theorem wideNegC_aluIns {K k a : Nat} (hK : a + 2 * k + 7 ≤ K) : ∀ i ∈ wideNegC k a, AluIns K a i := by
  intro i hi
  simp only [wideNegC, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · exact copyWords_aluIns k (a + k) a (by omega) (by omega) (by omega) i hi
  · exact zeroSlots_aluIns k a (Nat.le_refl _) (by omega) i hi
  · exact wideAddC_aluIns (by decide) (by decide) hK i hi

variable [Kern]

theorem wideNeg_run {m : Runner.Mem} {pc fp : Runner.W} {K k a : Nat}
    (hF : FrameOK m fp K) (hK : K < 2 ^ 31) (hKa : a + 2 * k + 7 ≤ K)
    (hc : CodeAt m pc (wideNegC k a)) (hfar : CodeFar pc (wideNegC k a).length fp K) (x : Int)
    (hx : WordsAt m fp a (integerEncoding k x)) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (wideNegC k a).length), fp⟩ m' ∧
      Agree fp a K m m' ∧ WordsAt m' fp a (integerEncoding k (-x)) := by
  have hv : ∀ j, j < K → m.rd64 (slot fp (BitVec.ofNat 64 j)) = some (slotVal m fp j) :=
    fun j hj => slotVal_rd hF hj
  obtain ⟨m', st, ag, rd⟩ := alu_run hF hK hc hfar (wideNegC_aluIns hKa) (slotVal m fp) hv
  exact ⟨m', st, ag, words_of_slotVal (-x) (by omega) _ rd
    (wideNeg_value k a (slotVal m fp) x (slotVal_words hF (by omega) x hx))⟩

end Gabbro.Stage0.Senke
