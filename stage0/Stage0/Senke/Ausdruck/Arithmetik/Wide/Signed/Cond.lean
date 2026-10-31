/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Signed/Cond.lean
  Subject:   Conditional negation of a multiword value under a runtime flag, and the frame of admitted code.

  `condNegC` copies the limbs above, negates the copy (`0 - x`, exact modulo `2^(64k)`), turns the
  flag word into a full mask and selects the copy limb by limb. The signed division reduces to the
  unsigned one on magnitudes with this block on both sides.
-/
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Divide.Run

namespace Gabbro.Stage0.Senke
open Runner.IR

/-- Slots at or above the executor's bound are never written. -/
theorem aluRun_high {K d : Nat} {code : List II} (h : ∀ i ∈ code, AluIns K d i) (s : Nat → Runner.W) {j : Nat}
    (hj : K ≤ j) : aluRun code s j = s j := by
  induction code generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [aluRun_cons]
    rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    have hA := h i (List.mem_cons_self ..)
    show slotUpd s i.a.toNat (aluVal i s) j = s j
    apply slotUpd_other
    cases hA <;> (simp only [ci, Int.toNat_natCast]; omega)

def condNegC (k p c F MS TA Z : Nat) : List II :=
  copyWords k c p ++ wideNegC k c ++ [cn 4 MS Z F] ++ selSeq p c MS TA k

theorem mask_of_flag (f : Nat) (hf : f < 2) :
    (0 : Runner.W) - BitVec.ofNat 64 f = if f = 1 then BitVec.allOnes 64 else 0 := by
  rcases (by omega : f = 0 ∨ f = 1) with rfl | rfl <;> decide

theorem condNeg_value (k p c F MS TA Z : Nat)
    (hd : p + k ≤ c ∧ c + 2 * k + 7 ≤ F ∧ c + 2 * k + 7 ≤ MS ∧ c + 2 * k + 7 ≤ TA ∧ c + 2 * k + 7 ≤ Z ∧
      MS ≠ TA ∧ MS ≠ F ∧ MS ≠ Z ∧ TA ≠ F ∧ TA ≠ Z)
    (s : Nat → Runner.W) (x : Int) (f : Nat) (hf : f < 2) (hl : ∀ j, j < k → s (p + j) = lmb x j)
    (hF : s F = BitVec.ofNat 64 f) (hZ : s Z = 0) :
    (∀ j, j < k → aluRun (condNegC k p c F MS TA Z) s (p + j) = lmb (if f = 1 then -x else x) j) ∧
    (∀ i, i ≠ MS → i ≠ TA → (i < p ∨ p + k ≤ i) → (i < c ∨ c + 2 * k + 7 ≤ i) →
      aluRun (condNegC k p c F MS TA Z) s i = s i) := by
  obtain ⟨c1, c2⟩ := copyUp_value k c p s (by omega)
  obtain ⟨s1, hs1⟩ : ∃ s1, s1 = aluRun (copyWords k c p) s := ⟨_, rfl⟩
  rw [← hs1] at c1 c2
  have hx1 : ∀ j, j < k → s1 (c + j) = lmb x j := fun j hj => by rw [c1 j hj]; exact hl j hj
  have n1 := wideNeg_value k c s1 x hx1
  have nF : ∀ i, (i < c ∨ c + 2 * k + 7 ≤ i) → aluRun (wideNegC k c) s1 i = s1 i := fun i hi => by
    have hA := wideNegC_aluIns (K := c + 2 * k + 7) (k := k) (a := c) (Nat.le_refl _)
    rcases hi with hi | hi
    · exact aluRun_low hA s1 hi
    · exact aluRun_high hA s1 hi
  obtain ⟨s2, hs2⟩ : ∃ s2, s2 = aluRun (wideNegC k c) s1 := ⟨_, rfl⟩
  rw [← hs2] at n1 nF
  have e3 : ∀ i, aluRun [cn 4 MS Z F] s2 i = if i = MS then s2 Z - s2 F else s2 i := fun i => by
    simp only [aluRun_cons, aluRun_nil, aluStep_sub, slotUpd]
  obtain ⟨s3, hs3⟩ : ∃ s3, s3 = aluRun [cn 4 MS Z F] s2 := ⟨_, rfl⟩
  have s3MS : s3 MS = if f = 1 then BitVec.allOnes 64 else 0 := by
    rw [hs3, e3]; simp only [↓reduceIte]
    rw [nF Z (Or.inr (by omega)), nF F (Or.inr (by omega)), c2 Z (Or.inr (by omega)),
      c2 F (Or.inr (by omega)), hZ, hF]
    exact mask_of_flag f hf
  have s3o : ∀ i, i ≠ MS → s3 i = s2 i := fun i hi => by rw [hs3, e3]; simp [hi]
  obtain ⟨u1, u2⟩ := selSeq_value p c MS TA k (by omega) s3
  obtain ⟨s4, hs4⟩ : ∃ s4, s4 = aluRun (selSeq p c MS TA k) s3 := ⟨_, rfl⟩
  rw [← hs4] at u1 u2
  have run : aluRun (condNegC k p c F MS TA Z) s = s4 := by
    simp only [condNegC, aluRun_append]
    rw [hs4, hs3, hs2, hs1]
  rw [run]
  refine ⟨fun j hj => ?_, fun i h1 h2 h3 h4 => ?_⟩
  · rw [u1 j hj, s3o _ (by omega), nF _ (Or.inl (by omega)), c2 _ (Or.inl (by omega)), hl j hj,
      s3o _ (by omega), n1 j hj, s3MS]
    by_cases hf1 : f = 1
    · simp only [hf1, ↓reduceIte]; exact sel_ones _ _
    · simp only [hf1, ↓reduceIte]; exact sel_zero _ _
  · rw [u2 i h2 h3, s3o i h1, nF i h4, c2 i (by omega)]

end Gabbro.Stage0.Senke
