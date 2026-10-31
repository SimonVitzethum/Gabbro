/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Divide/Step.lean
  Subject:   One step of restoring division on canonical limbs.

  Registers (`k` limbs for the dividend/quotient register `X` at `a`, `k+1` limbs for the remainder
  register `R` at `a+k`, the trial difference `T` at `a+2k+1`, the divisor `D'` with a zero top limb at
  `a+3k+2`, the subtraction scratch, then eight scalar slots from `c = a+4k+10`: zero, one, 62, 63,
  carry word, mask and two temporaries). A step takes the top bit `b` of `X`, forms `R' = 2R + b`,
  subtracts the divisor, and keeps the difference iff `R' >= y`; `X` shifts left taking the flag in.
-/
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Divide.Parts

namespace Gabbro.Stage0.Senke
open Runner.IR

def dvStep (k a c : Nat) : List II :=
  [cn 12 (c + 4) (a + (k - 1)) (c + 3)] ++
  shl1C (a + k) (k + 1) (c + 1) (c + 2) (c + 4) (c + 6) (c + 7) ++
  copyWords (k + 1) (a + 2 * k + 1) (a + k) ++
  wideAddC (k + 1) (a + 2 * k + 1) (-1) 1 ++
  flagC c (a + 2 * k + 1 + k) ++
  selSeq (a + k) (a + 2 * k + 1) (c + 5) (c + 6) (k + 1) ++
  shl1C a k (c + 1) (c + 2) (c + 4) (c + 6) (c + 7)

/-- The state a step starts from and leaves behind: the two registers, the divisor, the constants. -/
def DvRep (k a c y : Nat) (s : Nat → Runner.W) (xv rv : Nat) : Prop :=
  (∀ j, j < k → s (a + j) = lmb (xv : Int) j) ∧
  (∀ j, j < k + 1 → s (a + k + j) = lmb (rv : Int) j) ∧
  (∀ j, j < k + 1 → s (a + 3 * k + 2 + j) = lmb (y : Int) j) ∧
  s c = 0 ∧ s (c + 1) = 1 ∧ (s (c + 2)).toNat = 62 ∧ s (c + 3) = BitVec.ofInt 64 63

/-- The next register contents. -/
def dvNext (k y xv rv : Nat) : Nat × Nat :=
  let b := xv / 2 ^ (64 * k - 1) % 2
  let g := if y ≤ rv * 2 + b then 1 else 0
  ((xv * 2 + g) % 2 ^ (64 * k), rv * 2 + b - g * y)

theorem dvStep_value (k a c y xv rv : Nat) (hk : 1 ≤ k) (hc : c = a + 4 * k + 10)
    (hy : y < 2 ^ (64 * k)) (hr : rv < y) (s : Nat → Runner.W) (hs : DvRep k a c y s xv rv) :
    DvRep k a c y (aluRun (dvStep k a c) s) (dvNext k y xv rv).1 (dvNext k y xv rv).2 := by
  subst hc
  obtain ⟨hX, hR, hD, hZ, hO, hW, hC⟩ := hs
  obtain ⟨b, hb⟩ : ∃ b, b = xv / 2 ^ (64 * k - 1) % 2 := ⟨_, rfl⟩
  have hb2 : b < 2 := by rw [hb]; exact Nat.mod_lt _ (by decide)
  obtain ⟨g, hg⟩ : ∃ g : Nat, g = if y ≤ rv * 2 + b then 1 else 0 := ⟨_, rfl⟩
  have hg2 : g < 2 := by rw [hg]; split <;> omega
  have hnext : dvNext k y xv rv = ((xv * 2 + g) % 2 ^ (64 * k), rv * 2 + b - g * y) := by
    simp only [dvNext, ← hb, ← hg]
  rw [hnext]
  have hP : 0 < 2 ^ (64 * k) := by positivity
  -- segment 1: the top bit of the dividend register
  obtain ⟨s1, hs1⟩ : ∃ s1, s1 = aluRun [cn 12 (a + 4 * k + 10 + 4) (a + (k - 1)) (a + 4 * k + 10 + 3)] s := ⟨_, rfl⟩
  have e1 : ∀ i, s1 i = if i = a + 4 * k + 10 + 4 then
      s (a + (k - 1)) >>> ((s (a + 4 * k + 10 + 3)).toNat % 64) else s i := by
    intro i
    rw [hs1]
    simp only [aluRun_cons, aluRun_nil, aluStep_shr, slotUpd]
  have s1TB : s1 (a + 4 * k + 10 + 4) = BitVec.ofNat 64 b := by
    rw [e1]
    simp only [↓reduceIte]
    rw [hX (k - 1) (by omega), hC, hb]
    exact topbit_word xv k hk
  have s1o : ∀ i, i ≠ a + 4 * k + 10 + 4 → s1 i = s i := fun i hi => by simp [e1, hi]
  -- segment 2: R := 2 R + b
  obtain ⟨p2, p2f⟩ := shl1C_limbs (a + k) (k + 1) (a + 4 * k + 10 + 1) (a + 4 * k + 10 + 2)
    (a + 4 * k + 10 + 4) (a + 4 * k + 10 + 6) (a + 4 * k + 10 + 7) (by omega) rv b hb2 s1
    (fun j hj => by rw [s1o _ (by omega)]; exact hR j hj)
    (by rw [s1o _ (by omega), hO]; rfl) (by rw [s1o _ (by omega)]; exact hW) s1TB
  obtain ⟨s2, hs2⟩ : ∃ s2, s2 = aluRun (shl1C (a + k) (k + 1) (a + 4 * k + 10 + 1) (a + 4 * k + 10 + 2)
    (a + 4 * k + 10 + 4) (a + 4 * k + 10 + 6) (a + 4 * k + 10 + 7)) s1 := ⟨_, rfl⟩
  rw [← hs2] at p2 p2f
  -- segment 3: T := R
  obtain ⟨p3, p3f⟩ := copyUp_value (k + 1) (a + 2 * k + 1) (a + k) s2 (by omega)
  obtain ⟨s3, hs3⟩ : ∃ s3, s3 = aluRun (copyWords (k + 1) (a + 2 * k + 1) (a + k)) s2 := ⟨_, rfl⟩
  rw [← hs3] at p3 p3f
  -- segment 4: T := T - D'
  have h4x : ∀ j, j < k + 1 → s3 (a + 2 * k + 1 + j) = lmb ((rv * 2 + b : Nat) : Int) j := fun j hj => by
    rw [p3 j hj]
    exact p2 j hj
  have h4y : ∀ j, j < k + 1 → s3 (a + 2 * k + 1 + (k + 1) + j) = lmb (y : Int) j := fun j hj => by
    rw [p3f _ (Or.inr (by omega)), p2f _ (by omega) (by omega) (Or.inr (by omega)), s1o _ (by omega)]
    have := hD j hj
    rw [show a + 3 * k + 2 + j = a + 2 * k + 1 + (k + 1) + j by omega] at this
    exact this
  obtain ⟨p4, p4f⟩ := wideSub_value (k + 1) (a + 2 * k + 1) s3 ((rv * 2 + b : Nat) : Int) (y : Int) h4x h4y
  obtain ⟨s4, hs4⟩ : ∃ s4, s4 = aluRun (wideAddC (k + 1) (a + 2 * k + 1) (-1) 1) s3 := ⟨_, rfl⟩
  rw [← hs4] at p4 p4f
  -- segment 5: the flag and the mask
  have h5C : s4 (a + 4 * k + 10 + 3) = BitVec.ofInt 64 63 := by
    rw [p4f _ (Or.inr (Or.inl (by omega))), p3f _ (Or.inr (by omega)),
      p2f _ (by omega) (by omega) (Or.inr (by omega)), s1o _ (by omega)]
    exact hC
  have h5O : s4 (a + 4 * k + 10 + 1) = 1 := by
    rw [p4f _ (Or.inr (Or.inl (by omega))), p3f _ (Or.inr (by omega)),
      p2f _ (by omega) (by omega) (Or.inr (by omega)), s1o _ (by omega)]
    exact hO
  have h5Z : s4 (a + 4 * k + 10) = 0 := by
    rw [p4f _ (Or.inr (Or.inl (by omega))), p3f _ (Or.inr (by omega)),
      p2f _ (by omega) (by omega) (Or.inr (by omega)), s1o _ (by omega)]
    exact hZ
  have hyI : (y : Int) < (2 : Int) ^ (64 * k) := by exact_mod_cast hy
  have hPI : (0 : Int) < (2 : Int) ^ (64 * k) := by positivity
  obtain ⟨q1, q2, q3⟩ := flagC_run (a + 4 * k + 10) (a + 2 * k + 1 + k) k (by omega) (by omega) s4
    (((rv * 2 + b : Nat) : Int) - (y : Int)) (p4 k (by omega)) (by omega) (by omega) h5C h5O h5Z
  obtain ⟨s5, hs5⟩ : ∃ s5, s5 = aluRun (flagC (a + 4 * k + 10) (a + 2 * k + 1 + k)) s4 := ⟨_, rfl⟩
  rw [← hs5] at q1 q2 q3
  have hge : (0 : Int) ≤ ((rv * 2 + b : Nat) : Int) - (y : Int) ↔ y ≤ rv * 2 + b := by omega
  -- segment 6: select the difference under the mask
  obtain ⟨u1, u2⟩ := selSeq_value (a + k) (a + 2 * k + 1) (a + 4 * k + 10 + 5) (a + 4 * k + 10 + 6) (k + 1)
    (by omega) s5
  obtain ⟨s6, hs6⟩ : ∃ s6, s6 = aluRun (selSeq (a + k) (a + 2 * k + 1) (a + 4 * k + 10 + 5)
    (a + 4 * k + 10 + 6) (k + 1)) s5 := ⟨_, rfl⟩
  rw [← hs6] at u1 u2
  have r5R : ∀ j, j < k + 1 → s5 (a + k + j) = lmb ((rv * 2 + b : Nat) : Int) j := fun j hj => by
    rw [q3 _ (by omega) (by omega), p4f _ (Or.inl (by omega)), p3f _ (Or.inl (by omega))]
    exact p2 j hj
  have r5T : ∀ j, j < k + 1 → s5 (a + 2 * k + 1 + j) = lmb (((rv * 2 + b : Nat) : Int) - (y : Int)) j :=
    fun j hj => by
      rw [q3 _ (by omega) (by omega)]
      exact p4 j hj
  have r6R : ∀ j, j < k + 1 → s6 (a + k + j) = lmb ((rv * 2 + b - g * y : Nat) : Int) j := fun j hj => by
    rw [u1 j hj, r5R j hj, r5T j hj, q2]
    by_cases hy' : y ≤ rv * 2 + b
    · have hg1 : g = 1 := by rw [hg]; simp [hy']
      have h0 : (0 : Int) ≤ ((rv * 2 + b : Nat) : Int) - (y : Int) := hge.mpr hy'
      simp only [h0, ite_true, hg1, Nat.one_mul]
      rw [sel_ones]
      congr 2
      omega
    · have hg0 : g = 0 := by rw [hg]; simp [hy']
      have h0 : ¬ (0 : Int) ≤ ((rv * 2 + b : Nat) : Int) - (y : Int) := fun h => hy' (hge.mp h)
      simp only [h0, ite_false, hg0, Nat.zero_mul, Nat.sub_zero]
      exact sel_zero _ _
  -- segment 7: X := 2 X + flag
  have back : ∀ i, (i < a + k) → s6 i = s i := fun i hi => by
    rw [u2 i (by omega) (Or.inl (by omega)), q3 i (by omega) (by omega), p4f i (Or.inl (by omega)),
      p3f i (Or.inl (by omega)), p2f i (by omega) (by omega) (Or.inl (by omega)), s1o i (by omega)]
  have fwd : ∀ i, ((a + 3 * k + 2 ≤ i ∧ i < a + 4 * k + 3) ∨ (a + 4 * k + 10 ≤ i ∧ i ≤ a + 4 * k + 13)) →
      s6 i = s i := fun i hi => by
    rw [u2 i (by omega) (Or.inr (by omega)), q3 i (by omega) (by omega), p4f i (by omega),
      p3f i (Or.inr (by omega)), p2f i (by omega) (by omega) (Or.inr (by omega)), s1o i (by omega)]
  have h7TB : s6 (a + 4 * k + 10 + 4) = BitVec.ofNat 64 g := by
    rw [u2 _ (by omega) (Or.inr (by omega)), q1]
    by_cases hy' : y ≤ rv * 2 + b
    · have hg1 : g = 1 := by rw [hg]; simp [hy']
      simp [hg1]
      omega
    · have hg0 : g = 0 := by rw [hg]; simp [hy']
      have h0 : ¬ (0 : Int) ≤ ((rv * 2 + b : Nat) : Int) - (y : Int) := fun h => hy' (hge.mp h)
      simp [h0, hg0]
      omega
  obtain ⟨z1, z2⟩ := shl1C_limbs a k (a + 4 * k + 10 + 1) (a + 4 * k + 10 + 2) (a + 4 * k + 10 + 4)
    (a + 4 * k + 10 + 6) (a + 4 * k + 10 + 7) (by omega) xv g hg2 s6
    (fun j hj => by rw [back (a + j) (by omega)]; exact hX j hj)
    (by rw [fwd _ (by omega), hO]; rfl) (by rw [fwd _ (by omega)]; exact hW) h7TB
  obtain ⟨s7, hs7⟩ : ∃ s7, s7 = aluRun (shl1C a k (a + 4 * k + 10 + 1) (a + 4 * k + 10 + 2)
    (a + 4 * k + 10 + 4) (a + 4 * k + 10 + 6) (a + 4 * k + 10 + 7)) s6 := ⟨_, rfl⟩
  rw [← hs7] at z1 z2
  have run : aluRun (dvStep k a (a + 4 * k + 10)) s = s7 := by
    simp only [dvStep, aluRun_append]
    rw [hs7, hs6, hs5, hs4, hs3, hs2, hs1]
  have keep : ∀ i, ((a + 3 * k + 2 ≤ i ∧ i < a + 4 * k + 3) ∨ (a + 4 * k + 10 ≤ i ∧ i ≤ a + 4 * k + 13)) →
      s7 i = s i := fun i hi => by
    rw [z2 i (by omega) (by omega) (Or.inr (by omega)), fwd i hi]
  rw [run]
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, ?_, ?_, ?_, ?_⟩
  · rw [z1 j hj, lmb_mod _ k j hj]
  · rw [z2 _ (by omega) (by omega) (Or.inr (by omega))]; exact r6R j hj
  · rw [keep _ (Or.inl (by omega))]; exact hD j hj
  · rw [keep _ (Or.inr (by omega))]; exact hZ
  · rw [keep _ (Or.inr (by omega))]; exact hO
  · rw [keep _ (Or.inr (by omega))]; exact hW
  · rw [keep _ (Or.inr (by omega))]; exact hC

end Gabbro.Stage0.Senke
