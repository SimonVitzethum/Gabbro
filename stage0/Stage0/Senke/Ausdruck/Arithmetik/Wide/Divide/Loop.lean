/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Divide/Loop.lean
  Subject:   The unrolled division loop and the setup of the registers.

  `dvLoop` is `n` copies of the step; `dvPre` moves the divisor above the remainder register, appends
  its zero limb, clears the remainder register and installs the constants. The loop never branches:
  the flag selects the difference by a mask, so the code is straight-line.
-/
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Divide.Iter

namespace Gabbro.Stage0.Senke
open Runner.IR

theorem dvLoop_value (k a c y x : Nat) (hk : 1 ≤ k) (hc : c = a + 4 * k + 10) (hy0 : 0 < y)
    (hy : y < 2 ^ (64 * k)) (hx : x < 2 ^ (64 * k)) (s : Nat → Runner.W) (hs : DvRep k a c y s x 0) :
    ∀ n, n ≤ 64 * k → DvRep k a c y (aluRun (dvLoop k a c n) s) (dvIter k y x n).1 (dvIter k y x n).2
  | 0, _ => by simpa [dvLoop, dvIter] using hs
  | n + 1, hn => by
    have ih := dvLoop_value k a c y x hk hc hy0 hy hx s hs n (by omega)
    obtain ⟨ihR, _⟩ := dvIter_spec k y x hy0 hx hk n (by omega)
    have hr : (dvIter k y x n).2 < y := by rw [ihR]; exact Nat.mod_lt _ hy0
    have := dvStep_value k a c y (dvIter k y x n).1 (dvIter k y x n).2 hk hc hy hr _ ih
    simpa only [dvLoop, aluRun_append, dvIter] using this

theorem dvPre_value (k a y x : Nat) (hy : y < 2 ^ (64 * k)) (s : Nat → Runner.W)
    (hX : ∀ j, j < k → s (a + j) = lmb (x : Int) j) (hD : ∀ j, j < k → s (a + k + j) = lmb (y : Int) j) :
    DvRep k a (a + 4 * k + 10) y (aluRun (dvPre k a) s) x 0 := by
  obtain ⟨c1, c2⟩ := copyUp_value k (a + 3 * k + 2) (a + k) s (by omega)
  obtain ⟨s1, hs1⟩ : ∃ s1, s1 = aluRun (copyWords k (a + 3 * k + 2) (a + k)) s := ⟨_, rfl⟩
  rw [← hs1] at c1 c2
  have e1 : aluRun [ci 1 (a + 4 * k + 2 : Nat) 0 0] s1 =
      slotUpd s1 (a + 4 * k + 2) (BitVec.ofInt 64 0) := by
    simp only [aluRun_cons, aluRun_nil, aluStep_const]
  obtain ⟨s2, hs2⟩ : ∃ s2, s2 = aluRun [ci 1 (a + 4 * k + 2 : Nat) 0 0] s1 := ⟨_, rfl⟩
  have s2v : ∀ i, s2 i = if i = a + 4 * k + 2 then BitVec.ofInt 64 0 else s1 i := fun i => by
    rw [hs2, e1]; rfl
  obtain ⟨z1, z2⟩ := zeroSlots_value (k + 1) (a + k) s2
  obtain ⟨s3, hs3⟩ : ∃ s3, s3 = aluRun (zeroSlotsC (k + 1) (a + k)) s2 := ⟨_, rfl⟩
  rw [← hs3] at z1 z2
  have e4 : ∀ i, aluRun [ci 1 (a + 4 * k + 10 : Nat) 0 0, ci 1 (a + 4 * k + 11 : Nat) 1 0,
      ci 1 (a + 4 * k + 12 : Nat) 62 0, ci 1 (a + 4 * k + 13 : Nat) 63 0] s3 i =
      if i = a + 4 * k + 13 then BitVec.ofInt 64 63 else if i = a + 4 * k + 12 then BitVec.ofInt 64 62
      else if i = a + 4 * k + 11 then BitVec.ofInt 64 1 else if i = a + 4 * k + 10 then BitVec.ofInt 64 0
      else s3 i := fun i => by
    simp only [aluRun_cons, aluRun_nil, aluStep_const, slotUpd]
  have run : aluRun (dvPre k a) s = aluRun [ci 1 (a + 4 * k + 10 : Nat) 0 0, ci 1 (a + 4 * k + 11 : Nat) 1 0,
      ci 1 (a + 4 * k + 12 : Nat) 62 0, ci 1 (a + 4 * k + 13 : Nat) 63 0] s3 := by
    simp only [dvPre, aluRun_append]
    rw [hs3, hs2, hs1]
  rw [run]
  have keep : ∀ i, i < a + 4 * k + 2 → i ≠ a + 4 * k + 2 → (i < a + k ∨ a + 2 * k + 1 ≤ i) →
      (i < a + 3 * k + 2 ∨ a + 4 * k + 2 ≤ i) → aluRun [ci 1 (a + 4 * k + 10 : Nat) 0 0,
      ci 1 (a + 4 * k + 11 : Nat) 1 0, ci 1 (a + 4 * k + 12 : Nat) 62 0, ci 1 (a + 4 * k + 13 : Nat) 63 0] s3 i =
      s1 i := fun i h1 h2 h3 h4 => by
    rw [e4]
    simp only [show i ≠ a + 4 * k + 13 by omega, show i ≠ a + 4 * k + 12 by omega,
      show i ≠ a + 4 * k + 11 by omega, show i ≠ a + 4 * k + 10 by omega, ↓reduceIte]
    rw [z2 i (by omega), s2v]
    simp only [h2, ↓reduceIte]
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, ?_, ?_, ?_, ?_⟩
  · rw [keep _ (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)), c2 _ (Or.inl (by omega))]
    exact hX j hj
  · rw [e4]
    simp only [show a + k + j ≠ a + 4 * k + 13 by omega, show a + k + j ≠ a + 4 * k + 12 by omega,
      show a + k + j ≠ a + 4 * k + 11 by omega, show a + k + j ≠ a + 4 * k + 10 by omega, ↓reduceIte]
    rw [z1 j hj]
    simp [lmb_zero]
  · rw [e4]
    simp only [show a + 3 * k + 2 + j ≠ a + 4 * k + 13 by omega, show a + 3 * k + 2 + j ≠ a + 4 * k + 12 by omega,
      show a + 3 * k + 2 + j ≠ a + 4 * k + 11 by omega, show a + 3 * k + 2 + j ≠ a + 4 * k + 10 by omega,
      ↓reduceIte]
    rw [z2 _ (Or.inr (by omega)), s2v]
    by_cases hjk : j < k
    · simp only [show a + 3 * k + 2 + j ≠ a + 4 * k + 2 by omega, ↓reduceIte]
      rw [c1 j hjk]
      exact hD j hjk
    · have hj' : j = k := by omega
      subst hj'
      simp only [show a + 3 * j + 2 + j = a + 4 * j + 2 by omega, ↓reduceIte]
      rw [lmb_high y j j hy (Nat.le_refl _)]
      rfl
  · rw [e4]; simp
  · rw [e4]; simp
  · rw [e4]; simp
  · rw [e4]; simp

end Gabbro.Stage0.Senke
