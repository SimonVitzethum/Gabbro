/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Signed/Value.lean
  Subject:   `wideSdivC` computes `Int.tdiv` and `Int.tmod` on canonical limbs.
-/
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Signed.Run

namespace Gabbro.Stage0.Senke
open Runner.IR

theorem abs_cond (x : Int) : (if (if x < 0 then 1 else 0) = 1 then -x else x) = ((x.natAbs : Nat) : Int) := by
  by_cases h : x < 0
  · have e : (if x < 0 then 1 else 0 : Nat) = 1 := by simp [h]
    rw [e]
    simp only [↓reduceIte]
    omega
  · have e : (if x < 0 then 1 else 0 : Nat) = 0 := by simp [h]
    rw [e]
    simp only [Nat.zero_ne_one, ↓reduceIte]
    omega

theorem sgn_q (iff' : Prop) [Decidable iff'] (q : Int) :
    (if (if iff' then 0 else 1 : Nat) = 1 then -q else q) = if iff' then q else -q := by
  by_cases h : iff' <;> simp [h]

theorem sgn_r (neg : Prop) [Decidable neg] (q : Int) :
    (if (if neg then 1 else 0 : Nat) = 1 then -q else q) = if neg then -q else q := by
  by_cases h : neg <;> simp [h]

theorem xor_flags (x y : Int) :
    BitVec.ofNat 64 (if x < 0 then 1 else 0) ^^^ BitVec.ofNat 64 (if y < 0 then 1 else 0) =
      BitVec.ofNat 64 (if (x < 0 ↔ y < 0) then 0 else 1) := by
  by_cases hx : x < 0 <;> by_cases hy : y < 0 <;> simp [hx, hy]

theorem wideSdiv_value (k a : Nat) (hk : 1 ≤ k) (x y : Int) (hy0 : y ≠ 0)
    (hx1 : -(2 ^ 63 * 2 ^ (64 * (k - 1))) ≤ x) (hx2 : x < 2 ^ 63 * 2 ^ (64 * (k - 1)))
    (hy1 : -(2 ^ 63 * 2 ^ (64 * (k - 1))) ≤ y) (hy2 : y < 2 ^ 63 * 2 ^ (64 * (k - 1)))
    (s : Nat → Runner.W) (hA : ∀ j, j < k → s (a + j) = lmb x j) (hB : ∀ j, j < k → s (a + k + j) = lmb y j) :
    (∀ j, j < k → aluRun (wideSdivC k a) s (a + j) = lmb (x.tdiv y) j) ∧
    (∀ j, j < k → aluRun (wideSdivC k a) s (a + k + j) = lmb (x.tmod y) j) := by
  obtain ⟨ua, hua⟩ : ∃ ua, ua = x.natAbs := ⟨_, rfl⟩
  obtain ⟨ub, hub⟩ : ∃ ub, ub = y.natAbs := ⟨_, rfl⟩
  have hub0 : 0 < ub := by omega
  have hP : (2 : Nat) ^ (64 * k) = 2 ^ 64 * 2 ^ (64 * (k - 1)) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hPI : (((2 : Nat) ^ (64 * (k - 1)) : Nat) : Int) = (2 : Int) ^ (64 * (k - 1)) := by
    push_cast; rfl
  have hPpos : 0 < (2 : Nat) ^ (64 * (k - 1)) := by positivity
  have hua_lt : ua < 2 ^ (64 * k) := by rw [hP]; omega
  have hub_lt : ub < 2 ^ (64 * k) := by rw [hP]; omega
  -- the signs
  obtain ⟨g1, g2, g3, g4⟩ := sdSign_run k a hk s x y hx1 hx2 hy1 hy2 (hA (k - 1) (by omega))
    (hB (k - 1) (by omega))
  obtain ⟨s1, hs1⟩ : ∃ s1, s1 = aluRun (sdSign k a) s := ⟨_, rfl⟩
  rw [← hs1] at g1 g2 g3 g4
  have fl : ∀ b : Prop, ∀ [Decidable b], (if b then 1 else 0 : Nat) < 2 := fun b _ => by split <;> omega
  -- magnitude of the dividend
  obtain ⟨b1, b2⟩ := condNeg_value k a (a + 2 * k) (a + 4 * k + 18) (a + 4 * k + 18 + 3) (a + 4 * k + 18 + 4)
    (a + 4 * k + 18 + 5) (by omega) s1 x (if x < 0 then 1 else 0) (fl _)
    (fun j hj => by rw [g4 _ (by omega) (by omega) (by omega) (by omega)]; exact hA j hj) g1 g3
  obtain ⟨s2, hs2⟩ : ∃ s2, s2 = aluRun (condNegC k a (a + 2 * k) (a + 4 * k + 18) (a + 4 * k + 18 + 3)
    (a + 4 * k + 18 + 4) (a + 4 * k + 18 + 5)) s1 := ⟨_, rfl⟩
  rw [← hs2] at b1 b2
  rw [abs_cond, ← hua] at b1
  -- magnitude of the divisor
  obtain ⟨c1, c2⟩ := condNeg_value k (a + k) (a + 2 * k) (a + 4 * k + 18 + 1) (a + 4 * k + 18 + 3)
    (a + 4 * k + 18 + 4) (a + 4 * k + 18 + 5) (by omega) s2 y (if y < 0 then 1 else 0) (fl _)
    (fun j hj => by
      rw [b2 _ (by omega) (by omega) (Or.inr (by omega)) (Or.inl (by omega)),
        g4 _ (by omega) (by omega) (by omega) (by omega)]
      exact hB j hj)
    (by rw [b2 _ (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))]; exact g2)
    (by rw [b2 _ (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))]; exact g3)
  obtain ⟨s3, hs3⟩ : ∃ s3, s3 = aluRun (condNegC k (a + k) (a + 2 * k) (a + 4 * k + 18 + 1)
    (a + 4 * k + 18 + 3) (a + 4 * k + 18 + 4) (a + 4 * k + 18 + 5)) s2 := ⟨_, rfl⟩
  rw [← hs3] at c1 c2
  rw [abs_cond, ← hub] at c1
  -- the quotient flag
  have e4 : ∀ i, aluRun [cn 10 (a + 4 * k + 18 + 6) (a + 4 * k + 18) (a + 4 * k + 18 + 1)] s3 i =
      if i = a + 4 * k + 18 + 6 then s3 (a + 4 * k + 18) ^^^ s3 (a + 4 * k + 18 + 1) else s3 i := fun i => by
    simp only [aluRun_cons, aluRun_nil, aluStep_xor, slotUpd]
  obtain ⟨s4, hs4⟩ : ∃ s4, s4 = aluRun [cn 10 (a + 4 * k + 18 + 6) (a + 4 * k + 18) (a + 4 * k + 18 + 1)] s3 :=
    ⟨_, rfl⟩
  have s3F : s3 (a + 4 * k + 18) = BitVec.ofNat 64 (if x < 0 then 1 else 0) := by
    rw [c2 _ (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)),
      b2 _ (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))]
    exact g1
  have s3F1 : s3 (a + 4 * k + 18 + 1) = BitVec.ofNat 64 (if y < 0 then 1 else 0) := by
    rw [c2 _ (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)),
      b2 _ (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))]
    exact g2
  have s3Z : s3 (a + 4 * k + 18 + 5) = 0 := by
    rw [c2 _ (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)),
      b2 _ (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))]
    exact g3
  have s4Q : s4 (a + 4 * k + 18 + 6) = BitVec.ofNat 64 (if (x < 0 ↔ y < 0) then 0 else 1) := by
    rw [hs4, e4]; simp only [↓reduceIte]
    rw [s3F, s3F1]; exact xor_flags x y
  have s4o : ∀ i, i ≠ a + 4 * k + 18 + 6 → s4 i = s3 i := fun i hi => by rw [hs4, e4]; simp [hi]
  -- the unsigned division of the magnitudes
  obtain ⟨q1, r1⟩ := wideDiv_value k a ua ub hk hub0 hub_lt hua_lt s4
    (fun j hj => by
      rw [s4o _ (by omega), c2 _ (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega))]
      exact b1 j hj)
    (fun j hj => by rw [s4o _ (by omega)]; exact c1 j hj)
  obtain ⟨s5, hs5⟩ : ∃ s5, s5 = aluRun (wideDivC k a) s4 := ⟨_, rfl⟩
  rw [← hs5] at q1 r1
  have fr5 : ∀ i, (i < a ∨ a + 4 * k + 18 ≤ i) → s5 i = s4 i := fun i hi => by
    have hA' := wideDivC_aluIns (K := a + 4 * k + 18) k a hk (Nat.le_refl _)
    rw [hs5]
    rcases hi with hi | hi
    · exact aluRun_low hA' s4 hi
    · exact aluRun_high hA' s4 hi
  -- the quotient sign
  obtain ⟨d1, d2⟩ := condNeg_value k a (a + 2 * k) (a + 4 * k + 18 + 6) (a + 4 * k + 18 + 3)
    (a + 4 * k + 18 + 4) (a + 4 * k + 18 + 5) (by omega) s5 ((ua / ub : Nat) : Int)
    (if (x < 0 ↔ y < 0) then 0 else 1) (by split <;> omega) q1
    (by rw [fr5 _ (Or.inr (by omega))]; exact s4Q)
    (by rw [fr5 _ (Or.inr (by omega)), s4o _ (by omega)]; exact s3Z)
  obtain ⟨s6, hs6⟩ : ∃ s6, s6 = aluRun (condNegC k a (a + 2 * k) (a + 4 * k + 18 + 6) (a + 4 * k + 18 + 3)
    (a + 4 * k + 18 + 4) (a + 4 * k + 18 + 5)) s5 := ⟨_, rfl⟩
  rw [← hs6] at d1 d2
  -- the remainder sign
  obtain ⟨e1, e2⟩ := condNeg_value k (a + k) (a + 2 * k) (a + 4 * k + 18) (a + 4 * k + 18 + 3)
    (a + 4 * k + 18 + 4) (a + 4 * k + 18 + 5) (by omega) s6 ((ua % ub : Nat) : Int)
    (if x < 0 then 1 else 0) (by split <;> omega)
    (fun j hj => by
      rw [d2 _ (by omega) (by omega) (Or.inr (by omega)) (Or.inl (by omega))]
      exact r1 j hj)
    (by rw [d2 _ (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)),
        fr5 _ (Or.inr (by omega)), s4o _ (by omega)]; exact s3F)
    (by rw [d2 _ (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)),
        fr5 _ (Or.inr (by omega)), s4o _ (by omega)]; exact s3Z)
  obtain ⟨s7, hs7⟩ : ∃ s7, s7 = aluRun (condNegC k (a + k) (a + 2 * k) (a + 4 * k + 18) (a + 4 * k + 18 + 3)
    (a + 4 * k + 18 + 4) (a + 4 * k + 18 + 5)) s6 := ⟨_, rfl⟩
  rw [← hs7] at e1 e2
  have run : aluRun (wideSdivC k a) s = s7 := by
    simp only [wideSdivC, aluRun_append]
    rw [hs7, hs6, hs5, hs4, hs3, hs2, hs1]
  rw [run]
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · rw [e2 _ (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)), d1 j hj, sgn_q, tdiv_sign, hua, hub]
  · rw [e1 j hj, sgn_r, tmod_sign, hua, hub]

end Gabbro.Stage0.Senke
