/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Shift/Stages.lean
  Subject:   The limb stages of a barrel shifter, abstract in the direction.

  Stage `idx` moves the limbs by `c = 2^idx` positions when bit `idx` of `q` is set. A direction is a
  source-slot function `src c j` and a value function `phi m` (the operand after a limb shift by
  `m`) with `phi (m + c)` read from the limbs of `phi m` through `src c`. After `S` stages the limbs
  are those of `phi (q mod 2^S)`; for `q < 2^S` the limb count is realised exactly.
-/
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Shift.Stage

namespace Gabbro.Stage0.Senke
open Runner.IR

theorem stagesC_length (k a : Nat) (src : Nat → Nat → Nat) (l : List Nat) (S : Nat) :
    (stagesC k a src l S).length = S * (4 + 3 * l.length) := by
  induction S with
  | zero => simp [stagesC]
  | succ S ih => simp only [stagesC, List.length_append, ih, stgC_length, Nat.succ_mul]

theorem mod_two_pow_succ (q S : Nat) :
    q % 2 ^ (S + 1) = q % 2 ^ S + 2 ^ S * (if q.testBit S = true then 1 else 0) := by
  rw [Nat.mod_pow_succ]
  congr 2
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have := Nat.mod_two_eq_zero_or_one (q / 2 ^ S)
  by_cases h : q / 2 ^ S % 2 = 1 <;> simp [h]
  omega

theorem stagesC_value (k a q : Nat) (hq : q < 2 ^ 64) (src : Nat → Nat → Nat) (l : List Nat)
    (phi : Nat → Nat) (hl : ∀ j, j < k → j ∈ l) (hlk : ∀ j ∈ l, j < k)
    (hsrc : ∀ c j, j < k → src c j < a + k ∨ src c j = a + k + 5)
    (hpw : ∀ c, 1 ≤ c → l.Pairwise (fun j' j => j' ≠ j ∧ a + j' ≠ src c j))
    (hlim : ∀ m c (s : Nat → Runner.W), 1 ≤ c → s (a + k + 5) = 0 →
      (∀ j, j < k → s (a + j) = lmb (phi m : Int) j) →
      ∀ j, j < k → s (src c j) = lmb (phi (m + c) : Int) j)
    (s : Nat → Runner.W) (hQ : s (a + k + 1) = BitVec.ofNat 64 q) (hO : s (a + k + 4) = 1)
    (hZ : s (a + k + 5) = 0) (hlimbs : ∀ j, j < k → s (a + j) = lmb (phi 0 : Int) j) :
    ∀ S, S ≤ 63 →
    (∀ j, j < k → aluRun (stagesC k a src l S) s (a + j) = lmb (phi (q % 2 ^ S) : Int) j) ∧
    (∀ i, i ≠ a + k + 9 → i ≠ a + k + 7 → i ≠ a + k + 6 → (i < a ∨ a + k ≤ i) →
      aluRun (stagesC k a src l S) s i = s i)
  | 0, _ => ⟨fun j hj => by
      simp only [stagesC, aluRun_nil, Nat.pow_zero, Nat.mod_one]
      exact hlimbs j hj, fun i _ _ _ _ => rfl⟩
  | S + 1, hS => by
    obtain ⟨ih1, ih2⟩ := stagesC_value k a q hq src l phi hl hlk hsrc hpw hlim s hQ hO hZ hlimbs S (by omega)
    set s' := aluRun (stagesC k a src l S) s with hs'
    obtain ⟨v1, v2⟩ := stgC_value k a S q (by omega) hq (src (2 ^ S)) l hlk (hsrc _) (hpw _ (Nat.one_le_two_pow))
      s' (by rw [ih2 _ (by omega) (by omega) (by omega) (by omega)]; exact hQ)
      (by rw [ih2 _ (by omega) (by omega) (by omega) (by omega)]; exact hO)
      (by rw [ih2 _ (by omega) (by omega) (by omega) (by omega)]; exact hZ)
    have run : aluRun (stagesC k a src l (S + 1)) s = aluRun (stgC k a S (src (2 ^ S)) l) s' := by
      simp only [stagesC, aluRun_append]
      rfl
    refine ⟨fun j hj => ?_, fun i h1 h2 h3 h4 => ?_⟩
    · rw [run, v1 j (hl j hj), mod_two_pow_succ]
      by_cases hb : q.testBit S = true
      · simp only [hb, ite_true, Nat.mul_one]
        exact hlim (q % 2 ^ S) (2 ^ S) s' Nat.one_le_two_pow
          (by rw [ih2 _ (by omega) (by omega) (by omega) (by omega)]; exact hZ) ih1 j hj
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
        exact ih1 j hj
    · rw [run, v2 i h1 h2 h3 (fun j hj => by have := hlk j hj; omega)]
      exact ih2 i h1 h2 h3 h4

end Gabbro.Stage0.Senke
