/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Shift/Bit.lean
  Subject:   The sub-limb stage of a barrel shifter: `r < 64` bits, carried across neighbouring limbs.

  Every limb becomes `fM limb r | fX (fX neighbour 1) (63 - r)` of the ORIGINAL limbs; the order of
  the sequence guarantees that the neighbour has not been rewritten when it is read.
-/
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Shift.Stages

namespace Gabbro.Stage0.Senke
open Runner.IR

theorem bitC_length (k a oM oX : Nat) (srcB : Nat → Nat) (l : List Nat) :
    (bitC k a oM oX srcB l).length = 4 * l.length := by
  simp only [bitC, seqC_length _ 4 (fun j => bitP_length _ _ _ _ _ _ _ _ _ j)]

theorem bitC_value (k a oM oX : Nat) (fM fX : Runner.W → Runner.W → Runner.W)
    (hM : aluFn oM = some fM) (hX : aluFn oX = some fX) (hM1 : oM ≠ 1) (hM2 : oM ≠ 2)
    (hX1 : oX ≠ 1) (hX2 : oX ≠ 2) (srcB : Nat → Nat) (l : List Nat) (hlk : ∀ j ∈ l, j < k)
    (hsrc : ∀ j, j < k → srcB j < a + k ∨ srcB j = a + k + 5)
    (hpw : l.Pairwise (fun j' j => j' ≠ j ∧ a + j' ≠ srcB j)) (s : Nat → Runner.W) :
    (∀ j ∈ l, aluRun (bitC k a oM oX srcB l) s (a + j) =
      fM (s (a + j)) (s (a + k + 2)) ||| fX (fX (s (srcB j)) (s (a + k + 4))) (s (a + k + 3))) ∧
    (∀ i, i ≠ a + k + 7 → i ≠ a + k + 8 → (∀ j ∈ l, i ≠ a + j) → aluRun (bitC k a oM oX srcB l) s i = s i) := by
  have hnd : l.Nodup := hpw.imp (fun h => h.1)
  have hpw' : l.Pairwise (fun j' j => ¬ (a + j' = a + j ∨ a + j' = srcB j ∨ a + j' = a + k + 2 ∨
      a + j' = a + k + 4 ∨ a + j' = a + k + 3)) :=
    hpw.imp_of_mem (fun {j' j} hj' _ h => by
      have := hlk j' hj'
      omega)
  obtain ⟨v1, v2⟩ := seqC_value
    (fun j => bitP oM oX (srcB j) (a + k + 2) (a + k + 4) (a + k + 3) (a + k + 7) (a + k + 8) a j)
    (fun j s => fM (s (a + j)) (s (a + k + 2)) ||| fX (fX (s (srcB j)) (s (a + k + 4))) (s (a + k + 3)))
    (fun j i => i = a + j ∨ i = srcB j ∨ i = a + k + 2 ∨ i = a + k + 4 ∨ i = a + k + 3)
    (fun i => i = a + k + 7 ∨ i = a + k + 8) (fun j => j < k) a
    (fun j hj s => (bitP_run oM oX fM fX hM hX hM1 hM2 hX1 hX2 (srcB j) (a + k + 2) (a + k + 4) (a + k + 3)
      (a + k + 7) (a + k + 8) a j (by omega) (by omega) (by omega) (by have := hsrc j hj; omega)
      (by omega) (by omega) (by omega) s).1)
    (fun j hj s i h1 h2 => (bitP_run oM oX fM fX hM hX hM1 hM2 hX1 hX2 (srcB j) (a + k + 2) (a + k + 4)
      (a + k + 3) (a + k + 7) (a + k + 8) a j (by omega) (by omega) (by omega)
      (by have := hsrc j hj; omega) (by omega) (by omega) (by omega) s).2 i h1
      (fun h => h2 (Or.inl h)) (fun h => h2 (Or.inr h)))
    (fun j hj s s' h => by
      beta_reduce
      rw [h (a + j) (Or.inl rfl), h (srcB j) (Or.inr (Or.inl rfl)), h (a + k + 2) (by omega),
        h (a + k + 4) (by omega), h (a + k + 3) (by omega)])
    (fun j hj i h => by
      have := hsrc j hj
      omega)
    (fun j hj => by omega) l hlk hnd hpw' s
  exact ⟨v1, fun i h1 h2 h3 => v2 i (by omega) h3⟩

end Gabbro.Stage0.Senke
