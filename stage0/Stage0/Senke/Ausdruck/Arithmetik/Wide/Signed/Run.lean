/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Signed/Run.lean
  Subject:   The signed division code, its value theorem and its admission by the executor.

  Layout for `k` limbs at slot `a`: dividend `a ..< a+k`, divisor `a+k ..< a+2k`, the unsigned
  division's scratch up to `a+4k+18`, then the sign flags (`e` dividend, `e+1` divisor, `e+6`
  quotient), the constant 63 (`e+2`), the mask (`e+3`), a temporary (`e+4`) and zero (`e+5`),
  `e = a+4k+18`. The negation scratch of the magnitudes lives at `a+2k`, inside the division's.
-/
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Signed.Sdiv

namespace Gabbro.Stage0.Senke
open Runner.IR Runner.Mem

theorem bool_flag (p : Prop) [Decidable p] :
    Runner.IR.bool (decide p) = BitVec.ofNat 64 (if p then 1 else 0) := by
  by_cases h : p <;> simp [Runner.IR.bool, h]

theorem sdSign_run (k a : Nat) (hk : 1 ≤ k) (s : Nat → Runner.W) (x y : Int)
    (hx1 : -(2 ^ 63 * 2 ^ (64 * (k - 1))) ≤ x) (hx2 : x < 2 ^ 63 * 2 ^ (64 * (k - 1)))
    (hy1 : -(2 ^ 63 * 2 ^ (64 * (k - 1))) ≤ y) (hy2 : y < 2 ^ 63 * 2 ^ (64 * (k - 1)))
    (hA : s (a + (k - 1)) = lmb x (k - 1)) (hB : s (a + k + (k - 1)) = lmb y (k - 1)) :
    aluRun (sdSign k a) s (a + 4 * k + 18) = BitVec.ofNat 64 (if x < 0 then 1 else 0) ∧
    aluRun (sdSign k a) s (a + 4 * k + 18 + 1) = BitVec.ofNat 64 (if y < 0 then 1 else 0) ∧
    aluRun (sdSign k a) s (a + 4 * k + 18 + 5) = 0 ∧
    ∀ i, i ≠ a + 4 * k + 18 → i ≠ a + 4 * k + 18 + 1 → i ≠ a + 4 * k + 18 + 2 → i ≠ a + 4 * k + 18 + 5 →
      aluRun (sdSign k a) s i = s i := by
  have h63 : (BitVec.ofInt 64 63).toNat % 64 = 63 := by decide
  have sl1 := sign_limb (k - 1) x hx1 hx2
  have sl2 := sign_limb (k - 1) y hy1 hy2
  rw [h63] at sl1 sl2
  have f1 : a + (k - 1) ≠ a + 4 * k + 18 + 5 := by omega
  have f2 : a + (k - 1) ≠ a + 4 * k + 18 + 2 := by omega
  have f3 : a + k + (k - 1) ≠ a + 4 * k + 18 := by omega
  have f4 : a + k + (k - 1) ≠ a + 4 * k + 18 + 5 := by omega
  have f5 : a + k + (k - 1) ≠ a + 4 * k + 18 + 2 := by omega
  refine ⟨?_, ?_, ?_, fun i h1 h2 h3 h4 => ?_⟩
  · simp only [sdSign, aluRun_cons, aluRun_nil, aluStep_const, aluStep_shr, slotUpd]
    simp [f1, f2, hA]
    rw [sl1, bool_flag]
  · simp only [sdSign, aluRun_cons, aluRun_nil, aluStep_const, aluStep_shr, slotUpd]
    simp [f1, f2, f3, f4, f5, hA, hB]
    rw [sl2, bool_flag]
  · simp only [sdSign, aluRun_cons, aluRun_nil, aluStep_const, aluStep_shr, slotUpd]
    simp
  · simp only [sdSign, aluRun_cons, aluRun_nil, aluStep_const, aluStep_shr, slotUpd]
    simp [h1, h2, h3, h4]

end Gabbro.Stage0.Senke
