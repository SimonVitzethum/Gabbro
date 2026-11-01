/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Literal/Word.lean
  Subject:   The shared word materializer on the slot valuation.

  `wordConstant d n` (one `const` for a 32-bit literal, else four base-65536 digits) leaves the word
  `BitVec.ofInt 64 n` in slot `d` and touches only slots `d` and `d+1`. Here that effect is stated on the
  straight-line executor, which is where the multiword kernels compose it.
-/
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Alu
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Shift.Piece
import Stage0.Senke.Ausdruck.Gleit.Wort

namespace Gabbro.Stage0.Senke
open Runner.IR

theorem ci_succ_bin (o d : Nat) : ci o d d ((d : Int) + 1) = cn o d d (d + 1) := by
  simp [cn, ci]

theorem ci_succ_const (d : Nat) (v : Int) : ci 1 ((d : Int) + 1) v 0 = ci 1 ((d + 1 : Nat) : Int) v 0 := by
  simp [ci]

theorem aluStep_add (a b c : Nat) (s : Nat → Runner.W) :
    aluStep (cn 3 a b c) s = slotUpd s a (s b + s c) :=
  aluStep_cn (f := fun a b => a + b) rfl (by decide) (by decide) s
theorem aluStep_mul (a b c : Nat) (s : Nat → Runner.W) :
    aluStep (cn 5 a b c) s = slotUpd s a (s b * s c) :=
  aluStep_cn (f := fun a b => a * b) rfl (by decide) (by decide) s

theorem konstWL_run (k : Nat) : ∀ (n d : Nat) (s : Nat → Runner.W), n < 65536 ^ k →
    aluRun (konstWL k n d).1 s d = BitVec.ofNat 64 n ∧
    ∀ i, i ≠ d → i ≠ d + 1 → aluRun (konstWL k n d).1 s i = s i := by
  induction k with
  | zero =>
    intro n d s hn
    have : n = 0 := by simpa using hn
    subst n
    simp only [konstWL, aluRun_cons, aluRun_nil, aluStep_const, slotUpd]
    refine ⟨by simp, fun i h1 h2 => by simp [h1]⟩
  | succ k ih =>
    intro n d s hn
    have hq : n / 65536 < 65536 ^ k := by rw [Nat.pow_succ] at hn; omega
    obtain ⟨i1, i2⟩ := ih (n / 65536) d s hq
    simp only [konstWL, bin2, ci_succ_bin, ci_succ_const, List.append_assoc, aluRun_append, List.cons_append,
      List.nil_append, aluRun_cons, aluRun_nil, aluStep_const, aluStep_add, aluStep_mul]
    generalize aluRun (konstWL k (n / 65536) d).1 s = s1 at i1 i2 ⊢
    refine ⟨?_, fun i h1 h2 => ?_⟩
    · simp [slotUpd, i1]
      rw [show ((n : Int) % 65536) = ((n % 65536 : Nat) : Int) by omega, BitVec.ofInt_natCast,
        ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    · simp [slotUpd, h1, h2, i2 i h1 h2]

theorem wordConstant_run (d : Nat) (n : Int) (s : Nat → Runner.W) :
    aluRun (wordConstant d n).1 s d = BitVec.ofInt 64 n ∧
    ∀ i, i ≠ d → i ≠ d + 1 → aluRun (wordConstant d n).1 s i = s i := by
  unfold wordConstant
  by_cases small : lit32 n = true
  · simp only [small, ↓reduceIte, aluRun_cons, aluRun_nil, aluStep_const, slotUpd]
    refine ⟨by simp, fun i h1 h2 => by simp [h1]⟩
  · simp only [small, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨r1, r2⟩ := konstWL_run 4 (BitVec.ofInt 64 n).toNat d s (by
      have := (BitVec.ofInt 64 n).isLt
      simpa [Nat.pow_succ] using this)
    exact ⟨by rw [r1, BitVec.ofNat_toNat, BitVec.setWidth_eq], r2⟩

end Gabbro.Stage0.Senke
