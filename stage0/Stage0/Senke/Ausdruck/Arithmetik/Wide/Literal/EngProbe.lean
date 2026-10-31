/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Literal/EngProbe.lean
  Subject:   Joint witnesses for the multiword narrowing test on actual code and actual memory.

  Two limbs, bounds `[-2^100, 2^100]` (both limbs of both bounds are materialized with the digit path),
  code at 2048 and frame at `2^20`, operand in slots 8 and 9. `-2^100 - 1` is one below the lower bound
  (the borrow crosses the limb boundary): flag 1. `2^100` is the upper bound itself: flag 0.
-/
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Divide.Probe
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Literal.Eng

namespace Gabbro.Stage0.Senke.EngProbe
open Runner.IR Runner.Mem Gabbro.Stage0.Senke.DivideProbe

theorem probe_frame48 (code : List II) (words : List Nat) : FrameOK (probeMem code words) 1048576 48 :=
  ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩

theorem outC_length : (wideOutC 2 8 (-(2 ^ 100)) (2 ^ 100)).length = 131 := by decide +kernel

def lowMem : Runner.Mem :=
  probeMem (wideOutC 2 8 (-(2 ^ 100)) (2 ^ 100)) [18446744073709551615, 18446744004990074879]

def highMem : Runner.Mem :=
  probeMem (wideOutC 2 8 (-(2 ^ 100)) (2 ^ 100)) [0, 68719476736]

theorem lowMem_x : WordsAt lowMem 1048576 8 (integerEncoding 2 (-(2 ^ 100) - 1)) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem highMem_x : WordsAt highMem 1048576 8 (integerEncoding 2 (2 ^ 100)) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem wideOut_low_zeuge [Kern] :
    ∃ m', Star ⟨2048, 1048576⟩ lowMem
        ⟨2048 + BitVec.ofNat 64 (16 * (wideOutC 2 8 (-(2 ^ 100)) (2 ^ 100)).length), 1048576⟩ m' ∧
      Agree 1048576 8 48 lowMem m' ∧ WordsAt m' 1048576 8 [18446744073709551615, 18446744004990074879] ∧
      m'.rd64 (slot 1048576 (BitVec.ofNat 64 (8 + 2 + 3))) = some 1 := by
  have far : CodeFar 2048 (wideOutC 2 8 (-(2 ^ 100)) (2 ^ 100)).length 1048576 48 := by
    rw [outC_length]; unfold CodeFar; decide
  obtain ⟨m', run, agree, keep, flag⟩ := wideOut_run (m := lowMem) (pc := 2048) (fp := 1048576) (K := 48)
    (k := 2) (a := 8) (-(2 ^ 100)) (2 ^ 100) (-(2 ^ 100) - 1) (probe_frame48 _ _) (by decide) (by decide)
    (by decide) (probe_code (wideOutC 2 8 (-(2 ^ 100)) (2 ^ 100)) _ (by decide +kernel)
      (by rw [outC_length]; decide)) far (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) lowMem_x
  refine ⟨m', run, agree, ?_, ?_⟩
  · have e : integerEncoding 2 (-(2 ^ 100) - 1) = [18446744073709551615, 18446744004990074879] := by decide +kernel
    rw [e] at keep; exact keep
  · rw [flag]
    have : decide ((-(2 ^ 100) - 1 : Int) < -(2 ^ 100) ∨ (2 ^ 100 : Int) < -(2 ^ 100) - 1) = true := by decide
    rw [this]; rfl

theorem wideOut_high_zeuge [Kern] :
    ∃ m', Star ⟨2048, 1048576⟩ highMem
        ⟨2048 + BitVec.ofNat 64 (16 * (wideOutC 2 8 (-(2 ^ 100)) (2 ^ 100)).length), 1048576⟩ m' ∧
      Agree 1048576 8 48 highMem m' ∧ WordsAt m' 1048576 8 [0, 68719476736] ∧
      m'.rd64 (slot 1048576 (BitVec.ofNat 64 (8 + 2 + 3))) = some 0 := by
  have far : CodeFar 2048 (wideOutC 2 8 (-(2 ^ 100)) (2 ^ 100)).length 1048576 48 := by
    rw [outC_length]; unfold CodeFar; decide
  obtain ⟨m', run, agree, keep, flag⟩ := wideOut_run (m := highMem) (pc := 2048) (fp := 1048576) (K := 48)
    (k := 2) (a := 8) (-(2 ^ 100)) (2 ^ 100) (2 ^ 100) (probe_frame48 _ _) (by decide) (by decide)
    (by decide) (probe_code (wideOutC 2 8 (-(2 ^ 100)) (2 ^ 100)) _ (by decide +kernel)
      (by rw [outC_length]; decide)) far (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) highMem_x
  refine ⟨m', run, agree, ?_, ?_⟩
  · have e : integerEncoding 2 (2 ^ 100) = [0, 68719476736] := by decide +kernel
    rw [e] at keep; exact keep
  · rw [flag]
    have : decide (((2 ^ 100 : Int) < -(2 ^ 100)) ∨ ((2 ^ 100 : Int) < 2 ^ 100)) = false := by decide
    rw [this]; rfl

end Gabbro.Stage0.Senke.EngProbe
