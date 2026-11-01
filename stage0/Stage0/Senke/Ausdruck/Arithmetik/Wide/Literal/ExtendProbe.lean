/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Literal/ExtendProbe.lean
  Subject:   Actual-memory witnesses extending two limbs to four, with negative and high unsigned inputs.
-/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Literal.Extend
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Probe
@[expose] public section


namespace Gabbro.Stage0.Senke.ExtendProbe
open Runner.IR Runner.Mem Gabbro.Stage0.Senke.WideProbe

def value (signed : Bool) : Int := if signed then -(2 ^ 100) - 1 else 2 ^ 127 + 2 ^ 64 + 1

def words (signed : Bool) : List Nat :=
  if signed then [18446744073709551615, 18446744004990074879] else [1, 9223372036854775809]

def memory (signed : Bool) : Runner.Mem := probeMem (wideExtendC signed 2 4 8) (words signed)

theorem memory_input (signed : Bool) : WordsAt (memory signed) 4096 8 (integerEncoding 2 (value signed)) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
    (clear this; revert hi; cases signed <;> decide +kernel)

/-- Both extensions cross two limb boundaries; unsigned input has its top bit set. -/
theorem wideExtend_zeuge [Kern] (signed : Bool) :
    ∃ m', Star ⟨2048, 4096⟩ (memory signed)
        ⟨2048 + BitVec.ofNat 64 (16 * (wideExtendC signed 2 4 8).length), 4096⟩ m' ∧
      Agree 4096 8 24 (memory signed) m' ∧
      WordsAt m' 4096 8 (if signed then
        [18446744073709551615, 18446744004990074879, 18446744073709551615, 18446744073709551615]
        else [1, 9223372036854775809, 0, 0]) := by
  have far : CodeFar 2048 (wideExtendC signed 2 4 8).length 4096 24 := by
    cases signed <;> unfold CodeFar <;> decide +kernel
  obtain ⟨m', run, agree, res⟩ := wideExtend_run (m := memory signed) (pc := 2048) (fp := 4096)
    (K := 24) (j := 2) (k := 4) (a := 8) signed (value signed) (by decide) (by decide)
    (by cases signed <;> norm_num [WideFits, value]) (probe_frame _ _) (by decide) (by decide)
    (probe_code (wideExtendC signed 2 4 8) _ (by cases signed <;> decide +kernel)
      (by cases signed <;> decide +kernel)) far (memory_input signed)
  refine ⟨m', run, agree, ?_⟩
  have e : integerEncoding 4 (value signed) = if signed then
      [18446744073709551615, 18446744004990074879, 18446744073709551615, 18446744073709551615]
      else [1, 9223372036854775809, 0, 0] := by cases signed <;> decide +kernel
  rw [e] at res
  exact res

end Gabbro.Stage0.Senke.ExtendProbe
