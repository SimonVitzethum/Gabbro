/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Signed/Probe.lean
  Subject:   Joint witnesses for the signed multiword division on actual code and actual memory.

  Two limbs, code at 2048, frame at `2^20`, operands in slots 8 .. 11. The first witness divides a
  negative dividend `-(2^100 + 12345)` by `2^65 + 3` (quotient and remainder both negative, across the
  limb boundary); the second is the minimum by `-1`, where the quotient `2^127` appears with the
  minimum's encoding (the result type of the model excludes this overflow).
-/
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Divide.Probe
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Signed.Final

namespace Gabbro.Stage0.Senke.SignedProbe
open Runner.IR Runner.Mem Gabbro.Stage0.Senke.DivideProbe

theorem probe_frame41 (code : List II) (words : List Nat) : FrameOK (probeMem code words) 1048576 41 :=
  ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩

theorem sdivC_length : (wideSdivC 2 8).length = 7171 := by decide +kernel

def sdivMem : Runner.Mem :=
  probeMem (wideSdivC 2 8) [18446744073709539271, 18446744004990074879, 3, 2]

def sminMem : Runner.Mem :=
  probeMem (wideSdivC 2 8) [0, 9223372036854775808, 18446744073709551615, 18446744073709551615]

theorem sdivMem_x : WordsAt sdivMem 1048576 8 (integerEncoding 2 (-1267650600228229401496703217721)) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem sdivMem_y : WordsAt sdivMem 1048576 (8 + 2) (integerEncoding 2 36893488147419103235) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem sminMem_x : WordsAt sminMem 1048576 8 (integerEncoding 2 (-170141183460469231731687303715884105728)) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem sminMem_y : WordsAt sminMem 1048576 (8 + 2) (integerEncoding 2 (-1)) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem wideSdiv_zeuge [Kern] :
    ∃ m', Star ⟨2048, 1048576⟩ sdivMem ⟨2048 + BitVec.ofNat 64 (16 * (wideSdivC 2 8).length), 1048576⟩ m' ∧
      Agree 1048576 8 41 sdivMem m' ∧ WordsAt m' 1048576 8 [18446744039349813249, 18446744073709551615] ∧
      WordsAt m' 1048576 10 [103079202756, 18446744073709551614] := by
  have far : CodeFar 2048 (wideSdivC 2 8).length 1048576 41 := by
    rw [sdivC_length]; unfold CodeFar; decide
  obtain ⟨m', run, agree, quot, rem⟩ := wideSdiv_run (m := sdivMem) (pc := 2048) (fp := 1048576) (K := 41)
    (k := 2) (a := 8) (probe_frame41 _ _) (by decide) (by decide) (by decide)
    (probe_code (wideSdivC 2 8) _ (by decide +kernel) (by rw [sdivC_length]; decide)) far
    (-1267650600228229401496703217721) 36893488147419103235 (by decide) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) sdivMem_x sdivMem_y
  refine ⟨m', run, agree, ?_, ?_⟩
  · have e : integerEncoding 2 ((-1267650600228229401496703217721 : Int).tdiv 36893488147419103235) =
        [18446744039349813249, 18446744073709551615] := by decide +kernel
    rw [e] at quot; exact quot
  · have e : integerEncoding 2 ((-1267650600228229401496703217721 : Int).tmod 36893488147419103235) =
        [103079202756, 18446744073709551614] := by decide +kernel
    rw [e] at rem; exact rem

theorem wideSdiv_min_zeuge [Kern] :
    ∃ m', Star ⟨2048, 1048576⟩ sminMem ⟨2048 + BitVec.ofNat 64 (16 * (wideSdivC 2 8).length), 1048576⟩ m' ∧
      Agree 1048576 8 41 sminMem m' ∧ WordsAt m' 1048576 8 [0, 9223372036854775808] ∧
      WordsAt m' 1048576 10 [0, 0] := by
  have far : CodeFar 2048 (wideSdivC 2 8).length 1048576 41 := by
    rw [sdivC_length]; unfold CodeFar; decide
  obtain ⟨m', run, agree, quot, rem⟩ := wideSdiv_run (m := sminMem) (pc := 2048) (fp := 1048576) (K := 41)
    (k := 2) (a := 8) (probe_frame41 _ _) (by decide) (by decide) (by decide)
    (probe_code (wideSdivC 2 8) _ (by decide +kernel) (by rw [sdivC_length]; decide)) far
    (-170141183460469231731687303715884105728) (-1) (by decide) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) sminMem_x sminMem_y
  refine ⟨m', run, agree, ?_, ?_⟩
  · have e : integerEncoding 2 ((-170141183460469231731687303715884105728 : Int).tdiv (-1)) =
        [0, 9223372036854775808] := by decide +kernel
    rw [e] at quot; exact quot
  · have e : integerEncoding 2 ((-170141183460469231731687303715884105728 : Int).tmod (-1)) = [0, 0] := by
      decide +kernel
    rw [e] at rem; exact rem

end Gabbro.Stage0.Senke.SignedProbe
