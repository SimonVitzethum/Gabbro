/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Shift/Probe.lean
  Subject:   Joint witnesses for the multiword shifts on actual code and actual memory.

  Code at 2048 (the emitted instructions as bytes), the frame at 4096 with 24 slots, operand limbs in
  slots 8 and 9, the runtime count in slot 10. The counts 4 and 68 take the sub-limb path across the
  limb boundary and the whole-limb stage plus the sub-limb path, for both directions.
-/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Probe
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Shift.Shr
@[expose] public section


namespace Gabbro.Stage0.Senke.ShiftProbe
open Runner.IR Runner.Mem Gabbro.Stage0.Senke.WideProbe

abbrev shlCode : List II := wideShlC 2 1 8
abbrev shrCode : List II := wideShrC 2 1 8

theorem shlCode_length : shlCode.length = 25 := by decide
theorem shrCode_length : shrCode.length = 25 := by decide

/-- `[0xF000000000000001, 1] << 4`: the high bits of limb 0 enter limb 1. -/
def shl4Mem : Runner.Mem := probeMem shlCode [17293822569102704641, 1, 4]
/-- `[0xF000000000000001, 1] << 68`: limb 0 moves up and the count crosses the limb boundary. -/
def shl68Mem : Runner.Mem := probeMem shlCode [17293822569102704641, 1, 68]
/-- `[0x10, 0x1F] >> 4`. -/
def shr4Mem : Runner.Mem := probeMem shrCode [16, 31, 4]
/-- `[1, 0xF000000000000010] >> 68`. -/
def shr68Mem : Runner.Mem := probeMem shrCode [1, 17293822569102704656, 68]

theorem shl4_x : WordsAt shl4Mem 4096 8 (integerEncoding 2 ((17293822569102704641 + 2 ^ 64 : Nat) : Int)) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem shl68_x : WordsAt shl68Mem 4096 8 (integerEncoding 2 ((17293822569102704641 + 2 ^ 64 : Nat) : Int)) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem shr4_x : WordsAt shr4Mem 4096 8 (integerEncoding 2 ((16 + 31 * 2 ^ 64 : Nat) : Int)) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem shr68_x : WordsAt shr68Mem 4096 8 (integerEncoding 2 ((1 + 17293822569102704656 * 2 ^ 64 : Nat) : Int)) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem wideShl4_zeuge [Kern] :
    ∃ m', Star ⟨2048, 4096⟩ shl4Mem ⟨2048 + BitVec.ofNat 64 (16 * 25), 4096⟩ m' ∧
      Agree 4096 8 24 shl4Mem m' ∧ WordsAt m' 4096 8 [16, 31] := by
  have far : CodeFar 2048 shlCode.length 4096 24 := by rw [shlCode_length]; unfold CodeFar; decide
  obtain ⟨m', run, agree, res⟩ := wideShl_run (m := shl4Mem) (pc := 2048) (fp := 4096) (K := 24) (k := 2) (S := 1)
    (a := 8) (n := 4) (probe_frame _ _) (by decide) (by decide) (by decide) (by decide) (by decide)
    (probe_code shlCode _ (by decide) (by decide)) far (17293822569102704641 + 2 ^ 64) shl4_x (by decide +kernel)
  rw [shlCode_length] at run
  refine ⟨m', run, agree, ?_⟩
  have e : integerEncoding 2 ((((17293822569102704641 + 2 ^ 64) * 2 ^ 4 : Nat)) : Int) = [16, 31] := by decide +kernel
  rw [e] at res; exact res

theorem wideShl68_zeuge [Kern] :
    ∃ m', Star ⟨2048, 4096⟩ shl68Mem ⟨2048 + BitVec.ofNat 64 (16 * 25), 4096⟩ m' ∧
      Agree 4096 8 24 shl68Mem m' ∧ WordsAt m' 4096 8 [0, 16] := by
  have far : CodeFar 2048 shlCode.length 4096 24 := by rw [shlCode_length]; unfold CodeFar; decide
  obtain ⟨m', run, agree, res⟩ := wideShl_run (m := shl68Mem) (pc := 2048) (fp := 4096) (K := 24) (k := 2) (S := 1)
    (a := 8) (n := 68) (probe_frame _ _) (by decide) (by decide) (by decide) (by decide) (by decide)
    (probe_code shlCode _ (by decide) (by decide)) far (17293822569102704641 + 2 ^ 64) shl68_x (by decide +kernel)
  rw [shlCode_length] at run
  refine ⟨m', run, agree, ?_⟩
  have e : integerEncoding 2 ((((17293822569102704641 + 2 ^ 64) * 2 ^ 68 : Nat)) : Int) = [0, 16] := by decide +kernel
  rw [e] at res; exact res

theorem wideShr4_zeuge [Kern] :
    ∃ m', Star ⟨2048, 4096⟩ shr4Mem ⟨2048 + BitVec.ofNat 64 (16 * 25), 4096⟩ m' ∧
      Agree 4096 8 24 shr4Mem m' ∧ WordsAt m' 4096 8 [17293822569102704641, 1] := by
  have far : CodeFar 2048 shrCode.length 4096 24 := by rw [shrCode_length]; unfold CodeFar; decide
  obtain ⟨m', run, agree, res⟩ := wideShr_run (m := shr4Mem) (pc := 2048) (fp := 4096) (K := 24) (k := 2) (S := 1)
    (a := 8) (n := 4) (probe_frame _ _) (by decide) (by decide) (by decide) (by decide) (by decide)
    (probe_code shrCode _ (by decide) (by decide)) far (16 + 31 * 2 ^ 64) (by decide) shr4_x (by decide +kernel)
  rw [shrCode_length] at run
  refine ⟨m', run, agree, ?_⟩
  have e : integerEncoding 2 ((((16 + 31 * 2 ^ 64) / 2 ^ 4 : Nat)) : Int) = [17293822569102704641, 1] := by decide +kernel
  rw [e] at res; exact res

theorem wideShr68_zeuge [Kern] :
    ∃ m', Star ⟨2048, 4096⟩ shr68Mem ⟨2048 + BitVec.ofNat 64 (16 * 25), 4096⟩ m' ∧
      Agree 4096 8 24 shr68Mem m' ∧ WordsAt m' 4096 8 [1080863910568919041, 0] := by
  have far : CodeFar 2048 shrCode.length 4096 24 := by rw [shrCode_length]; unfold CodeFar; decide
  obtain ⟨m', run, agree, res⟩ := wideShr_run (m := shr68Mem) (pc := 2048) (fp := 4096) (K := 24) (k := 2) (S := 1)
    (a := 8) (n := 68) (probe_frame _ _) (by decide) (by decide) (by decide) (by decide) (by decide)
    (probe_code shrCode _ (by decide) (by decide)) far (1 + 17293822569102704656 * 2 ^ 64) (by decide) shr68_x
    (by decide +kernel)
  rw [shrCode_length] at run
  refine ⟨m', run, agree, ?_⟩
  have e : integerEncoding 2 ((((1 + 17293822569102704656 * 2 ^ 64) / 2 ^ 68 : Nat)) : Int) =
      [1080863910568919041, 0] := by decide +kernel
  rw [e] at res; exact res

end Gabbro.Stage0.Senke.ShiftProbe
