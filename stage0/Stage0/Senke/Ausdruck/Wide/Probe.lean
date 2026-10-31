/-
  File:      stage0/Stage0/Senke/Ausdruck/Wide/Probe.lean
  Subject:   Joint witnesses for the multiword carry chain on actual code and actual memory.

  Code at 2048 (the real emitted instructions, as bytes), the frame at 4096 with 24 slots and the
  operands in slots 8 .. 11. `wideAdd_zeuge` carries `2^64 - 1 + 1` across the limb boundary;
  `wideSub_zeuge` borrows across it for `0 - 1`.
-/
import Stage0.Senke.BildLese
import Stage0.Senke.Ausdruck.Wide.Run

namespace Gabbro.Stage0.Senke.WideProbe
open Runner.IR Runner.Mem

/-- One byte of the frame words, which start at slot 8. -/
def frameByte (words : List Nat) (a : Runner.W) : Runner.B :=
  if 4160 ≤ a.toNat ∧ a.toNat < 4160 + 8 * words.length then
    BitVec.ofNat 8 (words.getD ((a.toNat - 4160) / 8) 0 / 256 ^ ((a.toNat - 4160) % 8))
  else 0

def probeMem (code : List II) (words : List Nat) : Runner.Mem where
  b a := if 2048 ≤ a.toNat ∧ a.toNat < 2048 + (code.flatMap encII).length then
      ((code.flatMap encII)[a.toNat - 2048]?).getD 0 else frameByte words a
  rd _ := true
  wr _ := true

theorem probe_code (code : List II) (words : List Nat)
    (ho : code.all (fun i => decide (i.o < 256)) = true) (hlen : code.length ≤ 1024) :
    CodeAt (probeMem code words) 2048 code := by
  apply codeAt_bytes code 2048 ho
  intro i hi
  have size := flatMap_enc_len code
  have bound : 2048 + i < 2 ^ 64 := by omega
  have address : (BitVec.ofNat 64 (2048 + i)).toNat = 2048 + i := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  refine ⟨rfl, rfl, ?_⟩
  have low : 2048 ≤ 2048 + i := by omega
  have upper : 2048 + i < 2048 + (code.flatMap encII).length := by omega
  change (probeMem code words).b (BitVec.ofNat 64 (2048 + i)) = (code.flatMap encII)[i]
  show (if 2048 ≤ (BitVec.ofNat 64 (2048 + i)).toNat ∧
      (BitVec.ofNat 64 (2048 + i)).toNat < 2048 + (code.flatMap encII).length then
        ((code.flatMap encII)[(BitVec.ofNat 64 (2048 + i)).toNat - 2048]?).getD 0
      else frameByte words (BitVec.ofNat 64 (2048 + i))) = _
  rw [address, if_pos ⟨low, upper⟩, Nat.add_sub_cancel_left, List.getElem?_eq_getElem hi]
  rfl

theorem probe_frame (code : List II) (words : List Nat) : FrameOK (probeMem code words) 4096 24 :=
  ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩

abbrev addCode : List II := wideAddC 2 8 0 0
abbrev subCode : List II := wideAddC 2 8 (-1) 1

theorem addCode_length : addCode.length = 16 := by decide
theorem subCode_length : subCode.length = 16 := by decide

/-- `(2^64 - 1) + 1` over two limbs: operands `[2^64-1, 0]` and `[1, 0]`. -/
def addMem : Runner.Mem := probeMem addCode [18446744073709551615, 0, 1, 0]
def subMem : Runner.Mem := probeMem subCode [0, 0, 1, 0]

theorem addMem_x : WordsAt addMem 4096 8 (integerEncoding 2 18446744073709551615) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem addMem_y : WordsAt addMem 4096 (8 + 2) (integerEncoding 2 1) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem subMem_x : WordsAt subMem 4096 8 (integerEncoding 2 0) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem subMem_y : WordsAt subMem 4096 (8 + 2) (integerEncoding 2 1) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem wideAdd_zeuge [Kern] :
    ∃ m', Star ⟨2048, 4096⟩ addMem ⟨2048 + BitVec.ofNat 64 (16 * 16), 4096⟩ m' ∧
      Agree 4096 8 24 addMem m' ∧ WordsAt m' 4096 8 [0, 1] ∧ WordsAt m' 4096 10 [1, 0] := by
  have far : CodeFar 2048 addCode.length 4096 24 := by rw [addCode_length]; unfold CodeFar; decide
  obtain ⟨m', run, agree, sum, keep⟩ := wideAdd_run (m := addMem) (pc := 2048) (fp := 4096) (K := 24) (k := 2) (a := 8)
    (probe_frame _ _) (by decide) (by decide) (probe_code addCode _ (by decide) (by decide)) far
    18446744073709551615 1 addMem_x addMem_y
  rw [addCode_length] at run
  refine ⟨m', run, agree, ?_, ?_⟩
  · have e : integerEncoding 2 (18446744073709551615 + 1) = [0, 1] := by decide +kernel
    rw [e] at sum; exact sum
  · have e : integerEncoding 2 1 = [1, 0] := by decide +kernel
    rw [e] at keep; exact keep

theorem wideSub_zeuge [Kern] :
    ∃ m', Star ⟨2048, 4096⟩ subMem ⟨2048 + BitVec.ofNat 64 (16 * 16), 4096⟩ m' ∧
      Agree 4096 8 24 subMem m' ∧
      WordsAt m' 4096 8 [18446744073709551615, 18446744073709551615] ∧ WordsAt m' 4096 10 [1, 0] := by
  have far : CodeFar 2048 subCode.length 4096 24 := by rw [subCode_length]; unfold CodeFar; decide
  obtain ⟨m', run, agree, diff, keep⟩ := wideSub_run (m := subMem) (pc := 2048) (fp := 4096) (K := 24) (k := 2) (a := 8)
    (probe_frame _ _) (by decide) (by decide) (probe_code subCode _ (by decide) (by decide)) far
    0 1 subMem_x subMem_y
  rw [subCode_length] at run
  refine ⟨m', run, agree, ?_, ?_⟩
  · have e : integerEncoding 2 (0 - 1) =
        [18446744073709551615, 18446744073709551615] := by decide +kernel
    rw [e] at diff; exact diff
  · have e : integerEncoding 2 1 = [1, 0] := by decide +kernel
    rw [e] at keep; exact keep

end Gabbro.Stage0.Senke.WideProbe
