/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Divide/Probe.lean
  Subject:   Joint witness for the multiword division on actual code and actual memory.

  The unrolled division is 7050 instructions for two limbs, so the code at 2048 ends below a frame at
  `2^20` (`CodeFar`). Operands in slots 8 .. 11: the dividend `2^127 + 2^100 + 12345` and the divisor
  `2^65 + 3`; the quotient is one limb, the remainder crosses the limb boundary.
-/
module
public import Stage0.Senke.Images.BildLese
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Divide.Run
@[expose] public section


namespace Gabbro.Stage0.Senke.DivideProbe
open Runner.IR Runner.Mem

/-- One byte of the frame words, which start at slot 8 of the frame at `2^20`. -/
def frameByte (words : List Nat) (a : Runner.W) : Runner.B :=
  if 1048640 ≤ a.toNat ∧ a.toNat < 1048640 + 8 * words.length then
    BitVec.ofNat 8 (words.getD ((a.toNat - 1048640) / 8) 0 / 256 ^ ((a.toNat - 1048640) % 8))
  else 0

def probeMem (code : List II) (words : List Nat) : Runner.Mem where
  b a := if 2048 ≤ a.toNat ∧ a.toNat < 2048 + (code.flatMap encII).length then
      ((code.flatMap encII)[a.toNat - 2048]?).getD 0 else frameByte words a
  rd _ := true
  wr _ := true

theorem probe_code (code : List II) (words : List Nat)
    (ho : code.all (fun i => decide (i.o < 256)) = true) (hlen : code.length ≤ 60000) :
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

theorem probe_frame (code : List II) (words : List Nat) : FrameOK (probeMem code words) 1048576 34 :=
  ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩

theorem wideDivC_length_two : (wideDivC 2 8).length = 7050 := by decide +kernel

def divMem : Runner.Mem :=
  probeMem (wideDivC 2 8) [12345, 9223372105574252544, 3, 2]

theorem divMem_x : WordsAt divMem 1048576 8
    (integerEncoding 2 ((170141184728119831959916705212587323449 : Nat) : Int)) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem divMem_y : WordsAt divMem 1048576 (8 + 2)
    (integerEncoding 2 ((36893488147419103235 : Nat) : Int)) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem wideDiv_zeuge [Kern] :
    ∃ m', Star ⟨2048, 1048576⟩ divMem ⟨2048 + BitVec.ofNat 64 (16 * (wideDivC 2 8).length), 1048576⟩ m' ∧
      Agree 1048576 8 34 divMem m' ∧ WordsAt m' 1048576 8 [4611686052787126271, 0] ∧
      WordsAt m' 1048576 10 [4611685915348185148, 1] := by
  have far : CodeFar 2048 (wideDivC 2 8).length 1048576 34 := by
    rw [wideDivC_length_two]; unfold CodeFar; decide
  obtain ⟨m', run, agree, quot, rem⟩ := wideDiv_run (m := divMem) (pc := 2048) (fp := 1048576) (K := 34)
    (k := 2) (a := 8) (probe_frame _ _) (by decide) (by decide) (by decide)
    (probe_code (wideDivC 2 8) _ (by decide +kernel) (by rw [wideDivC_length_two]; decide)) far
    170141184728119831959916705212587323449 36893488147419103235 (by decide) (by decide) (by decide)
    divMem_x divMem_y
  refine ⟨m', run, agree, ?_, ?_⟩
  · have e : integerEncoding 2 (((170141184728119831959916705212587323449 / 36893488147419103235 : Nat)) : Int) =
        [4611686052787126271, 0] := by decide +kernel
    rw [e] at quot; exact quot
  · have e : integerEncoding 2 (((170141184728119831959916705212587323449 % 36893488147419103235 : Nat)) : Int) =
        [4611685915348185148, 1] := by decide +kernel
    rw [e] at rem; exact rem

end Gabbro.Stage0.Senke.DivideProbe
