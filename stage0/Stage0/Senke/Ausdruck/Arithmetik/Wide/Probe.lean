/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Probe.lean
  Subject:   Joint witnesses for the multiword carry chain on actual code and actual memory.

  Code at 2048 (the real emitted instructions, as bytes), the frame at 4096 with 24 slots and the
  operands in slots 8 .. 11. `wideAdd_zeuge` carries `2^64 - 1 + 1` across the limb boundary;
  `wideSub_zeuge` borrows across it for `0 - 1`.
-/
module
public import Stage0.Senke.Images.BildLese
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Run
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.CompareRun
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.MulRun
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Bits
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Neg
@[expose] public section


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

/-! ## Comparisons across the limb boundary -/

abbrev ltCode : List II := wideLtC 1 8
abbrev eqCode : List II := wideEqC 1 8

theorem ltCode_length : ltCode.length = 18 := by decide
theorem eqCode_length : eqCode.length = 19 := by decide

/-- `2^64 - 1 < 2^64`: operands `[2^64-1, 0]` and `[0, 1]`. -/
def ltMem : Runner.Mem := probeMem ltCode [18446744073709551615, 0, 0, 1]
/-- `2^64 = 0` differs only in the high limb. -/
def eqMemDiff : Runner.Mem := probeMem eqCode [0, 1, 0, 0]
/-- `2^64 + 7 = 2^64 + 7`. -/
def eqMemSame : Runner.Mem := probeMem eqCode [7, 1, 7, 1]

theorem ltMem_x : WordsAt ltMem 4096 8 (integerEncoding 2 18446744073709551615) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem ltMem_y : WordsAt ltMem 4096 (8 + 2) (integerEncoding 2 18446744073709551616) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem eqMemDiff_x : WordsAt eqMemDiff 4096 8 (integerEncoding 2 18446744073709551616) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem eqMemDiff_y : WordsAt eqMemDiff 4096 (8 + 2) (integerEncoding 2 0) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem eqMemSame_x : WordsAt eqMemSame 4096 8 (integerEncoding 2 18446744073709551623) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem eqMemSame_y : WordsAt eqMemSame 4096 (8 + 2) (integerEncoding 2 18446744073709551623) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem wideLt_zeuge [Kern] :
    ∃ m', Star ⟨2048, 4096⟩ ltMem ⟨2048 + BitVec.ofNat 64 (16 * 18), 4096⟩ m' ∧
      Agree 4096 8 24 ltMem m' ∧ m'.rd64 (slot 4096 (BitVec.ofNat 64 8)) = some 1 := by
  have far : CodeFar 2048 ltCode.length 4096 24 := by rw [ltCode_length]; unfold CodeFar; decide
  obtain ⟨m', run, agree, flag⟩ := wideLt_run (m := ltMem) (pc := 2048) (fp := 4096) (K := 24) (n := 1) (a := 8)
    (probe_frame _ _) (by decide) (by decide) (probe_code ltCode _ (by decide) (by decide)) far
    18446744073709551615 18446744073709551616 ltMem_x ltMem_y (by decide) (by decide)
  rw [ltCode_length] at run
  exact ⟨m', run, agree, by rw [flag]; decide⟩

theorem wideEq_diff_zeuge [Kern] :
    ∃ m', Star ⟨2048, 4096⟩ eqMemDiff ⟨2048 + BitVec.ofNat 64 (16 * 19), 4096⟩ m' ∧
      Agree 4096 8 24 eqMemDiff m' ∧ m'.rd64 (slot 4096 (BitVec.ofNat 64 8)) = some 0 := by
  have far : CodeFar 2048 eqCode.length 4096 24 := by rw [eqCode_length]; unfold CodeFar; decide
  obtain ⟨m', run, agree, flag⟩ := wideEq_run (m := eqMemDiff) (pc := 2048) (fp := 4096) (K := 24) (n := 1) (a := 8)
    (probe_frame _ _) (by decide) (by decide) (probe_code eqCode _ (by decide) (by decide)) far
    18446744073709551616 0 eqMemDiff_x eqMemDiff_y (by decide) (by decide)
  rw [eqCode_length] at run
  exact ⟨m', run, agree, by rw [flag]; decide⟩

theorem wideEq_same_zeuge [Kern] :
    ∃ m', Star ⟨2048, 4096⟩ eqMemSame ⟨2048 + BitVec.ofNat 64 (16 * 19), 4096⟩ m' ∧
      Agree 4096 8 24 eqMemSame m' ∧ m'.rd64 (slot 4096 (BitVec.ofNat 64 8)) = some 1 := by
  have far : CodeFar 2048 eqCode.length 4096 24 := by rw [eqCode_length]; unfold CodeFar; decide
  obtain ⟨m', run, agree, flag⟩ := wideEq_run (m := eqMemSame) (pc := 2048) (fp := 4096) (K := 24) (n := 1) (a := 8)
    (probe_frame _ _) (by decide) (by decide) (probe_code eqCode _ (by decide) (by decide)) far
    18446744073709551623 18446744073709551623 eqMemSame_x eqMemSame_y (by decide) (by decide)
  rw [eqCode_length] at run
  exact ⟨m', run, agree, by rw [flag]; decide⟩

/-! ## The 64 x 64 -> 128 bit product -/

abbrev mulCode : List II := wideMulC 2 8

theorem mulCode_length : mulCode.length = 99 := by decide

theorem probe_frame32 (code : List II) (words : List Nat) : FrameOK (probeMem code words) 4096 32 :=
  ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩

/-- `(2^64 - 1) * (2^64 - 1) = 2^128 - 2^65 + 1`: operands `[2^64-1, 0]` twice. -/
def mulMem : Runner.Mem := probeMem mulCode [18446744073709551615, 0, 18446744073709551615, 0]

theorem mulMem_x : WordsAt mulMem 4096 8 (integerEncoding 2 18446744073709551615) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem mulMem_y : WordsAt mulMem 4096 (8 + 2) (integerEncoding 2 18446744073709551615) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem wideMul_zeuge [Kern] :
    ∃ m', Star ⟨2048, 4096⟩ mulMem ⟨2048 + BitVec.ofNat 64 (16 * 99), 4096⟩ m' ∧
      Agree 4096 8 32 mulMem m' ∧ WordsAt m' 4096 8 [1, 18446744073709551614] ∧
      WordsAt m' 4096 10 [18446744073709551615, 0] := by
  have far : CodeFar 2048 mulCode.length 4096 32 := by rw [mulCode_length]; unfold CodeFar; decide
  obtain ⟨m', run, agree, prod, keep⟩ := wideMul_run (m := mulMem) (pc := 2048) (fp := 4096) (K := 32) (k := 2) (a := 8)
    (probe_frame32 _ _) (by decide) (by decide) (probe_code mulCode _ (by decide) (by decide)) far
    18446744073709551615 18446744073709551615 mulMem_x mulMem_y
  rw [mulCode_length] at run
  refine ⟨m', run, agree, ?_, ?_⟩
  · have e : integerEncoding 2 (18446744073709551615 * 18446744073709551615) =
        [1, 18446744073709551614] := by decide +kernel
    rw [e] at prod; exact prod
  · have e : integerEncoding 2 18446744073709551615 = [18446744073709551615, 0] := by decide +kernel
    rw [e] at keep; exact keep

/-! ## Bitwise and negation -/

abbrev andCode : List II := wideBitC 8 2 8
abbrev negCode : List II := wideNegC 2 8

theorem andCode_length : andCode.length = 2 := by decide
theorem negCode_length : negCode.length = 20 := by decide

/-- `(2^64 + 255) & (2^64 + 15)`: both limbs take part. -/
def andMem : Runner.Mem := probeMem andCode [255, 1, 15, 1]
/-- `-(2^64 + 1)`. -/
def negMem : Runner.Mem := probeMem negCode [1, 1, 0, 0]

theorem andMem_x : WordsAt andMem 4096 8 (integerEncoding 2 ((18446744073709551871 : Nat) : Int)) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem andMem_y : WordsAt andMem 4096 (8 + 2) (integerEncoding 2 ((18446744073709551631 : Nat) : Int)) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem negMem_x : WordsAt negMem 4096 8 (integerEncoding 2 18446744073709551617) := by
  intro i hi
  have : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> (clear this; revert hi; decide +kernel)

theorem wideAnd_zeuge [Kern] :
    ∃ m', Star ⟨2048, 4096⟩ andMem ⟨2048 + BitVec.ofNat 64 (16 * 2), 4096⟩ m' ∧
      Agree 4096 8 24 andMem m' ∧ WordsAt m' 4096 8 [15, 1] := by
  have far : CodeFar 2048 andCode.length 4096 24 := by rw [andCode_length]; unfold CodeFar; decide
  obtain ⟨m', run, agree, res, _⟩ := wideAnd_run (m := andMem) (pc := 2048) (fp := 4096) (K := 24) (k := 2) (a := 8)
    (probe_frame _ _) (by decide) (by decide) (probe_code andCode _ (by decide) (by decide)) far
    18446744073709551871 18446744073709551631 andMem_x andMem_y
  rw [andCode_length] at run
  refine ⟨m', run, agree, ?_⟩
  have e : integerEncoding 2 ((18446744073709551871 &&& 18446744073709551631 : Nat) : Int) = [15, 1] := by
    decide +kernel
  rw [e] at res; exact res

theorem wideNeg_zeuge [Kern] :
    ∃ m', Star ⟨2048, 4096⟩ negMem ⟨2048 + BitVec.ofNat 64 (16 * 20), 4096⟩ m' ∧
      Agree 4096 8 24 negMem m' ∧
      WordsAt m' 4096 8 [18446744073709551615, 18446744073709551614] := by
  have far : CodeFar 2048 negCode.length 4096 24 := by rw [negCode_length]; unfold CodeFar; decide
  obtain ⟨m', run, agree, res⟩ := wideNeg_run (m := negMem) (pc := 2048) (fp := 4096) (K := 24) (k := 2) (a := 8)
    (probe_frame _ _) (by decide) (by decide) (probe_code negCode _ (by decide) (by decide)) far
    18446744073709551617 negMem_x
  rw [negCode_length] at run
  refine ⟨m', run, agree, ?_⟩
  have e : integerEncoding 2 (-18446744073709551617) =
      [18446744073709551615, 18446744073709551614] := by decide +kernel
  rw [e] at res; exact res

end Gabbro.Stage0.Senke.WideProbe
