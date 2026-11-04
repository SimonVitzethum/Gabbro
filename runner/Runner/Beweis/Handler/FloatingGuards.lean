module
public import Runner.Beweis.Handler.FloatingWords
import Runner.Beweis.Handler.Sprung
@[expose] public section

namespace Runner.Beweis
open Runner.X86 Runner.Prog

/-! Exact integer guard certificates for the emitted saturation prefixes.
    Classification neither asks for arithmetic nor reads or writes memory. -/

structure FPClassified (format : FPFormat) (before after : X) : Prop where
  run : runL (fpClassify format) before = .next after
  position : after.rip = before.rip + BitVec.ofNat 64 (lenOfL (fpClassify format))
  input : after.rax = format.scalarBits before.rax
  magnitude : after.rsi = fpMagnitude format before.rax
  infinity : after.rdx = format.infinityBits
  nan : after.cf = some (fpNaN format before.rax)
  pc : after.r12 = before.r12
  frame : after.r13 = before.r13
  table : after.r14 = before.r14
  mode : after.fpReady = before.fpReady

theorem fpClassify_run (format : FPFormat) (before : X) :
    ∃ after, FPClassified format before after := by
  let registers : X := { before with
    rip := before.rip + BitVec.ofNat 64 (lenOfL (fpClassify format))
    rax := format.scalarBits before.rax
    rcx := match format with | .f32 => 31 | .f64 => 48
    rdx := format.infinityBits
    rsi := fpMagnitude format before.rax
    xmm := match format with
      | .f32 => fun slot => if slot = .xmm0 then (before.rax.setWidth 32).setWidth 128 else before.xmm slot
      | .f64 => before.xmm }
  let after : X := registers.cmpf format.infinityBits (fpMagnitude format before.rax)
  have run : runL (fpClassify format) before = .next after := by
    cases format <;>
      simp (disch := decide) [after, registers, fpClassify, fpNormalizeInput, fpSignMask, fpUpper,
        fpInfinity, FPFormat.scalarBits, FPFormat.infinityBits, FPFormat.signBit, fpMagnitude, fpLow32,
        runL, exec, X.get, X.set, X.setXmm, X.xmmWord, X.cmpf, X.nof, aluStep, aluOp,
        lenOfL, enc, regEnc, le32, BitVec.ofNat_add, BitVec.add_assoc,
        BitVec.setWidth_setWidth_of_le, sx32_ofNat]
  exact ⟨after, {
    run := run, position := rfl, input := rfl, magnitude := rfl, infinity := rfl,
    nan := rfl, pc := rfl, frame := rfl, table := rfl, mode := rfl }⟩

theorem FPClassified.code {format : FPFormat} {before after : X}
    (h : FPClassified format before after) {C : W → B} {tail : List Ins}
    (hc : Code C before.rip (fpClassify format ++ tail)) : Code C after.rip tail := by
  rw [h.position]
  exact code_append hc

theorem FPClassified.match_next {format : FPFormat} {before after : X}
    (h : FPClassified format before after) {L : Lay} {r : Res IR.T}
    (hc : Code L.C before.rip (fpClassify format)) (hn : Match L r after) : Match L r before := by
  have falling : ∀ i ∈ (fpClassify format).dropLast, Fall i = true := by
    cases format <;> decide
  have continued : CorrM L r (runL (fpClassify format) before) := by
    simpa only [h.run, CorrM] using hn
  exact go (fpClassify format) before r falling hc continued

theorem fpNegative_bit (format : FPFormat) (word : W) :
    fpNegative format word = word.getLsbD (match format with | .f32 => 31 | .f64 => 63) := by
  cases format
  · change (fpLow32 word &&& BitVec.twoPow 64 31 != 0) = _
    rw [BitVec.and_twoPow]
    simp only [fpLow32, BitVec.getLsbD_setWidth]
    cases word.getLsbD 31 <;> decide
  · change (word &&& BitVec.twoPow 64 63 != 0) = _
    rw [BitVec.and_twoPow]
    cases word.getLsbD 63 <;> decide

private theorem shifted_sign_zero (word : W) (bit : Nat) :
    (((word >>> bit) &&& (1#64)) == (0#64)) = !(word.getLsbD bit) := by
  rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD (x := word >>> bit),
    BitVec.getLsbD_ushiftRight, Nat.add_zero]
  cases word.getLsbD bit <;> rfl

theorem fpInputSign_run (format : FPFormat) (before : X) :
    ∃ after, runL (fpInputSign format) before = .next after ∧
      after.rip = before.rip + BitVec.ofNat 64 (lenOfL (fpInputSign format)) ∧
      after.zf = some (!(fpNegative format before.rax)) ∧
      after.rax = before.rax ∧ after.rsi = before.rsi ∧
      after.r12 = before.r12 ∧ after.r13 = before.r13 ∧ after.r14 = before.r14 ∧
      after.fpReady = before.fpReady := by
  cases format
  all_goals
    refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  all_goals
    simp (disch := decide) [fpInputSign, runL, exec, X.get, X.set, X.nof, X.cmpf, aluStep, aluOp,
      lenOfL, enc, regEnc, le32, BitVec.ofNat_add, BitVec.add_assoc, sx32_ofNat,
      fpNegative_bit, shifted_sign_zero]

theorem fpLimit_run (format : FPFormat) (unsigned : Bool) (before : X) :
    ∃ after, runL (fpLimit .rdx format unsigned ++ [.alu .cmp .rsi .rdx]) before = .next after ∧
      after.rip = before.rip + BitVec.ofNat 64
        (lenOfL (fpLimit .rdx format unsigned ++ [.alu .cmp .rsi .rdx])) ∧
      after.cf = some (before.rsi.ult (if unsigned then format.uint64Limit else format.int64Limit)) ∧
      after.rdx = (if unsigned then format.uint64Limit else format.int64Limit) ∧
      after.rax = before.rax ∧ after.rsi = before.rsi ∧
      after.r12 = before.r12 ∧ after.r13 = before.r13 ∧ after.r14 = before.r14 ∧
      after.fpReady = before.fpReady := by
  cases format <;> cases unsigned
  all_goals
    refine ⟨_, rfl, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  all_goals
    simp (disch := decide) [fpLimit, fpUpper, FPFormat.int64Limit, FPFormat.uint64Limit,
      runL, exec, X.get, X.set, X.nof, X.cmpf, aluStep, aluOp, lenOfL, enc, regEnc, le32,
      BitVec.ofNat_add, BitVec.add_assoc, sx32_ofNat]

end Runner.Beweis
