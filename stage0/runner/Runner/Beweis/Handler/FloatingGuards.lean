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
  -- Keep the actual instruction-by-instruction RIP shape in the execution
  -- witness. Address reassociation belongs only to its scalar position proof.
  let advance (i : Ins) (x : X) : X :=
    { x with rip := x.rip + BitVec.ofNat 64 (enc i).length }
  let normalized : X := match format with
    | .f32 =>
      let loaded : X := (advance (.movToXmm .f32 .xmm0 .rax) before).setXmm .xmm0
        ((before.rax.setWidth 32).setWidth 128)
      (advance (.movFromXmm .f32 .rax .xmm0) loaded).set .rax (loaded.xmmWord .f32 .xmm0)
    | .f64 => before
  let copied : X := (advance (.mov .rsi .rax) normalized).set .rsi normalized.rax
  let maskLoaded : X := (advance (.movi .rdx (BitVec.ofNat 32 1)) copied).set .rdx
    (sx32 (BitVec.ofNat 32 1))
  let shift := match format with | .f32 => 31 | .f64 => 63
  let shiftLoaded : X := (advance (.movi .rcx (BitVec.ofNat 32 shift)) maskLoaded).set .rcx
    (sx32 (BitVec.ofNat 32 shift))
  let shifted : X := ((advance (.shl .rdx) shiftLoaded).set .rdx
    (shiftLoaded.rdx <<< (shiftLoaded.rcx.toNat % 64))).nof
  let complemented : X := aluStep (advance (.alui .xor .rdx (-1)) shifted)
    .xor .rdx (sx32 (-1))
  let masked : X := aluStep (advance (.alu .and .rsi .rdx) complemented)
    .and .rsi complemented.rdx
  let infinity : X := match format with
    | .f32 => (advance (.movi .rdx 0x7F800000) masked).set .rdx (sx32 0x7F800000)
    | .f64 =>
      let loaded : X := (advance (.movi .rdx (BitVec.ofNat 32 0x7FF0)) masked).set .rdx
        (sx32 (BitVec.ofNat 32 0x7FF0))
      let amount : X := (advance (.movi .rcx (BitVec.ofNat 32 48)) loaded).set .rcx
        (sx32 (BitVec.ofNat 32 48))
      ((advance (.shl .rdx) amount).set .rdx (amount.rdx <<< (amount.rcx.toNat % 64))).nof
  let after : X := aluStep (advance (.alu .cmp .rdx .rsi) infinity) .cmp .rdx infinity.rsi
  have allOnes : sx32 4294967295#32 = 18446744073709551615#64 := by decide
  have allSign : (18446744073709551615#64).msb = true := by decide
  have mask32Sign : (18446744071562067967#64).msb = true := by decide
  have mask64Sign : (9223372036854775807#64).msb = false := by decide
  have infinity32Sign : (2139095040#64).msb = false := by decide
  have infinity64Sign : (9218868437227405312#64).msb = false := by decide
  have run : runL (fpClassify format) before = .next after := by
    cases format <;> rfl
  have position : after.rip = before.rip + BitVec.ofNat 64 (lenOfL (fpClassify format)) := by
    cases format
    all_goals
      dsimp only [after, infinity, masked, complemented, shifted, shiftLoaded, shift,
        maskLoaded, copied, normalized, advance, aluStep, aluOp, X.get, X.set, X.setXmm,
        X.nof, X.cmpf]
      simp [fpClassify, fpNormalizeInput, fpSignMask, fpUpper, fpInfinity,
        lenOfL, enc, regEnc, le32, BitVec.ofNat_add, BitVec.add_assoc]
  refine ⟨after, {
    run := run, position := position, input := ?_, magnitude := ?_, infinity := ?_,
    nan := ?_, pc := ?_, frame := ?_, table := ?_, mode := ?_ }⟩
  all_goals
    cases format
    all_goals
      dsimp only [after, infinity, masked, complemented, shifted, shiftLoaded, shift,
        maskLoaded, copied, normalized, advance, aluStep, aluOp, X.get, X.set, X.setXmm,
        X.xmmWord, X.nof, X.cmpf, X.fpReady]
  all_goals
    simp (disch := decide) [FPFormat.scalarBits, FPFormat.infinityBits, FPFormat.signBit,
      fpMagnitude, fpNaN, fpLow32, BitVec.setWidth_setWidth_of_le, sx32_ofNat,
      allOnes, allSign, mask32Sign, mask64Sign, infinity32Sign, infinity64Sign]

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
