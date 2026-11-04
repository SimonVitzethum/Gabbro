module
public import Runner.Beweis.Handler.FloatingWords
import Runner.Beweis.Handler.Sprung
@[expose] public section

namespace Runner.Beweis
open Runner.X86 Runner.Prog

/-! NEG and finite classification are total integer codecs. The physical body
    makes only the original field/slot reads and destination write, never a
    floating request or an assumed hardware callback. -/

macro "fp_codec_corr" : tactic => `(tactic| (
  simp (disch := decide) [IR.op, IR.fp, fpSequence, IR.ret1, IR.f1, IR.f2, IR.f3, IR.ld,
    IR.slot, IR.nxt, binBody, fpNormalizeInput, fpSignMask, fpUpper, fpInfinity,
    fpNegWord_word32, fpNegWord, fpFiniteWord_word32, fpFiniteWord_word64, flagWord,
    runL, exec, fld, sld, sst, mb, ms, ea, Cond.eval, aluStep, aluOp,
    X.get, X.set, X.setXmm, X.xmmWord, X.nof, rd64, rd32,
    sx32_ofNat, fpLow32, BitVec.setWidth_setWidth_of_le, setcc_zx, eq_flags]
  repeat (first | (apply corr_ask; intro _) | (apply corr_opt; intro _))
  simp (disch := decide) [Corr, runL, exec, Cond.eval, X.get, X.set, X.nof, X.fpReady,
    aluStep, aluOp, flagWord, eq_flags, setcc_zx, and_self]))

theorem fp_neg_ok {L : Lay} {y : X} (format : FPFormat)
    (h : HPre L (NativeFPOp.neg format).code y) :
    Match L (IR.op (NativeFPOp.neg format).code ⟨y.r12, y.r13⟩) y := by
  refine straight_go h.tb h.mode
    (binBody (fpNormalizeInput format ++ fpSignMask .rdx format ++ [.alu .xor .rax .rdx])) y _ ?_ ?_ ?_
  · cases format <;> decide
  · cases format <;> exact h.code
  · cases format <;> fp_codec_corr

theorem fp_finite_ok {L : Lay} {y : X} (format : FPFormat)
    (h : HPre L (NativeFPOp.isFinite format).code y) :
    Match L (IR.op (NativeFPOp.isFinite format).code ⟨y.r12, y.r13⟩) y := by
  refine straight_go h.tb h.mode
    (binBody (fpNormalizeInput format ++ fpInfinity .rdx format ++
      [.alu .and .rax .rdx, .alu .cmp .rax .rdx, .set .nz .rax, .zx8 .rax .rax])) y _ ?_ ?_ ?_
  · cases format <;> decide
  · cases format <;> exact h.code
  · cases format <;> fp_codec_corr

end Runner.Beweis
