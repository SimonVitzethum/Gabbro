module
public import Runner.Beweis.Handler.FloatingWords
import Runner.Beweis.Handler.Floating
import Runner.Beweis.Handler.Sprung
@[expose] public section

namespace Runner.Beweis
open Runner.X86 Runner.Prog

/-! NEG and finite classification are total integer codecs. The physical body
    makes only the original field/slot reads and destination write, never a
    floating request or an assumed hardware callback. -/

/- Reduce one active instruction before consuming an answer. Keep runL out of
   the reducer, so the remaining list stays closed under unknown read/write
   answers. The shared FP reducer also normalizes actual CMP flag projections. -/
macro "fp_codec_reduce" ready:term : tactic => `(tactic| (
  fp_reduce $ready
  try simp (disch := decide) [bind_next, bind_ask, bind_opt,
    fpNegWord_word32, fpNegWord, fpFiniteWord_word32, fpFiniteWord_word64, flagWord,
    X.cmpf, X.get, X.set, X.nof, Cond.eval, sx32_ofNat,
    eq_flags, setcc_zx, zx_bool, zx_prop]))

macro "fp_codec_corr" hm:term : tactic => `(tactic| (
  have ready := $hm
  simp only [X.fpReady, beq_iff_eq] at ready
  simp only [IR.op, IR.fp, fpSequence, IR.ret1, IR.f1, IR.f2, IR.f3, IR.ld,
    IR.slot, IR.nxt, binBody, fpNormalizeInput, fpSignMask, fpUpper, fpInfinity,
    fpNegWord_word32, fpNegWord, fpFiniteWord_word32, fpFiniteWord_word64, flagWord,
    List.cons_append, List.nil_append, List.append_assoc]
  fp_codec_reduce ready
  repeat (first
    | (apply corr_ask; intro _; fp_codec_reduce ready)
    | (apply corr_opt; intro _; fp_codec_reduce ready)
    | (rw [runL]; fp_codec_reduce ready))
  all_goals simp [Corr, X.fpReady]))

theorem fp_neg_ok {L : Lay} {y : X} (format : FPFormat)
    (h : HPre L (NativeFPOp.neg format).code y) :
    Match L (IR.op (NativeFPOp.neg format).code ⟨y.r12, y.r13⟩) y := by
  refine straight_go h.tb h.mode
    (binBody (fpNormalizeInput format ++ fpSignMask .rdx format ++ [.alu .xor .rax .rdx])) y _ ?_ ?_ ?_
  · cases format <;> decide
  · cases format <;> exact h.code
  · cases format <;> fp_codec_corr h.mode

theorem fp_finite_ok {L : Lay} {y : X} (format : FPFormat)
    (h : HPre L (NativeFPOp.isFinite format).code y) :
    Match L (IR.op (NativeFPOp.isFinite format).code ⟨y.r12, y.r13⟩) y := by
  refine straight_go h.tb h.mode
    (binBody (fpNormalizeInput format ++ fpInfinity .rdx format ++
      [.alu .and .rax .rdx, .alu .cmp .rax .rdx, .set .nz .rax, .zx8 .rax .rax])) y _ ?_ ?_ ?_
  · cases format <;> decide
  · cases format <;> exact h.code
  · cases format <;> fp_codec_corr h.mode

end Runner.Beweis
