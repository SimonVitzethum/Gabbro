module
public import Runner.Beweis.Handler.FloatingWords
@[expose] public section

namespace Runner.Beweis
open Runner.X86 Runner.Prog

/-! The physical scalar instructions share the IR's native requests. These
    proofs cover arbitrary answers, including refusal, before any memory model
    restricts answers through NativeFPEval. -/

macro "fp_corr" hm:term : tactic => `(tactic| (
  have ready := $hm
  simp only [X.fpReady] at ready
  simp (disch := decide) [IR.op, IR.fp, IR.ret1, IR.f1, IR.f2, IR.f3, IR.ld, IR.slot, IR.nxt,
    binBody, fpOperands, runL, exec, fld, sld, sst, mb, ms, ea,
    X.get, X.set, X.setXmm, X.xmmWord, X.fpReady, rd64, rd32,
    Runner.fp, NativeFPOp.inputs, NativeFPOp.resultWord, FPArith.native, FPCompare.native,
    fpLow32, BitVec.setWidth_setWidth_of_le, ready]
  repeat (first | (apply corr_ask; intro _) | (apply corr_opt; intro _))
  simp (disch := decide) [runL, exec, X.get, X.set, X.setScalar, X.setXmm, X.xmmWord,
    X.fpReady, X.nof, aluStep, aluOp, fpLow32, BitVec.setWidth_setWidth_of_le,
    Corr, and_self]))

theorem fp_arith_ok {L : Lay} {y : X} (kind : FPArith) (format : FPFormat)
    (h : HPre L (kind.native format).code y) :
    Match L (IR.op (kind.native format).code ⟨y.r12, y.r13⟩) y := by
  refine straight_go h.tb h.mode
    (binBody (fpOperands format ++ [.scalar kind format .xmm0 .xmm1,
      .movFromXmm format .rax .xmm0])) y _ ?_ ?_ ?_
  · cases kind <;> cases format <;> decide
  · cases kind <;> cases format <;> exact h.code
  · cases kind <;> cases format <;> fp_corr h.mode

theorem fp_compare_ok {L : Lay} {y : X} (pred : FPCompare) (format : FPFormat)
    (h : HPre L (pred.native format).code y) :
    Match L (IR.op (pred.native format).code ⟨y.r12, y.r13⟩) y := by
  refine straight_go h.tb h.mode
    (binBody (fpOperands format ++ [.compareScalar pred format .xmm0 .xmm1,
      .movFromXmm format .rax .xmm0, .alui .and .rax 1])) y _ ?_ ?_ ?_
  · cases pred <;> cases format <;> decide
  · cases pred <;> cases format <;> exact h.code
  · cases pred <;> cases format
    all_goals
      have ready := h.mode
      simp only [X.fpReady] at ready
      simp (disch := decide) [IR.op, IR.fp, IR.ret1, IR.f1, IR.f2, IR.f3, IR.ld, IR.slot, IR.nxt,
        binBody, fpOperands, runL, exec, fld, sld, sst, mb, ms, ea,
        X.get, X.set, X.setXmm, X.xmmWord, X.fpReady, rd64, rd32,
        Runner.fp, NativeFPOp.inputs, NativeFPOp.resultWord, FPCompare.native,
        fpLow32, BitVec.setWidth_setWidth_of_le, ready]
      repeat (first | (apply corr_ask; intro _) | (apply corr_opt; intro _))
      split <;> simp (disch := decide) [runL, exec, X.get, X.set, X.setScalar, X.setXmm,
        X.xmmWord, X.fpReady, X.nof, aluStep, aluOp, fpLow32,
        BitVec.setWidth_setWidth_of_le, Corr, and_self]

theorem fp_fromInt_ok {L : Lay} {y : X} (format : FPFormat)
    (h : HPre L (NativeFPOp.fromInt64 format).code y) :
    Match L (IR.op (NativeFPOp.fromInt64 format).code ⟨y.r12, y.r13⟩) y := by
  refine straight_go h.tb h.mode
    (binBody [.fromIntScalar format .xmm0 .rax, .movFromXmm format .rax .xmm0]) y _ ?_ ?_ ?_
  · cases format <;> decide
  · cases format <;> exact h.code
  · cases format <;> fp_corr h.mode

theorem fp_truncate_ok {L : Lay} {y : X} (format : FPFormat)
    (h : HPre L (NativeFPOp.truncateInt64 format).code y) :
    Match L (IR.op (NativeFPOp.truncateInt64 format).code ⟨y.r12, y.r13⟩) y := by
  refine straight_go h.tb h.mode
    (binBody [.movToXmm format .xmm0 .rax, .truncateScalar format .rax .xmm0]) y _ ?_ ?_ ?_
  · cases format <;> decide
  · cases format <;> exact h.code
  · cases format <;> fp_corr h.mode

theorem fp_widen_ok {L : Lay} {y : X} (h : HPre L 54 y) :
    Match L (IR.op 54 ⟨y.r12, y.r13⟩) y := by
  apply straight_go h.tb h.mode
    (binBody [.movToXmm .f32 .xmm1 .rax, .widenScalar .xmm0 .xmm1,
      .movFromXmm .f64 .rax .xmm0]) y _ (by decide) h.code
  fp_corr h.mode

theorem fp_narrow_ok {L : Lay} {y : X} (h : HPre L 55 y) :
    Match L (IR.op 55 ⟨y.r12, y.r13⟩) y := by
  apply straight_go h.tb h.mode
    (binBody [.movToXmm .f64 .xmm1 .rax, .narrowScalar .xmm0 .xmm1,
      .movFromXmm .f32 .rax .xmm0]) y _ (by decide) h.code
  fp_corr h.mode

theorem fp_flags_ok {L : Lay} {y : X} (format : FPFormat)
    (h : HPre L (NativeFPOp.compare format).code y) :
    Match L (IR.op (NativeFPOp.compare format).code ⟨y.r12, y.r13⟩) y := by
  refine straight_go h.tb h.mode
      (binBody (fpOperands format ++ [.ucomis format .xmm0 .xmm1,
        .set .b .rax, .set .p .rdx, .set .z .rsi,
        .zx8 .rax .rax, .zx8 .rdx .rdx, .zx8 .rsi .rsi,
        .movi .rcx 2, .shl .rdx, .movi .rcx 6, .shl .rsi,
        .alu .or .rax .rdx, .alu .or .rax .rsi])) y _ ?_ ?_ ?_
  · cases format <;> decide
  · cases format <;> exact h.code
  · cases format
    all_goals
      have ready := h.mode
      simp only [X.fpReady] at ready
      simp (disch := decide) [IR.op, IR.fp, IR.ret1, IR.f1, IR.f2, IR.f3, IR.ld, IR.slot, IR.nxt,
        binBody, fpOperands, runL, exec, fld, sld, sst, mb, ms, ea,
        X.get, X.set, X.setXmm, X.xmmWord, X.fpReady, rd64, rd32,
        Runner.fp, NativeFPOp.inputs, NativeFPOp.resultWord,
        fpLow32, BitVec.setWidth_setWidth_of_le, ready]
      repeat (first | (apply corr_ask; intro _) | (apply corr_opt; intro _))
      simp (disch := decide) [Cond.eval, runL, exec, X.get, X.set, X.nof, X.fpReady, aluStep, aluOp,
        setcc_zx, zx_bool, pack_compare_flags, BitVec.and_assoc, Corr, and_self]

end Runner.Beweis
