module
public import Runner.Beweis.Handler.FloatingWords
@[expose] public section

namespace Runner.Beweis
open Runner.X86 Runner.Prog

/-! The physical scalar instructions share the IR's native requests. These
    proofs cover arbitrary answers, including refusal, before any memory model
    restricts answers through NativeFPEval. -/

theorem fp_control_immediates :
    sx32 1#32 = 1#64 ∧ sx32 2#32 = 2#64 ∧ sx32 6#32 = 6#64 := by decide

theorem fp_compare_bool_zero (word : W) :
    (if word = 0 then (0 : W) else 1) = 0 ↔ word = 0 := by
  by_cases zero : word = 0 <;> simp [zero]

theorem fp_compare_mask32 (word : W) :
    (((if word = 0 then (0 : W) else BitVec.allOnes 64).setWidth 32).setWidth 64 &&& 1) =
      if word = 0 then 0 else 1 := by
  by_cases zero : word = 0
  · simpa only [if_pos zero] using
      (show (((0 : W).setWidth 32).setWidth 64 &&& 1) = (0 : W) from by decide)
  · simpa only [if_neg zero] using
      (show (((BitVec.allOnes 64).setWidth 32).setWidth 64 &&& 1) = (1 : W) from by decide)

theorem fp_compare_mask64 (word : W) :
    ((if word = 0 then (0 : W) else BitVec.allOnes 64) &&& 1) =
      if word = 0 then 0 else 1 := by
  by_cases zero : word = 0
  · simpa only [if_pos zero] using (show (0 : W) &&& 1 = 0 from by decide)
  · simpa only [if_neg zero] using (show BitVec.allOnes 64 &&& 1 = (1 : W) from by decide)

theorem fp_scalar_pc (x : X) (format : FPFormat) (destination : Xmm) (value : W) :
    (x.setScalar format destination value).r12 = x.r12 := by cases format <;> rfl

theorem fp_scalar_frame (x : X) (format : FPFormat) (destination : Xmm) (value : W) :
    (x.setScalar format destination value).r13 = x.r13 := by cases format <;> rfl

theorem fp_scalar_table (x : X) (format : FPFormat) (destination : Xmm) (value : W) :
    (x.setScalar format destination value).r14 = x.r14 := by cases format <;> rfl

theorem fp_scalar_mode (x : X) (format : FPFormat) (destination : Xmm) (value : W) :
    (x.setScalar format destination value).fpReady = x.fpReady := by cases format <;> rfl

theorem fp_scalar_mxcsr (x : X) (format : FPFormat) (destination : Xmm) (value : W) :
    (x.setScalar format destination value).mxcsr = x.mxcsr := by cases format <;> rfl

/- `runL` is deliberately absent here. A residual instruction list must not be
   expanded under a still unknown request answer or flag state. Mode reduction
   is committed before any word simplification can fail or expose more lanes. -/
macro "fp_reduce" ready:term : tactic => `(tactic| (
  try simp only [exec]
  try dsimp only [X.get, X.set, X.setXmm, X.nof, X.cmpf]
  try simp only [X.fpReady, fp_scalar_mxcsr, beq_iff_eq, ($ready), ↓reduceIte]
  try rw [ite_eq_left ($ready)]
  try simp only [bind_next, bind_ask, bind_opt, bind_fault, bind_unk]
  try simp only [xmmWord_setScalar, fp_scalar_pc, fp_scalar_frame, fp_scalar_table, fp_scalar_mode]
  try simp (disch := decide) [bind_next, bind_ask, bind_opt,
    fld, sld, sst, mb, ms, ea, ir_sx, X.get, X.set, X.setXmm, X.xmmWord,
    X.nof, X.cmpf, Cond.eval, aluStep, aluOp, rd64, rd32, wr64,
    Runner.fp, NativeFPOp.inputs, NativeFPOp.resultWord, FPArith.native, FPCompare.native,
    fpLow32, uint64StickyHalf, BitVec.setWidth_setWidth_of_le,
    fp_control_immediates.1, fp_control_immediates.2.1, fp_control_immediates.2.2,
    fp_compare_bool_zero, fp_compare_mask32, fp_compare_mask64,
    fp_scalar_pc, fp_scalar_frame, fp_scalar_table, fp_scalar_mode,
    setcc_zx, zx_bool, pack_compare_flags, BitVec.and_assoc]))

macro "fp_corr" hm:term : tactic => `(tactic| (
  have ready := $hm
  try simp only [X.fpReady, beq_iff_eq] at ready
  try simp only [NativeFPOp.code, FPArith.native, FPCompare.native,
    IR.op, IR.fp, fpSequence, IR.ret1, IR.f1, IR.f2, IR.f3, IR.ld, IR.slot, IR.nxt,
    binBody, fpOperands, List.cons_append, List.nil_append, List.append_assoc]
  fp_reduce ready
  repeat (first
    | (apply corr_ask; intro _; fp_reduce ready)
    | (apply corr_opt; intro _; fp_reduce ready)
    | (rw [runL]; fp_reduce ready))
  all_goals try simp [Corr, X.fpReady]))

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
  · cases pred <;> cases format <;> fp_corr h.mode
    all_goals
      constructor
      · try rw [fp_control_immediates.1]
        first
        | exact (fp_compare_mask32 _).symm
        | exact (fp_compare_mask64 _).symm
      · intro answer
        cases answer with
        | none => trivial
        | some result => exact ⟨rfl, rfl, rfl, rfl⟩

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
  · cases format <;> fp_corr h.mode
    all_goals
      constructor
      · try rw [fp_control_immediates.2.1, fp_control_immediates.2.2]
        exact (pack_compare_flags _).symm
      · intro answer
        cases answer with
        | none => trivial
        | some result => exact ⟨rfl, rfl, rfl, rfl⟩

end Runner.Beweis
