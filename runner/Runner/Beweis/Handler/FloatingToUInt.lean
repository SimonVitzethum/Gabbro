module
public import Runner.Beweis.Handler.FloatingSaturation
@[expose] public section

namespace Runner.Beweis
open Runner.X86 Runner.Prog FPSaturation

/- Proof names for the original let-bound byte fragments of fpToUIntH. -/
private abbrev uintHigh (format : FPFormat) : List Ins :=
  [.movToXmm format .xmm0 .rax] ++ fpLimit .rdx format false ++
    [.movToXmm format .xmm1 .rdx, .scalar .sub format .xmm0 .xmm1,
      .truncateScalar format .rax .xmm0] ++ fpSignMask .rdx .f64 ++ [.alu .or .rax .rdx]

private abbrev uintInRange (format : FPFormat) : List Ins :=
  fpLimit .rdx format false ++ [.alu .cmp .rsi .rdx] ++
    fpChoose .b (fpTruncateBody format) (uintHigh format)

private abbrev uintPositive (format : FPFormat) : List Ins :=
  fpLimit .rdx format true ++ [.alu .cmp .rsi .rdx] ++
    fpChoose .b (uintInRange format) [.movi .rax (-1)]

private abbrev uintFinite (format : FPFormat) : List Ins :=
  fpInputSign format ++ fpChoose .nz [.movi .rax 0] (uintPositive format)

private abbrev uintBody (format : FPFormat) : List Ins :=
  fpClassify format ++ fpChoose .b [.movi .rax 0] (uintFinite format)

private theorem high_match {L : Lay} {t : IR.T} {x : X} {tail : List Ins}
    {k : W → Res IR.T} (format : FPFormat) (exit : Exit L t tail k)
    (code : Code L.C x.rip (uintHigh format ++ tail)) (controls : Controls L t x) :
    Match L (Runner.fp (.sub format) x.rax format.int64Limit fun reduced =>
      Runner.fp (.truncateInt64 format) reduced 0 fun integer =>
        k (integer ||| 0x8000000000000000)) x := by
  have placed := code_append code
  apply go (uintHigh format) x _ (by cases format <;> decide) (code_prefix code)
  have ready := controls.mode
  simp only [X.fpReady, beq_iff_eq] at ready
  cases format
  all_goals
    simp only [uintHigh, fpLimit, fpSignMask, fpUpper, FPFormat.int64Limit,
      List.cons_append, List.nil_append, List.append_assoc]
    fp_reduce ready
    repeat (first
      | (apply corrM_ask; intro _; fp_reduce ready)
      | (apply corrM_opt; intro _; fp_reduce ready)
      | (rw [runL]; fp_reduce ready))
    simp only [CorrM]
    apply exit.finish
    · simpa (disch := decide) [uintHigh, fpLimit, fpSignMask, fpUpper, lenOfL,
        enc, regEnc, le32, BitVec.ofNat_add, BitVec.add_assoc,
        X.get, X.set, X.setXmm, X.setScalar, X.nof, aluStep, aluOp] using placed
    · exact ⟨controls.pc, controls.frame, controls.table, controls.mode⟩

private theorem inRange_match {L : Lay} {t : IR.T} {x : X} {tail : List Ins}
    {k : W → Res IR.T} (format : FPFormat) (value : W) (exit : Exit L t tail k)
    (code : Code L.C x.rip (uintInRange format ++ tail))
    (controls : Controls L t x) (input : x.rax = format.scalarBits value)
    (magnitude : x.rsi = fpMagnitude format value) :
    Match L (if (fpMagnitude format value).ult format.int64Limit then
      Runner.fp (.truncateInt64 format) value 0 k
      else Runner.fp (.sub format) value format.int64Limit fun reduced =>
        Runner.fp (.truncateInt64 format) reduced 0 fun integer =>
          k (integer ||| 0x8000000000000000)) x := by
  let first := fpLimit .rdx format false ++ [.alu .cmp .rsi .rdx]
  have complete : Code L.C x.rip
      (first ++ (fpChoose .b (fpTruncateBody format) (uintHigh format) ++ tail)) := by
    simpa only [first, uintInRange, List.append_assoc] using code
  obtain ⟨z, run, position, flag, limit, rax, rsi, pc, frame, table, mode⟩ := fpLimit_run format false x
  have placed : Code L.C z.rip (fpChoose .b (fpTruncateBody format) (uintHigh format) ++ tail) := by
    rw [position]
    exact code_append (by simpa only [first, List.append_assoc] using complete)
  have kept : Controls L t z :=
    ⟨pc.trans controls.pc, frame.trans controls.frame, table.trans controls.table, mode.trans controls.mode⟩
  have actualFlag : z.cf = some ((fpMagnitude format value).ult format.int64Limit) := by
    simpa only [Bool.false_eq_true, ↓reduceIte, magnitude] using flag
  apply pure_match (body := first) complete (by cases format <;> decide) run
  cases within : (fpMagnitude format value).ult format.int64Limit with
  | true =>
    simp only [within, ↓reduceIte]
    apply fpChoose_true placed (by simp only [Cond.eval, actualFlag, within])
    have leaf := truncate (x := choiceTaken z .b (uintHigh format)) format exit
      (fpChoose_yes_code placed (by cases format <;> decide))
      ⟨kept.pc, kept.frame, kept.table, kept.mode⟩
    cases format <;> simpa only [rax, input, FPFormat.scalarBits, Runner.fp,
      NativeFPOp.inputs, fpLow32_idem] using leaf
  | false =>
    simp only [within, Bool.false_eq_true, ↓reduceIte]
    apply fpChoose_false placed (by simp only [Cond.eval, actualFlag, within])
    have leaf := high_match (x := choiceFallthrough z .b (uintHigh format)) format
      (exit.jump (yes := fpTruncateBody format) (by cases format <;> decide))
      (fpChoose_no_code placed) ⟨kept.pc, kept.frame, kept.table, kept.mode⟩
    cases format <;> simpa only [rax, input, FPFormat.scalarBits, Runner.fp,
      NativeFPOp.inputs, fpLow32_idem] using leaf

private theorem positive_match {L : Lay} {t : IR.T} {x : X} {tail : List Ins}
    {k : W → Res IR.T} (format : FPFormat) (value : W) (exit : Exit L t tail k)
    (code : Code L.C x.rip (uintPositive format ++ tail))
    (controls : Controls L t x) (input : x.rax = format.scalarBits value)
    (magnitude : x.rsi = fpMagnitude format value) :
    Match L (if (fpMagnitude format value).ult format.uint64Limit then
      (if (fpMagnitude format value).ult format.int64Limit then
        Runner.fp (.truncateInt64 format) value 0 k
        else Runner.fp (.sub format) value format.int64Limit fun reduced =>
          Runner.fp (.truncateInt64 format) reduced 0 fun integer =>
            k (integer ||| 0x8000000000000000))
      else k 0xFFFFFFFFFFFFFFFF) x := by
  let first := fpLimit .rdx format true ++ [.alu .cmp .rsi .rdx]
  have complete : Code L.C x.rip
      (first ++ (fpChoose .b (uintInRange format) [.movi .rax (-1)] ++ tail)) := by
    simpa only [first, uintPositive, List.append_assoc] using code
  obtain ⟨z, run, position, flag, limit, rax, rsi, pc, frame, table, mode⟩ := fpLimit_run format true x
  have placed : Code L.C z.rip (fpChoose .b (uintInRange format) [.movi .rax (-1)] ++ tail) := by
    rw [position]
    exact code_append (by simpa only [first, List.append_assoc] using complete)
  have kept : Controls L t z :=
    ⟨pc.trans controls.pc, frame.trans controls.frame, table.trans controls.table, mode.trans controls.mode⟩
  have actualFlag : z.cf = some ((fpMagnitude format value).ult format.uint64Limit) := by
    simpa only [↓reduceIte, magnitude] using flag
  apply pure_match (body := first) complete (by cases format <;> decide) run
  cases within : (fpMagnitude format value).ult format.uint64Limit with
  | true =>
    simp only [within, ↓reduceIte]
    apply fpChoose_true placed (by simp only [Cond.eval, actualFlag, within])
    exact inRange_match (x := choiceTaken z .b [.movi .rax (-1)]) format value exit
      (fpChoose_yes_code placed (by decide))
      ⟨kept.pc, kept.frame, kept.table, kept.mode⟩ (rax.trans input)
      (rsi.trans magnitude)
  | false =>
    simp only [within, Bool.false_eq_true, ↓reduceIte]
    apply fpChoose_false placed (by simp only [Cond.eval, actualFlag, within])
    have leaf := word_constant (x := choiceFallthrough z .b [.movi .rax (-1)])
      (exit.jump (yes := uintInRange format) (by cases format <;> decide))
      (-1 : BitVec 32) (fpChoose_no_code placed) ⟨kept.pc, kept.frame, kept.table, kept.mode⟩
    simpa only [show sx32 (-1 : BitVec 32) = (0xFFFFFFFFFFFFFFFF : W) from by decide] using leaf

private theorem finite_match {L : Lay} {t : IR.T} {x : X} {tail : List Ins}
    {k : W → Res IR.T} (format : FPFormat) (value : W) (exit : Exit L t tail k)
    (code : Code L.C x.rip (uintFinite format ++ tail))
    (controls : Controls L t x) (input : x.rax = format.scalarBits value)
    (magnitude : x.rsi = fpMagnitude format value) :
    Match L (if fpNegative format value then k 0
      else if (fpMagnitude format value).ult format.uint64Limit then
        (if (fpMagnitude format value).ult format.int64Limit then
          Runner.fp (.truncateInt64 format) value 0 k
          else Runner.fp (.sub format) value format.int64Limit fun reduced =>
            Runner.fp (.truncateInt64 format) reduced 0 fun integer =>
              k (integer ||| 0x8000000000000000))
      else k 0xFFFFFFFFFFFFFFFF) x := by
  obtain ⟨z, run, position, flag, rax, rsi, pc, frame, table, mode⟩ := fpInputSign_run format x
  have placed : Code L.C z.rip (fpChoose .nz [.movi .rax 0] (uintPositive format) ++ tail) := by
    rw [position]
    exact code_append (by simpa only [uintFinite, List.append_assoc] using code)
  have kept : Controls L t z :=
    ⟨pc.trans controls.pc, frame.trans controls.frame, table.trans controls.table, mode.trans controls.mode⟩
  have actualFlag : Cond.eval z .nz = some (fpNegative format value) := by
    simp only [Cond.eval, flag, input, negative_scalar, Option.map_some, Bool.not_not]
  apply pure_match (body := fpInputSign format)
    (by simpa only [uintFinite, List.append_assoc] using code) (by cases format <;> decide) run
  cases negative : fpNegative format value with
  | true =>
    simp only [negative, ↓reduceIte]
    apply fpChoose_true placed (by simpa only [negative] using actualFlag)
    simpa only [sx32_zero] using word_constant
      (x := choiceTaken z .nz (uintPositive format)) exit (0 : BitVec 32)
      (fpChoose_yes_code placed (by cases format <;> decide))
      ⟨kept.pc, kept.frame, kept.table, kept.mode⟩
  | false =>
    simp only [negative, Bool.false_eq_true, ↓reduceIte]
    apply fpChoose_false placed (by simpa only [negative] using actualFlag)
    exact positive_match (x := choiceFallthrough z .nz (uintPositive format)) format value
      (exit.jump (yes := [.movi .rax 0]) (by decide)) (fpChoose_no_code placed)
      ⟨kept.pc, kept.frame, kept.table, kept.mode⟩ (rax.trans input)
      (rsi.trans magnitude)

private theorem body_match {L : Lay} {t : IR.T} {x : X} {tail : List Ins}
    {k : W → Res IR.T} (format : FPFormat) (exit : Exit L t tail k)
    (code : Code L.C x.rip (uintBody format ++ tail)) (controls : Controls L t x) :
    Match L (fpToUInt64 format x.rax k) x := by
  have complete : Code L.C x.rip
      (fpClassify format ++ (fpChoose .b [.movi .rax 0] (uintFinite format) ++ tail)) := by
    simpa only [uintBody, List.append_assoc] using code
  obtain ⟨z, classified⟩ := fpClassify_run format x
  have placed : Code L.C z.rip (fpChoose .b [.movi .rax 0] (uintFinite format) ++ tail) :=
    classified.code complete
  have kept : Controls L t z :=
    ⟨classified.pc.trans controls.pc, classified.frame.trans controls.frame,
      classified.table.trans controls.table, classified.mode.trans controls.mode⟩
  apply classified.match_next (code_prefix complete)
  cases nan : fpNaN format x.rax with
  | true =>
    simp only [fpToUInt64, nan, Bool.true_or, ↓reduceIte]
    apply fpChoose_true placed (by simp only [Cond.eval, classified.nan, nan])
    simpa only [sx32_zero] using word_constant
      (x := choiceTaken z .b (uintFinite format)) exit (0 : BitVec 32)
      (fpChoose_yes_code placed (by cases format <;> decide))
      ⟨kept.pc, kept.frame, kept.table, kept.mode⟩
  | false =>
    simp only [fpToUInt64, nan, Bool.false_or]
    apply fpChoose_false placed (by simp only [Cond.eval, classified.nan, nan])
    exact finite_match (x := choiceFallthrough z .b (uintFinite format)) format x.rax
      (exit.jump (yes := [.movi .rax 0]) (by decide)) (fpChoose_no_code placed)
      ⟨kept.pc, kept.frame, kept.table, kept.mode⟩
      classified.input classified.magnitude

/-- The whole production unsigned-saturation handler. All guard bytes and
    both high-path native requests are matched before the full result write. -/
theorem fp_toUInt64_body {L : Lay} {y : X} (format : FPFormat)
    (table : y.r14 = L.T) (mode : y.fpReady = true)
    (code : Code L.C y.rip (fpToUIntH format)) :
    Match L (IR.f2 ⟨y.r12, y.r13⟩ fun a => IR.ld ⟨y.r12, y.r13⟩ a fun va =>
      IR.f3 ⟨y.r12, y.r13⟩ fun b => IR.ld ⟨y.r12, y.r13⟩ b fun _ =>
      fpToUInt64 format va (IR.ret1 ⟨y.r12, y.r13⟩)) y := by
  apply read_body (uintBody format) (fpToUInt64 format) table mode code
  intro x controls placed
  exact body_match format (store_exit L _)
    (by simpa only [List.append_assoc] using placed) controls

end Runner.Beweis
