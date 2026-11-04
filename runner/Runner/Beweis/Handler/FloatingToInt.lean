module
public import Runner.Beweis.Handler.FloatingSaturation
@[expose] public section

namespace Runner.Beweis
open Runner.X86 Runner.Prog FPSaturation

/- These names only expose the existing let-bound pieces of fpToIntH to the
   proof. Their concatenation is definitionally the production handler body. -/
private abbrev intClamp (format : FPFormat) : List Ins :=
  fpInputSign format ++ fpSignMask .rax .f64 ++ [.alu .test .rdi .rdi] ++
    fpChoose .nz [] [.alui .sub .rax 1]

private abbrev intFinite (format : FPFormat) : List Ins :=
  fpLimit .rdx format false ++ [.alu .cmp .rsi .rdx] ++
    fpChoose .b (fpTruncateBody format) (intClamp format)

private abbrev intBody (format : FPFormat) : List Ins :=
  fpClassify format ++ fpChoose .b [.movi .rax 0] (intFinite format)

private theorem clamp_prefix (format : FPFormat) (x : X) :
    ∃ z, runL (fpInputSign format ++ fpSignMask .rax .f64 ++ [.alu .test .rdi .rdi]) x = .next z ∧
      z.rip = x.rip + BitVec.ofNat 64
        (lenOfL (fpInputSign format ++ fpSignMask .rax .f64 ++ [.alu .test .rdi .rdi])) ∧
      z.rax = 0x8000000000000000 ∧ z.zf = some (!(fpNegative format x.rax)) ∧
      z.r12 = x.r12 ∧ z.r13 = x.r13 ∧ z.r14 = x.r14 ∧ z.fpReady = x.fpReady := by
  have signZero (word : W) (bit : Nat) :
      (((word >>> bit) &&& 1) == 0) = !(word.getLsbD bit) := by
    rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD, BitVec.getLsbD_ushiftRight, Nat.add_zero]
    cases word.getLsbD bit <;> rfl
  cases format
  all_goals
    refine ⟨_, rfl, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    simp (disch := decide) [fpInputSign, fpSignMask, fpUpper, runL, exec,
      X.get, X.set, X.nof, aluStep, aluOp, BitVec.and_self,
      lenOfL, enc, regEnc, le32, BitVec.ofNat_add, BitVec.add_assoc,
      sx32_ofNat, fpNegative_bit, signZero]

private theorem clamp_match {L : Lay} {t : IR.T} {x : X} {tail : List Ins}
    {k : W → Res IR.T} (format : FPFormat) (exit : Exit L t tail k)
    (code : Code L.C x.rip (intClamp format ++ tail)) (controls : Controls L t x) :
    Match L (k (if fpNegative format x.rax then 0x8000000000000000 else 0x7FFFFFFFFFFFFFFF)) x := by
  let first := fpInputSign format ++ fpSignMask .rax .f64 ++ [.alu .test .rdi .rdi]
  have complete : Code L.C x.rip (first ++ (fpChoose .nz [] [.alui .sub .rax 1] ++ tail)) := by
    simpa only [first, intClamp, List.append_assoc] using code
  obtain ⟨z, run, position, result, flag, pc, frame, table, mode⟩ := clamp_prefix format x
  have placed : Code L.C z.rip (fpChoose .nz [] [.alui .sub .rax 1] ++ tail) := by
    rw [position]
    exact code_append (by simpa only [first, List.append_assoc] using complete)
  have kept : Controls L t z :=
    ⟨pc.trans controls.pc, frame.trans controls.frame, table.trans controls.table, mode.trans controls.mode⟩
  apply pure_match (body := first) complete (by cases format <;> decide) run
  cases sign : fpNegative format x.rax with
  | true =>
    simp only [sign, ↓reduceIte]
    apply fpChoose_true placed
    · simp only [Cond.eval, flag, sign, Bool.not_true, Option.map_some, Bool.not_false]
    · have leaf := exit.finish (choiceTaken z .nz [.alui .sub .rax 1])
        (fpChoose_yes_code placed (by decide))
        ⟨kept.pc, kept.frame, kept.table, kept.mode⟩
      simpa only [result] using leaf
  | false =>
    simp only [sign, Bool.false_eq_true, ↓reduceIte]
    apply fpChoose_false placed
    · simp only [Cond.eval, flag, sign, Bool.not_false, Option.map_some, Bool.not_true]
    · let subtract := choiceFallthrough z .nz [.alui .sub .rax 1]
      have noCode := fpChoose_no_code placed
      let after := aluStep
        { subtract with rip := subtract.rip + BitVec.ofNat 64 (enc (.alui .sub .rax 1)).length }
        .sub .rax (sx32 1)
      have output : after.rax = 0x7FFFFFFFFFFFFFFF := by
        change z.rax - sx32 (1 : BitVec 32) = 0x7FFFFFFFFFFFFFFF
        rw [result, fp_control_immediates.1]
        decide
      apply pure_match (body := [.alui .sub .rax 1]) (z := after) noCode (by decide) rfl
      have leaf := (exit.jump (yes := []) (by decide)).finish after noCode.2.2
        ⟨kept.pc, kept.frame, kept.table, kept.mode⟩
      simpa only [output] using leaf

private theorem finite_match {L : Lay} {t : IR.T} {x : X} {tail : List Ins}
    {k : W → Res IR.T} (format : FPFormat) (value : W) (exit : Exit L t tail k)
    (code : Code L.C x.rip (intFinite format ++ tail))
    (controls : Controls L t x) (input : x.rax = format.scalarBits value)
    (magnitude : x.rsi = fpMagnitude format value) :
    Match L (if (fpMagnitude format value).ult format.int64Limit then
      Runner.fp (.truncateInt64 format) value 0 k
      else k (if fpNegative format value then 0x8000000000000000 else 0x7FFFFFFFFFFFFFFF)) x := by
  let first := fpLimit .rdx format false ++ [.alu .cmp .rsi .rdx]
  have complete : Code L.C x.rip
      (first ++ (fpChoose .b (fpTruncateBody format) (intClamp format) ++ tail)) := by
    simpa only [first, intFinite, List.append_assoc] using code
  obtain ⟨z, run, position, flag, limit, rax, rsi, pc, frame, table, mode⟩ := fpLimit_run format false x
  have placed : Code L.C z.rip (fpChoose .b (fpTruncateBody format) (intClamp format) ++ tail) := by
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
    have leaf := truncate (x := choiceTaken z .b (intClamp format)) format exit
      (fpChoose_yes_code placed (by cases format <;> decide))
      ⟨kept.pc, kept.frame, kept.table, kept.mode⟩
    cases format <;> simpa only [rax, input, FPFormat.scalarBits, Runner.fp,
      NativeFPOp.inputs, fpLow32_idem] using leaf
  | false =>
    simp only [within, Bool.false_eq_true, ↓reduceIte]
    apply fpChoose_false placed (by simp only [Cond.eval, actualFlag, within])
    have leaf := clamp_match (x := choiceFallthrough z .b (intClamp format)) format
      (exit.jump (yes := fpTruncateBody format)
      (by cases format <;> decide)) (fpChoose_no_code placed)
      ⟨kept.pc, kept.frame, kept.table, kept.mode⟩
    simpa only [rax, input, negative_scalar] using leaf

private theorem body_match {L : Lay} {t : IR.T} {x : X} {tail : List Ins}
    {k : W → Res IR.T} (format : FPFormat) (exit : Exit L t tail k)
    (code : Code L.C x.rip (intBody format ++ tail)) (controls : Controls L t x) :
    Match L (fpToInt64 format x.rax k) x := by
  have complete : Code L.C x.rip
      (fpClassify format ++ (fpChoose .b [.movi .rax 0] (intFinite format) ++ tail)) := by
    simpa only [intBody, List.append_assoc] using code
  obtain ⟨z, classified⟩ := fpClassify_run format x
  have placed : Code L.C z.rip (fpChoose .b [.movi .rax 0] (intFinite format) ++ tail) :=
    classified.code complete
  have kept : Controls L t z :=
    ⟨classified.pc.trans controls.pc, classified.frame.trans controls.frame,
      classified.table.trans controls.table, classified.mode.trans controls.mode⟩
  apply classified.match_next (code_prefix complete)
  cases nan : fpNaN format x.rax with
  | true =>
    simp only [fpToInt64, nan, ↓reduceIte]
    apply fpChoose_true placed (by simp only [Cond.eval, classified.nan, nan])
    simpa only [sx32_zero] using word_constant
      (x := choiceTaken z .b (intFinite format)) exit (0 : BitVec 32)
      (fpChoose_yes_code placed (by cases format <;> decide))
      ⟨kept.pc, kept.frame, kept.table, kept.mode⟩
  | false =>
    simp only [fpToInt64, nan, Bool.false_eq_true, ↓reduceIte]
    apply fpChoose_false placed (by simp only [Cond.eval, classified.nan, nan])
    exact finite_match (x := choiceFallthrough z .b (intFinite format)) format x.rax
      (exit.jump (yes := [.movi .rax 0]) (by decide))
      (fpChoose_no_code placed)
      ⟨kept.pc, kept.frame, kept.table, kept.mode⟩
      classified.input classified.magnitude

/-- The complete production signed-saturation handler, with all operand reads,
    branches, arbitrary/refused CVTT answers, destination writes and dispatch. -/
theorem fp_toInt64_body {L : Lay} {y : X} (format : FPFormat)
    (table : y.r14 = L.T) (mode : y.fpReady = true)
    (code : Code L.C y.rip (fpToIntH format)) :
    Match L (IR.f2 ⟨y.r12, y.r13⟩ fun a => IR.ld ⟨y.r12, y.r13⟩ a fun va =>
      IR.f3 ⟨y.r12, y.r13⟩ fun b => IR.ld ⟨y.r12, y.r13⟩ b fun _ =>
      fpToInt64 format va (IR.ret1 ⟨y.r12, y.r13⟩)) y := by
  apply read_body (intBody format) (fpToInt64 format) table mode code
  intro x controls placed
  exact body_match format (store_exit L _)
    (by simpa only [List.append_assoc] using placed) controls

end Runner.Beweis
