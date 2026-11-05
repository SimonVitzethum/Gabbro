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
      (((word >>> bit) &&& (1#64)) == (0#64)) = !(word.getLsbD bit) := by
    rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD (x := word >>> bit),
      BitVec.getLsbD_ushiftRight, Nat.add_zero]
    cases word.getLsbD bit <;> rfl
  -- Preserve each actual instruction advance in the witness. In particular,
  -- the final TEST observes RDI after the intervening mask construction.
  let advance (i : Ins) (state : X) : X :=
    { state with rip := (state.rip + BitVec.ofNat 64 (enc i).length) }
  let copied : X := (advance (.mov .rdi .rax) x).set .rdi x.rax
  let bit : Nat := match format with | .f32 => 31 | .f64 => 63
  let counted : X := (advance (.movi .rcx (BitVec.ofNat 32 bit)) copied).set .rcx
    (sx32 (BitVec.ofNat 32 bit))
  let shifted : X := ((advance (.shr .rdi) counted).set .rdi
    (counted.rdi >>> (counted.rcx.toNat % 64))).nof
  let masked : X := aluStep (advance (.alui .and .rdi 1) shifted) .and .rdi (sx32 (1#32))
  let tested : X := aluStep (advance (.alu .test .rdi .rdi) masked) .test .rdi masked.rdi
  let one : X := (advance (.movi .rax 1) tested).set .rax (sx32 (1#32))
  let highCount : X := (advance (.movi .rcx 63) one).set .rcx (sx32 (63#32))
  let raised : X := ((advance (.shl .rax) highCount).set .rax
    (highCount.rax <<< (highCount.rcx.toNat % 64))).nof
  let z : X := aluStep (advance (.alu .test .rdi .rdi) raised) .test .rdi raised.rdi
  have run : runL (fpInputSign format ++ fpSignMask .rax .f64 ++
      [.alu .test .rdi .rdi]) x = .next z := by
    cases format <;> rfl
  have position : z.rip = x.rip + BitVec.ofNat 64
      (lenOfL (fpInputSign format ++ fpSignMask .rax .f64 ++ [.alu .test .rdi .rdi])) := by
    dsimp only [z, raised, highCount, one, tested, masked, shifted, counted, bit, copied,
      advance, aluStep, aluOp, X.set, X.get, X.nof]
    cases format <;> simp [fpInputSign, fpSignMask, fpUpper, lenOfL,
      BitVec.ofNat_add, BitVec.add_assoc]
  refine ⟨z, run, position, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    cases format
    all_goals
      dsimp only [z, raised, highCount, one, tested, masked, shifted, counted, bit,
        copied, advance, aluStep, aluOp, X.get, X.set, X.nof, X.fpReady]
  all_goals
    simp (disch := decide) [BitVec.and_self, sx32_ofNat, fpNegative_bit, signZero]

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
    · let selected := choiceTaken z .nz [.alui .sub .rax 1]
      have leaf : Match L (k z.rax) selected := exit.finish selected
        (fpChoose_yes_code placed (by decide))
        ⟨kept.pc, kept.frame, kept.table, kept.mode⟩
      exact (congrArg (fun value => Match L (k value) selected) result).mp leaf
  | false =>
    simp only [sign, Bool.false_eq_true, ↓reduceIte]
    apply fpChoose_false placed
    · simp only [Cond.eval, flag, sign, Bool.not_false, Option.map_some, Bool.not_true]
    · let subtract := choiceFallthrough z .nz [.alui .sub .rax 1]
      have noCode := fpChoose_no_code placed
      let after := aluStep
        { subtract with rip := (subtract.rip + BitVec.ofNat 64 (enc (.alui .sub .rax 1)).length) }
        .sub .rax (sx32 1)
      have output : after.rax = 0x7FFFFFFFFFFFFFFF := by
        change z.rax - sx32 (1#32) = 0x7FFFFFFFFFFFFFFF
        rw [result]
        decide
      have subtractCode : Code L.C subtract.rip
          ([.alui .sub .rax 1] ++ (.jmp (BitVec.ofNat 32 (lenOf [])) :: tail)) := by
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using noCode
      apply pure_match (body := [.alui .sub .rax 1]) (z := after) subtractCode (by decide) rfl
      have leaf : Match L (k after.rax) after :=
        (exit.jump (yes := []) (by decide)).finish after subtractCode.2.2
        ⟨kept.pc, kept.frame, kept.table, kept.mode⟩
      exact (congrArg (fun value => Match L (k value) after) output).mp leaf

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
    let selected := choiceTaken z .b (intClamp format)
    have leaf := truncate (x := selected) format exit
      (fpChoose_yes_code placed (by cases format <;> decide))
      ⟨kept.pc, kept.frame, kept.table, kept.mode⟩
    have request : Runner.fp (.truncateInt64 format) selected.rax 0 k =
        Runner.fp (.truncateInt64 format) value 0 k := by
      change Runner.fp (.truncateInt64 format) z.rax 0 k = _
      rw [rax, input]
      cases format <;> simp only [FPFormat.scalarBits, Runner.fp,
        NativeFPOp.inputs, fpLow32_idem]
    exact (congrArg (fun tree => Match L tree selected) request).mp leaf
  | false =>
    simp only [within, Bool.false_eq_true, ↓reduceIte]
    apply fpChoose_false placed (by simp only [Cond.eval, actualFlag, within])
    let selected := choiceFallthrough z .b (intClamp format)
    let rest := [.jmp (BitVec.ofNat 32 (lenOf (fpTruncateBody format)))] ++
      fpTruncateBody format ++ tail
    have selectedCode : Code L.C selected.rip (intClamp format ++ rest) := by
      simpa only [selected, choiceFallthrough, rest, List.append_assoc] using fpChoose_no_code placed
    have selectedExit : Exit L t rest k :=
      exit.jump (yes := fpTruncateBody format) (by cases format <;> decide)
    have leaf := clamp_match (x := selected) format selectedExit selectedCode
      ⟨kept.pc, kept.frame, kept.table, kept.mode⟩
    have output : (if fpNegative format selected.rax then
        (0x8000000000000000 : W) else 0x7FFFFFFFFFFFFFFF) =
        (if fpNegative format value then 0x8000000000000000 else 0x7FFFFFFFFFFFFFFF) := by
      change (if fpNegative format z.rax then _ else _) = _
      rw [rax, input, negative_scalar]
    exact (congrArg (fun word => Match L (k word) selected) output).mp leaf

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
    let selected := choiceTaken z .b (intFinite format)
    have leaf := word_constant (x := selected) exit (0#32)
      (fpChoose_yes_code placed (by cases format <;> decide))
      ⟨kept.pc, kept.frame, kept.table, kept.mode⟩
    exact (congrArg (fun word => Match L (k word) selected) sx32_zero).mp leaf
  | false =>
    simp only [fpToInt64, nan, Bool.false_eq_true, ↓reduceIte]
    apply fpChoose_false placed (by simp only [Cond.eval, classified.nan, nan])
    let selected := choiceFallthrough z .b (intFinite format)
    let rest := [.jmp (BitVec.ofNat 32 (lenOf [.movi .rax 0]))] ++ [.movi .rax 0] ++ tail
    have selectedCode : Code L.C selected.rip (intFinite format ++ rest) := by
      simpa only [selected, choiceFallthrough, rest, List.append_assoc] using fpChoose_no_code placed
    have selectedExit : Exit L t rest k := exit.jump (yes := [.movi .rax 0]) (by decide)
    exact finite_match (x := selected) format x.rax selectedExit selectedCode
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
