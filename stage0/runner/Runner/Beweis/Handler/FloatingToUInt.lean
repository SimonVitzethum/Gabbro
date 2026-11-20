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

private abbrev highLoad (format : FPFormat) : List Ins :=
  [.movToXmm format .xmm0 .rax] ++ fpLimit .rdx format false ++ [.movToXmm format .xmm1 .rdx]

private abbrev highOr : List Ins :=
  fpSignMask .rdx .f64 ++ [.alu .or .rax .rdx]

/-- Both physical input lanes are prepared without opening a request tree.
    Its actual state, rather than an address-normalized record, is retained. -/
private theorem high_load (format : FPFormat) (before : X) :
    ∃ after, runL (highLoad format) before = .next after ∧
      after.rip = before.rip + BitVec.ofNat 64 (lenOfL (highLoad format)) ∧
      after.xmmWord format .xmm0 = format.scalarBits before.rax ∧
      after.xmmWord format .xmm1 = format.int64Limit ∧
      after.r12 = before.r12 ∧ after.r13 = before.r13 ∧ after.r14 = before.r14 ∧
      after.fpReady = before.fpReady := by
  let advance (i : Ins) (x : X) : X :=
    { x with rip := (x.rip + BitVec.ofNat 64 (enc i).length) }
  let loaded := (advance (.movToXmm format .xmm0 .rax) before).setXmm .xmm0
    (match format with
      | .f32 => (before.rax.setWidth 32).setWidth 128
      | .f64 => before.rax.setWidth 128)
  let limited : X := match format with
    | .f32 => (advance (.movi .rdx 0x5F000000) loaded).set .rdx (sx32 0x5F000000)
    | .f64 =>
      let upper := (advance (.movi .rdx 0x43E0) loaded).set .rdx (sx32 0x43E0)
      let amount := (advance (.movi .rcx 48) upper).set .rcx (sx32 48)
      ((advance (.shl .rdx) amount).set .rdx (amount.rdx <<< (amount.rcx.toNat % 64))).nof
  let after := (advance (.movToXmm format .xmm1 .rdx) limited).setXmm .xmm1
    (match format with
      | .f32 => (limited.rdx.setWidth 32).setWidth 128
      | .f64 => limited.rdx.setWidth 128)
  have run : runL (highLoad format) before = .next after := by
    cases format <;> rfl
  have position : after.rip = before.rip + BitVec.ofNat 64 (lenOfL (highLoad format)) := by
    cases format
    all_goals
      dsimp only [after, limited, loaded, advance, X.set, X.setXmm, X.nof]
      simp [highLoad, fpLimit, fpUpper, lenOfL, BitVec.ofNat_add, BitVec.add_assoc]
  refine ⟨after, run, position, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    cases format
    all_goals
      dsimp only [after, limited, loaded, advance, X.set, X.setXmm, X.xmmWord, X.nof, X.fpReady]
  all_goals
    simp (disch := decide) [FPFormat.scalarBits, FPFormat.int64Limit, fpLow32,
      BitVec.setWidth_setWidth_of_le, sx32_ofNat]

/-- The integer OR suffix is independent of either preceding FP answer. -/
private theorem high_or (before : X) :
    ∃ after, runL highOr before = .next after ∧
      after.rip = before.rip + BitVec.ofNat 64 (lenOfL highOr) ∧
      after.rax = before.rax ||| 0x8000000000000000 ∧
      after.r12 = before.r12 ∧ after.r13 = before.r13 ∧ after.r14 = before.r14 ∧
      after.fpReady = before.fpReady := by
  let advance (i : Ins) (x : X) : X :=
    { x with rip := (x.rip + BitVec.ofNat 64 (enc i).length) }
  let one := (advance (.movi .rdx 1) before).set .rdx (sx32 1)
  let counted := (advance (.movi .rcx 63) one).set .rcx (sx32 63)
  let shifted := ((advance (.shl .rdx) counted).set .rdx
    (counted.rdx <<< (counted.rcx.toNat % 64))).nof
  let after := aluStep (advance (.alu .or .rax .rdx) shifted) .or .rax shifted.rdx
  have run : runL highOr before = .next after := rfl
  have position : after.rip = before.rip + BitVec.ofNat 64 (lenOfL highOr) := by
    dsimp only [after, shifted, counted, one, advance, aluStep, aluOp, X.get, X.set, X.nof]
    simp [highOr, fpSignMask, fpUpper, lenOfL, BitVec.ofNat_add, BitVec.add_assoc]
  have mask : sx32 (1#32) <<< ((sx32 (63#32)).toNat % 64) = (0x8000000000000000 : W) := by decide
  refine ⟨after, run, position, ?_, rfl, rfl, rfl, rfl⟩
  change before.rax ||| (sx32 (1#32) <<< ((sx32 (63#32)).toNat % 64)) = _
  rw [mask]

private theorem high_exit {L : Lay} {t : IR.T} {tail : List Ins} {k : W → Res IR.T}
    (exit : Exit L t tail k) :
    Exit L t (highOr ++ tail) (fun integer => k (integer ||| 0x8000000000000000)) := by
  constructor
  intro x code controls
  obtain ⟨after, run, position, output, pc, frame, table, mode⟩ := high_or x
  have placed : Code L.C after.rip tail := by
    rw [position]
    exact code_append code
  have leaf := exit.finish after placed
    ⟨pc.trans controls.pc, frame.trans controls.frame,
      table.trans controls.table, mode.trans controls.mode⟩
  have continued : Match L (k (x.rax ||| 0x8000000000000000)) after :=
    (congrArg (fun word => Match L (k word) after) output).mp leaf
  exact pure_match code (by decide) run continued

/-- Only the two adjacent native instructions enter this request reducer.
    The loader and OR states remain behind independent typed certificates. -/
private theorem sub_truncate {L : Lay} {t : IR.T} {x : X} {tail : List Ins}
    {k : W → Res IR.T} (format : FPFormat) (exit : Exit L t tail k)
    (code : Code L.C x.rip
      ([.scalar .sub format .xmm0 .xmm1, .truncateScalar format .rax .xmm0] ++ tail))
    (controls : Controls L t x) :
    Match L (Runner.fp (.sub format) (x.xmmWord format .xmm0) (x.xmmWord format .xmm1)
      fun reduced => Runner.fp (.truncateInt64 format) reduced 0 k) x := by
  let subtracted (reduced : W) : X :=
    ({ x with rip := (x.rip + BitVec.ofNat 64
      (enc (.scalar .sub format .xmm0 .xmm1)).length) }).setScalar format .xmm0 reduced
  let after (reduced integer : W) : X :=
    ({ subtracted reduced with rip := ((subtracted reduced).rip + BitVec.ofNat 64
      (enc (.truncateScalar format .rax .xmm0)).length) }).set .rax integer
  let subWord (value : W) := (NativeFPOp.sub format).resultWord value
  have position (reduced integer : W) :
      (after reduced integer).rip = x.rip + BitVec.ofNat 64
        (lenOfL [.scalar .sub format .xmm0 .xmm1, .truncateScalar format .rax .xmm0]) := by
    simp only [after, set_rip, subtracted, setScalar_rip]
    simp [lenOfL, BitVec.ofNat_add, BitVec.add_assoc]
  have kept (reduced integer : W) : Controls L t (after reduced integer) := by
    cases format <;> exact ⟨controls.pc, controls.frame, controls.table, controls.mode⟩
  have placed := code_append code
  have finish (reduced integer : W) : Match L (k integer) (after reduced integer) := by
    have continuationCode : Code L.C (after reduced integer).rip tail := by
      rw [position]
      exact placed
    exact exit.finish (after reduced integer) continuationCode (kept reduced integer)
  apply go [.scalar .sub format .xmm0 .xmm1, .truncateScalar format .rax .xmm0] x _
    (by cases format <;> decide) (code_prefix code)
  have ready := controls.mode
  simp only [X.fpReady, beq_iff_eq] at ready
  cases format
  all_goals
    fp_reduce ready
    repeat (first
      | (apply corrM_ask; intro _; fp_reduce ready)
      | (apply corrM_opt; intro _; fp_reduce ready)
      | (rw [runL]; fp_reduce ready))
    rename_i _ subtraction _ integer
    simp only [CorrM]
    change Match L (k integer.1) (after (subWord subtraction.1) integer.1)
    exact finish (subWord subtraction.1) integer.1

private theorem high_match {L : Lay} {t : IR.T} {x : X} {tail : List Ins}
    {k : W → Res IR.T} (format : FPFormat) (exit : Exit L t tail k)
    (code : Code L.C x.rip (uintHigh format ++ tail)) (controls : Controls L t x) :
    Match L (Runner.fp (.sub format) x.rax format.int64Limit fun reduced =>
      Runner.fp (.truncateInt64 format) reduced 0 fun integer =>
        k (integer ||| 0x8000000000000000)) x := by
  have complete : Code L.C x.rip (highLoad format ++
      ([.scalar .sub format .xmm0 .xmm1, .truncateScalar format .rax .xmm0] ++
        (highOr ++ tail))) := by
    simpa only [uintHigh, highLoad, highOr, List.cons_append, List.nil_append,
      List.append_assoc] using code
  obtain ⟨z, run, position, input, limit, pc, frame, table, mode⟩ := high_load format x
  have placed : Code L.C z.rip
      ([.scalar .sub format .xmm0 .xmm1, .truncateScalar format .rax .xmm0] ++
        (highOr ++ tail)) := by
    rw [position]
    exact code_append complete
  have leaf : Match L (Runner.fp (.sub format)
      (z.xmmWord format .xmm0) (z.xmmWord format .xmm1) fun reduced =>
      Runner.fp (.truncateInt64 format) reduced 0 fun integer =>
        k (integer ||| 0x8000000000000000)) z := sub_truncate format (high_exit exit) placed
    ⟨pc.trans controls.pc, frame.trans controls.frame,
      table.trans controls.table, mode.trans controls.mode⟩
  rw [input, limit] at leaf
  have request : (Runner.fp (.sub format) (format.scalarBits x.rax) format.int64Limit
      fun reduced => Runner.fp (.truncateInt64 format) reduced 0 fun integer =>
        k (integer ||| 0x8000000000000000)) =
      (Runner.fp (.sub format) x.rax format.int64Limit
      fun reduced => Runner.fp (.truncateInt64 format) reduced 0 fun integer =>
        k (integer ||| 0x8000000000000000)) := by
    cases format <;> simp only [FPFormat.scalarBits, Runner.fp, NativeFPOp.inputs, fpLow32_idem]
  rw [request] at leaf
  exact pure_match complete (by cases format <;> decide) run leaf

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
    change Match L (Runner.fp (.truncateInt64 format) value 0 k)
      (choiceTaken z .b (uintHigh format))
    have atInput : (choiceTaken z .b (uintHigh format)).rax = format.scalarBits value :=
      rax.trans input
    have request : Runner.fp (.truncateInt64 format)
        (choiceTaken z .b (uintHigh format)).rax 0 k =
        Runner.fp (.truncateInt64 format) value 0 k := by
      rw [atInput]
      cases format <;> simp only [Runner.fp, NativeFPOp.inputs, FPFormat.scalarBits, fpLow32_idem]
    rw [request] at leaf
    exact leaf
  | false =>
    simp only [within, Bool.false_eq_true, ↓reduceIte]
    apply fpChoose_false placed (by simp only [Cond.eval, actualFlag, within])
    have branchCode : Code L.C (choiceFallthrough z .b (uintHigh format)).rip
        (uintHigh format ++ (.jmp (BitVec.ofNat 32 (lenOf (fpTruncateBody format))) ::
          fpTruncateBody format ++ tail)) := by
      simpa only [choiceFallthrough, List.append_assoc, List.cons_append, List.nil_append]
        using fpChoose_no_code placed
    have leaf := high_match (x := choiceFallthrough z .b (uintHigh format)) format
      (exit.jump (yes := fpTruncateBody format) (by cases format <;> decide))
      branchCode ⟨kept.pc, kept.frame, kept.table, kept.mode⟩
    change Match L (Runner.fp (.sub format) value format.int64Limit fun reduced =>
      Runner.fp (.truncateInt64 format) reduced 0 fun integer =>
        k (integer ||| 0x8000000000000000)) (choiceFallthrough z .b (uintHigh format))
    have atInput : (choiceFallthrough z .b (uintHigh format)).rax = format.scalarBits value :=
      rax.trans input
    have request : (Runner.fp (.sub format) (choiceFallthrough z .b (uintHigh format)).rax
        format.int64Limit fun reduced => Runner.fp (.truncateInt64 format) reduced 0 fun integer =>
          k (integer ||| 0x8000000000000000)) =
        (Runner.fp (.sub format) value format.int64Limit fun reduced =>
          Runner.fp (.truncateInt64 format) reduced 0 fun integer =>
            k (integer ||| 0x8000000000000000)) := by
      rw [atInput]
      cases format <;> simp only [Runner.fp, NativeFPOp.inputs, FPFormat.scalarBits, fpLow32_idem]
    rw [request] at leaf
    exact leaf

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
    change Match L (k 0) (choiceTaken z .nz (uintPositive format))
    have leaf := word_constant
      (x := choiceTaken z .nz (uintPositive format)) exit (0 : BitVec 32)
      (fpChoose_yes_code placed (by cases format <;> decide))
      ⟨kept.pc, kept.frame, kept.table, kept.mode⟩
    simpa only [show sx32 (0 : BitVec 32) = (0 : W) from by decide] using leaf
  | false =>
    simp only [negative, Bool.false_eq_true, ↓reduceIte]
    apply fpChoose_false placed (by simpa only [negative] using actualFlag)
    have branchCode : Code L.C (choiceFallthrough z .nz (uintPositive format)).rip
        (uintPositive format ++ (.jmp (BitVec.ofNat 32 (lenOf [.movi .rax 0])) ::
          [.movi .rax 0] ++ tail)) := by
      simpa only [choiceFallthrough, List.append_assoc, List.cons_append, List.nil_append]
        using fpChoose_no_code placed
    exact positive_match (x := choiceFallthrough z .nz (uintPositive format)) format value
      (exit.jump (yes := [.movi .rax 0]) (by decide)) branchCode
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
    change Match L (k 0) (choiceTaken z .b (uintFinite format))
    have leaf := word_constant
      (x := choiceTaken z .b (uintFinite format)) exit (0 : BitVec 32)
      (fpChoose_yes_code placed (by cases format <;> decide))
      ⟨kept.pc, kept.frame, kept.table, kept.mode⟩
    simpa only [show sx32 (0 : BitVec 32) = (0 : W) from by decide] using leaf
  | false =>
    simp only [fpToUInt64, nan, Bool.false_or]
    apply fpChoose_false placed (by simp only [Cond.eval, classified.nan, nan])
    have branchCode : Code L.C (choiceFallthrough z .b (uintFinite format)).rip
        (uintFinite format ++ (.jmp (BitVec.ofNat 32 (lenOf [.movi .rax 0])) ::
          [.movi .rax 0] ++ tail)) := by
      simpa only [choiceFallthrough, List.append_assoc, List.cons_append, List.nil_append]
        using fpChoose_no_code placed
    exact finite_match (x := choiceFallthrough z .b (uintFinite format)) format x.rax
      (exit.jump (yes := [.movi .rax 0]) (by decide)) branchCode
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
