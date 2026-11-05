module
public import Runner.Beweis.Handler.FloatingWords
import Runner.Beweis.Handler.Floating
import Runner.Beweis.Handler.Sprung
import Runner.Beweis.Handler.FloatingSaturation
@[expose] public section

namespace Runner.Beweis
open Runner.X86 Runner.Prog

/-! NEG and finite classification are total integer codecs. The physical body
    makes only the original field/slot reads and destination write, never a
    floating request or an assumed hardware callback. -/

private abbrev negPrefix (format : FPFormat) : List Ins :=
  fpNormalizeInput format ++ fpSignMask .rdx format ++ [.alu .xor .rax .rdx]

/-- NEG's pure prefix is checked before any destination request is composed.
    The witness retains the actual instruction-by-instruction RIP and lanes. -/
private theorem neg_prefix (format : FPFormat) (before : X) :
    ∃ after, runL (negPrefix format) before = .next after ∧
      after.rip = before.rip + BitVec.ofNat 64 (lenOfL (negPrefix format)) ∧
      after.rax = fpNegWord format before.rax ∧
      after.r12 = before.r12 ∧ after.r13 = before.r13 ∧ after.r14 = before.r14 ∧
      after.fpReady = before.fpReady := by
  let advance (i : Ins) (x : X) : X :=
    { x with rip := (x.rip + BitVec.ofNat 64 (enc i).length) }
  let normalized : X := match format with
    | .f32 =>
      let loaded := (advance (.movToXmm .f32 .xmm0 .rax) before).setXmm .xmm0
        ((before.rax.setWidth 32).setWidth 128)
      (advance (.movFromXmm .f32 .rax .xmm0) loaded).set .rax (loaded.xmmWord .f32 .xmm0)
    | .f64 => before
  let loaded := (advance (.movi .rdx 1) normalized).set .rdx (sx32 1)
  let amount : BitVec 32 := match format with | .f32 => 31 | .f64 => 63
  let counted := (advance (.movi .rcx amount) loaded).set .rcx (sx32 amount)
  let shifted := ((advance (.shl .rdx) counted).set .rdx
    (counted.rdx <<< (counted.rcx.toNat % 64))).nof
  let after := aluStep (advance (.alu .xor .rax .rdx) shifted) .xor .rax shifted.rdx
  have run : runL (negPrefix format) before = .next after := by
    cases format <;> rfl
  have position : after.rip = before.rip + BitVec.ofNat 64 (lenOfL (negPrefix format)) := by
    cases format
    all_goals
      dsimp only [after, shifted, counted, amount, loaded, normalized, advance,
        aluStep, aluOp, X.get, X.set, X.setXmm, X.nof]
      simp [negPrefix, fpNormalizeInput, fpSignMask, fpUpper, lenOfL,
        BitVec.ofNat_add, BitVec.add_assoc]
  have mask32 : sx32 (1#32) <<< ((sx32 (31#32)).toNat % 64) = (0x80000000 : W) := by decide
  have mask64 : sx32 (1#32) <<< ((sx32 (63#32)).toNat % 64) =
      (0x8000000000000000 : W) := by decide
  refine ⟨after, run, position, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    cases format
    all_goals
      dsimp only [after, shifted, counted, amount, loaded, normalized, advance,
        aluStep, aluOp, X.get, X.set, X.setXmm, X.xmmWord, X.nof, X.fpReady]
  all_goals
    simp only [↓reduceIte, mask32, mask64, fpNegWord_word32, fpLow32,
      BitVec.setWidth_setWidth_of_le _ (k := 32) (l := 128) (by decide),
      BitVec.setWidth_eq]
  all_goals rfl

theorem fp_neg_ok {L : Lay} {y : X} (format : FPFormat)
    (h : HPre L (NativeFPOp.neg format).code y) :
    Match L (IR.op (NativeFPOp.neg format).code ⟨y.r12, y.r13⟩) y := by
  rw [IR.op_fp_neg]
  simp only [IR.fp, fpSequence]
  refine FPSaturation.read_body (negPrefix format)
    (fun word k => k (fpNegWord format word)) h.tb h.mode ?_ ?_
  · cases format <;> exact h.code
  · intro x controls code
    have complete : Code L.C x.rip (negPrefix format ++
        ([fld .rcx 1, sst .rcx .rax, .alui .add .r12 16] ++ dispatch)) := by
      simpa only [List.append_assoc] using code
    obtain ⟨after, run, position, output, pc, frame, table, mode⟩ := neg_prefix format x
    have continuationCode : Code L.C after.rip
        ([fld .rcx 1, sst .rcx .rax, .alui .add .r12 16] ++ dispatch) := by
      rw [position]
      exact code_append complete
    have kept : FPSaturation.Controls L ⟨y.r12, y.r13⟩ after :=
      ⟨pc.trans controls.pc, frame.trans controls.frame,
        table.trans controls.table, mode.trans controls.mode⟩
    have leaf := (FPSaturation.store_exit L ⟨y.r12, y.r13⟩).finish after continuationCode kept
    have continued : Match L (IR.ret1 ⟨y.r12, y.r13⟩ (fpNegWord format x.rax)) after :=
      (congrArg (fun word => Match L (IR.ret1 ⟨y.r12, y.r13⟩ word) after) output).mp leaf
    exact FPSaturation.pure_match complete (by cases format <;> decide) run continued

private abbrev finitePrefix (format : FPFormat) : List Ins :=
  fpNormalizeInput format ++ fpInfinity .rdx format ++
    [.alu .and .rax .rdx, .alu .cmp .rax .rdx]

private theorem finite_falling (format : FPFormat) :
    ∀ i ∈ finitePrefix format, Fall i = true := by
  cases format <;> decide

/-- Certify only the pure comparison prefix. The actual end state retains its
    flags and sequential RIP; its scalar certificates need no request tree. -/
private theorem finite_prefix (format : FPFormat) (before : X) :
    ∃ after, runL (finitePrefix format) before = .next after ∧
      after.rip = before.rip + BitVec.ofNat 64 (lenOfL (finitePrefix format)) ∧
      after.zf = some ((format.scalarBits before.rax &&& format.infinityBits) == format.infinityBits) ∧
      after.r12 = before.r12 ∧ after.r13 = before.r13 ∧ after.r14 = before.r14 ∧
      after.fpReady = before.fpReady := by
  let advance (i : Ins) (x : X) : X :=
    { x with rip := (x.rip + BitVec.ofNat 64 (enc i).length) }
  let normalized : X := match format with
    | .f32 =>
      let loaded : X := (advance (.movToXmm .f32 .xmm0 .rax) before).setXmm .xmm0
        ((before.rax.setWidth 32).setWidth 128)
      (advance (.movFromXmm .f32 .rax .xmm0) loaded).set .rax (loaded.xmmWord .f32 .xmm0)
    | .f64 => before
  let infinity : X := match format with
    | .f32 => (advance (.movi .rdx 0x7F800000) normalized).set .rdx (sx32 0x7F800000)
    | .f64 =>
      let loaded : X := (advance (.movi .rdx 0x7FF0) normalized).set .rdx (sx32 0x7FF0)
      let counted : X := (advance (.movi .rcx 48) loaded).set .rcx (sx32 48)
      ((advance (.shl .rdx) counted).set .rdx (counted.rdx <<< (counted.rcx.toNat % 64))).nof
  let masked : X := aluStep (advance (.alu .and .rax .rdx) infinity) .and .rax infinity.rdx
  let after : X := aluStep (advance (.alu .cmp .rax .rdx) masked) .cmp .rax masked.rdx
  have run : runL (finitePrefix format) before = .next after := by
    cases format <;> rfl
  have position : after.rip = before.rip + BitVec.ofNat 64 (lenOfL (finitePrefix format)) := by
    cases format
    all_goals
      dsimp only [after, masked, infinity, normalized, advance, aluStep, aluOp,
        X.get, X.set, X.setXmm, X.nof, X.cmpf]
      simp [finitePrefix, fpNormalizeInput, fpInfinity, fpUpper, lenOfL,
        BitVec.ofNat_add, BitVec.add_assoc]
  refine ⟨after, run, position, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    cases format
    all_goals
      dsimp only [after, masked, infinity, normalized, advance, aluStep, aluOp,
        X.get, X.set, X.setXmm, X.xmmWord, X.nof, X.cmpf, X.fpReady]
  all_goals
    simp (disch := decide) [eq_flags, FPFormat.scalarBits, FPFormat.infinityBits,
      fpLow32, BitVec.setWidth_setWidth_of_le, sx32_ofNat]

/-- SETNZ/MOVZX consumes the proven ZF without expanding the earlier states. -/
private theorem finite_boolean (before : X) (zero : Bool) (flag : before.zf = some zero) :
    ∃ after, runL [.set .nz .rax, .zx8 .rax .rax] before = .next after ∧
      after.rip = before.rip + BitVec.ofNat 64 (lenOfL [.set .nz .rax, .zx8 .rax .rax]) ∧
      after.rax = flagWord (!zero) ∧ after.r12 = before.r12 ∧ after.r13 = before.r13 ∧
      after.r14 = before.r14 ∧ after.fpReady = before.fpReady := by
  let selected : X := ({ before with rip := (before.rip +
    BitVec.ofNat 64 (enc (.set .nz .rax)).length) }).set .rax
      ((before.rax &&& ~~~(BitVec.ofNat 64 255)) ||| (if !zero then 1 else 0))
  let after : X := ({ selected with rip := (selected.rip +
    BitVec.ofNat 64 (enc (.zx8 .rax .rax)).length) }).set .rax
      ((selected.rax.setWidth 8).setWidth 64)
  have decision : Cond.eval before .nz = some (!zero) := by
    simp only [Cond.eval, flag, Option.map_some]
  have step : exec (.set .nz .rax) (enc (.set .nz .rax)).length before = .next selected := by
    simp only [exec, decision]
    rfl
  have run : runL [.set .nz .rax, .zx8 .rax .rax] before = .next after := by
    change (exec (.set .nz .rax) (enc (.set .nz .rax)).length before).bind
      (runL [.zx8 .rax .rax]) = .next after
    exact congrArg (fun tree : Res X => tree.bind (runL [.zx8 .rax .rax])) step
  have position : after.rip = before.rip +
      BitVec.ofNat 64 (lenOfL [.set .nz .rax, .zx8 .rax .rax]) := by
    dsimp only [after, selected, X.set]
    simp [lenOfL, BitVec.ofNat_add, BitVec.add_assoc]
  have output : after.rax = flagWord (!zero) := setcc_zx before.rax (!zero)
  exact ⟨after, run, position, output, rfl, rfl, rfl, rfl⟩

private theorem finite_word (format : FPFormat) (word : W) :
    flagWord (!((format.scalarBits word &&& format.infinityBits) == format.infinityBits)) =
      fpFiniteWord format word := by
  cases format
  · exact (fpFiniteWord_word32 word).symm
  · exact (fpFiniteWord_word64 word).symm

theorem fp_finite_ok {L : Lay} {y : X} (format : FPFormat)
    (h : HPre L (NativeFPOp.isFinite format).code y) :
    Match L (IR.op (NativeFPOp.isFinite format).code ⟨y.r12, y.r13⟩) y := by
  rw [IR.op_fp_finite]
  simp only [IR.fp, fpSequence]
  refine FPSaturation.read_body (finitePrefix format ++ [.set .nz .rax, .zx8 .rax .rax])
    (fun word k => k (fpFiniteWord format word)) h.tb h.mode ?_ ?_
  · cases format <;> exact h.code
  · intro x controls code
    have complete : Code L.C x.rip (finitePrefix format ++
        ([.set .nz .rax, .zx8 .rax .rax] ++
          ([fld .rcx 1, sst .rcx .rax, .alui .add .r12 16] ++ dispatch))) := by
      simpa only [List.append_assoc] using code
    obtain ⟨z, run, position, flag, pc, frame, table, mode⟩ := finite_prefix format x
    have selectedCode : Code L.C z.rip ([.set .nz .rax, .zx8 .rax .rax] ++
        ([fld .rcx 1, sst .rcx .rax, .alui .add .r12 16] ++ dispatch)) := by
      rw [position]
      exact code_append complete
    obtain ⟨after, boolRun, boolPosition, output, pc', frame', table', mode'⟩ :=
      finite_boolean z _ flag
    have afterCode : Code L.C after.rip
        ([fld .rcx 1, sst .rcx .rax, .alui .add .r12 16] ++ dispatch) := by
      rw [boolPosition]
      exact code_append selectedCode
    have afterControls : FPSaturation.Controls L ⟨y.r12, y.r13⟩ after :=
      ⟨pc'.trans (pc.trans controls.pc), frame'.trans (frame.trans controls.frame),
        table'.trans (table.trans controls.table), mode'.trans (mode.trans controls.mode)⟩
    have leaf := (FPSaturation.store_exit L ⟨y.r12, y.r13⟩).finish after afterCode afterControls
    have result : after.rax = fpFiniteWord format x.rax := output.trans (finite_word format x.rax)
    have continued : Match L (IR.ret1 ⟨y.r12, y.r13⟩ (fpFiniteWord format x.rax)) after :=
      (congrArg (fun word => Match L (IR.ret1 ⟨y.r12, y.r13⟩ word) after) result).mp leaf
    have selected := FPSaturation.pure_match selectedCode (by decide) boolRun continued
    exact FPSaturation.pure_match complete (finite_falling format) run selected

end Runner.Beweis
