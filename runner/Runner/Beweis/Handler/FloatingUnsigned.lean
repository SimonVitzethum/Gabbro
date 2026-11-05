module
public import Runner.Beweis.Handler.Floating
public import Runner.Beweis.Handler.FloatingChoice
import Runner.Beweis.Handler.FloatingSaturation
@[expose] public section

namespace Runner.Beweis
open Runner.X86 Runner.Prog FPSaturation

/-! The portable unsigned handler is composed at actual instruction joins.
    Pure integer prefixes and the short native arm are certified separately;
    neither field reads nor destination writes enter a native arm's reducer. -/

private abbrev integerBody (format : FPFormat) (twice : Bool) : List Ins :=
  [.fromIntScalar format .xmm0 .rax] ++
    (if twice then [.scalar .add format .xmm0 .xmm0] else []) ++
      [.movFromXmm format .rax .xmm0]

/-- Match one actual native instruction before instantiating its continuation
    state. Refused answers take the same fault branch in both request trees. -/
private theorem native_step {L : Lay} {x : X} {tail : List Ins} {k : W → Res IR.T}
    (instruction : Ins) (kind : NativeFPOp) (a b : W) (after : W → X)
    (code : Code L.C x.rip (instruction :: tail))
    (execution : exec instruction (enc instruction).length x =
      Runner.fp kind a b (fun word => .next (after word)))
    (continued : ∀ raw, Match L (k (kind.resultWord raw)) (after (kind.resultWord raw))) :
    Match L (Runner.fp kind a b k) x := by
  apply go [instruction] x _ (by simp) (code_prefix code)
  simp only [runL, execution, Runner.fp, bind_ask, bind_opt, bind_next]
  apply corrM_ask
  intro answer
  apply corrM_opt
  intro result
  simpa only [CorrM] using continued result.1

/-- The scalar move preserves the exact lane word at its own instruction join. -/
private theorem scalar_move {L : Lay} {t : IR.T} {x : X} {tail : List Ins}
    {k : W → Res IR.T} (format : FPFormat) (exit : Exit L t tail k)
    (code : Code L.C x.rip (.movFromXmm format .rax .xmm0 :: tail))
    (controls : Controls L t x) : Match L (k (x.xmmWord format .xmm0)) x := by
  let after := ({ x with rip := (x.rip + BitVec.ofNat 64
    (enc (.movFromXmm format .rax .xmm0)).length) }).set .rax (x.xmmWord format .xmm0)
  have run : runL [.movFromXmm format .rax .xmm0] x = .next after := rfl
  have placed : Code L.C after.rip tail := code.2.2
  have kept : Controls L t after :=
    ⟨controls.pc, controls.frame, controls.table, controls.mode⟩
  have leaf : Match L (k (x.xmmWord format .xmm0)) after := exit.finish after placed kept
  exact pure_match (body := [.movFromXmm format .rax .xmm0]) code
    (by cases format <;> decide) run leaf

/-- Doubling consumes the saved scalar once. Its normalized answer is related
    to RAX by a word equality, without normalizing the whole machine state. -/
private theorem double_match {L : Lay} {t : IR.T} {x : X} {tail : List Ins}
    {k : W → Res IR.T} (format : FPFormat) (value : W) (exit : Exit L t tail k)
    (code : Code L.C x.rip
      (.scalar .add format .xmm0 .xmm0 :: .movFromXmm format .rax .xmm0 :: tail))
    (controls : Controls L t x) (input : x.xmmWord format .xmm0 = value) :
    Match L (Runner.fp (.add format) value value k) x := by
  let after (word : W) : X :=
    ({ x with rip := (x.rip + BitVec.ofNat 64
      (enc (.scalar .add format .xmm0 .xmm0)).length) }).setScalar format .xmm0 word
  have execution : exec (.scalar .add format .xmm0 .xmm0)
      (enc (.scalar .add format .xmm0 .xmm0)).length x =
      Runner.fp (.add format) value value (fun word => .next (after word)) := by
    simp only [exec, controls.mode, ↓reduceIte, FPArith.native, input, after]
  refine native_step (.scalar .add format .xmm0 .xmm0) (.add format)
    value value after code execution ?_
  intro raw
  let word := (NativeFPOp.add format).resultWord raw
  have placed : Code L.C (after word).rip (.movFromXmm format .rax .xmm0 :: tail) := by
    simpa only [after, setScalar_rip] using code.2.2
  have kept : Controls L t (after word) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [after, fp_scalar_pc] using controls.pc
    · simpa only [after, fp_scalar_frame] using controls.frame
    · simpa only [after, fp_scalar_table] using controls.table
    · have unchanged : (after word).fpReady = x.fpReady := by cases format <;> rfl
      exact unchanged.trans controls.mode
  have output : (after word).xmmWord format .xmm0 = word := by
    cases format <;>
      simp only [after, word, xmmWord_setScalar, NativeFPOp.resultWord, fpLow32_idem]
  have leaf := scalar_move (x := after word) format exit placed kept
  exact (congrArg (fun result => Match L (k result) (after word)) output).mp leaf

/-- One signed conversion, optionally doubled by its actual ADD instruction.
    Each request is proved at a separate, fully typed continuation state. -/
private theorem integer_match {L : Lay} {t : IR.T} {x : X} {tail : List Ins}
    {k : W → Res IR.T} (format : FPFormat) (twice : Bool) (exit : Exit L t tail k)
    (code : Code L.C x.rip (integerBody format twice ++ tail)) (controls : Controls L t x) :
    Match L (Runner.fp (.fromInt64 format) x.rax 0 fun value =>
      if twice then Runner.fp (.add format) value value k else k value) x := by
  let rest : List Ins := (if twice then [.scalar .add format .xmm0 .xmm0] else []) ++
    [.movFromXmm format .rax .xmm0]
  have complete : Code L.C x.rip (.fromIntScalar format .xmm0 .rax :: rest ++ tail) := by
    simpa only [integerBody, rest, List.cons_append, List.nil_append, List.append_assoc] using code
  let after (word : W) : X :=
    ({ x with rip := (x.rip + BitVec.ofNat 64
      (enc (.fromIntScalar format .xmm0 .rax)).length) }).setScalar format .xmm0 word
  have execution : exec (.fromIntScalar format .xmm0 .rax)
      (enc (.fromIntScalar format .xmm0 .rax)).length x =
      Runner.fp (.fromInt64 format) x.rax 0 (fun word => .next (after word)) := by
    simp only [exec, controls.mode, ↓reduceIte, X.get, after]
  refine native_step (.fromIntScalar format .xmm0 .rax) (.fromInt64 format)
    x.rax 0 after complete execution ?_
  intro raw
  let word := (NativeFPOp.fromInt64 format).resultWord raw
  have placed : Code L.C (after word).rip (rest ++ tail) := by
    simpa only [after, setScalar_rip, List.append_eq] using complete.2.2
  have kept : Controls L t (after word) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [after, fp_scalar_pc] using controls.pc
    · simpa only [after, fp_scalar_frame] using controls.frame
    · simpa only [after, fp_scalar_table] using controls.table
    · have unchanged : (after word).fpReady = x.fpReady := by cases format <;> rfl
      exact unchanged.trans controls.mode
  have output : (after word).xmmWord format .xmm0 = word := by
    cases format <;>
      simp only [after, word, xmmWord_setScalar, NativeFPOp.resultWord, fpLow32_idem]
  cases twice with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have moveCode : Code L.C (after word).rip (.movFromXmm format .rax .xmm0 :: tail) := by
      simpa only [rest, Bool.false_eq_true, ↓reduceIte, List.nil_append,
        List.cons_append] using placed
    have leaf := scalar_move (x := after word) format exit moveCode kept
    exact (congrArg (fun result => Match L (k result) (after word)) output).mp leaf
  | true =>
    simp only [↓reduceIte]
    have addCode : Code L.C (after word).rip
        (.scalar .add format .xmm0 .xmm0 :: .movFromXmm format .rax .xmm0 :: tail) := by
      simpa only [rest, ↓reduceIte, List.cons_append, List.nil_append] using placed
    exact double_match (x := after word) format word exit addCode kept output

private abbrev stickyPrefix : List Ins :=
  [.mov .rsi .rax, .alui .and .rsi 1, .movi .rcx 1, .shr .rax, .alu .or .rax .rsi]

private theorem sticky_prefix (before : X) :
    ∃ after, runL stickyPrefix before = .next after ∧
      after.rip = before.rip + BitVec.ofNat 64 (lenOfL stickyPrefix) ∧
      after.rax = uint64StickyHalf before.rax ∧
      after.r12 = before.r12 ∧ after.r13 = before.r13 ∧ after.r14 = before.r14 ∧
      after.fpReady = before.fpReady := by
  let advance (i : Ins) (x : X) : X :=
    { x with rip := (x.rip + BitVec.ofNat 64 (enc i).length) }
  let copied := (advance (.mov .rsi .rax) before).set .rsi before.rax
  let masked := aluStep (advance (.alui .and .rsi 1) copied) .and .rsi (sx32 1)
  let counted := (advance (.movi .rcx 1) masked).set .rcx (sx32 1)
  let shifted := ((advance (.shr .rax) counted).set .rax
    (counted.rax >>> (counted.rcx.toNat % 64))).nof
  let after := aluStep (advance (.alu .or .rax .rsi) shifted) .or .rax shifted.rsi
  have run : runL stickyPrefix before = .next after := rfl
  have position : after.rip = before.rip + BitVec.ofNat 64 (lenOfL stickyPrefix) := by
    dsimp only [after, shifted, counted, masked, copied, advance, aluStep, aluOp, X.set, X.get, X.nof]
    simp [stickyPrefix, lenOfL, enc, regEnc, le32, BitVec.ofNat_add, BitVec.add_assoc]
  refine ⟨after, run, position, ?_, rfl, rfl, rfl, rfl⟩
  change (before.rax >>> ((sx32 (1#32)).toNat % 64)) ||| (before.rax &&& sx32 (1#32)) = _
  exact congrArg (fun one : W => (before.rax >>> (one.toNat % 64)) ||| (before.rax &&& one))
    fp_control_immediates.1

private theorem high_match {L : Lay} {t : IR.T} {x : X} {tail : List Ins}
    {k : W → Res IR.T} (format : FPFormat) (exit : Exit L t tail k)
    (code : Code L.C x.rip (fpFromUIntHigh format ++ tail)) (controls : Controls L t x) :
    Match L (Runner.fp (.fromInt64 format) (uint64StickyHalf x.rax) 0 fun value =>
      Runner.fp (.add format) value value k) x := by
  have complete : Code L.C x.rip (stickyPrefix ++ (integerBody format true ++ tail)) := by
    simpa only [fpFromUIntHigh, stickyPrefix, integerBody, ↓reduceIte,
      List.cons_append, List.nil_append] using code
  obtain ⟨z, run, position, input, pc, frame, table, mode⟩ := sticky_prefix x
  have placed : Code L.C z.rip (integerBody format true ++ tail) := by
    rw [position]
    exact code_append complete
  have leaf : Match L (Runner.fp (.fromInt64 format) z.rax 0 fun value =>
      Runner.fp (.add format) value value k) z := integer_match format true exit placed
    ⟨pc.trans controls.pc, frame.trans controls.frame,
      table.trans controls.table, mode.trans controls.mode⟩
  rw [input] at leaf
  exact pure_match complete (by decide) run leaf

/-- Export only the actual test's scalar facts; subsequent branch proofs never
    unfold its full flag-setting record. -/
private theorem sign_test (before : X) :
    ∃ after, runL [Ins.alu .test .rax .rax] before = .next after ∧
      after.rip = before.rip + BitVec.ofNat 64 (enc (Ins.alu .test .rax .rax)).length ∧
      Cond.eval after .s = some before.rax.msb ∧ after.rax = before.rax ∧
      after.r12 = before.r12 ∧ after.r13 = before.r13 ∧ after.r14 = before.r14 ∧
      after.fpReady = before.fpReady := by
  let after := aluStep { before with rip := (before.rip +
    BitVec.ofNat 64 (enc (Ins.alu .test .rax .rax)).length) } .test .rax before.rax
  refine ⟨after, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  simp only [Cond.eval, after, aluStep, X.get, BitVec.and_self]

private theorem body_match {L : Lay} {t : IR.T} {x : X} {tail : List Ins}
    {k : W → Res IR.T} (format : FPFormat) (exit : Exit L t tail k)
    (code : Code L.C x.rip
      ([Ins.alu .test .rax .rax] ++ (fpChoose .s (fpFromUIntHigh format) (fpFromIntBody format) ++ tail)))
    (controls : Controls L t x) : Match L (fpFromUInt64 format x.rax k) x := by
  obtain ⟨z, run, position, flag, input, pc, frame, table, mode⟩ := sign_test x
  have placed : Code L.C z.rip
      (fpChoose .s (fpFromUIntHigh format) (fpFromIntBody format) ++ tail) := by
    rw [position]
    exact code.2.2
  have kept : Controls L t z :=
    ⟨pc.trans controls.pc, frame.trans controls.frame,
      table.trans controls.table, mode.trans controls.mode⟩
  apply pure_match (body := [Ins.alu .test .rax .rax]) (z := z) code (by decide) run
  cases signed : x.rax.msb with
  | true =>
    simp only [fpFromUInt64, signed, ↓reduceIte]
    let selected : X := choiceTaken z .s (fpFromIntBody format)
    have selectedCode : Code L.C selected.rip (fpFromUIntHigh format ++ tail) :=
      fpChoose_yes_code placed (by cases format <;> decide)
    have selectedControls : Controls L t selected :=
      ⟨kept.pc, kept.frame, kept.table, kept.mode⟩
    have selectedInput : selected.rax = x.rax := input
    have leaf : Match L (Runner.fp (.fromInt64 format) (uint64StickyHalf selected.rax) 0
        fun value => Runner.fp (.add format) value value k) selected :=
      high_match (x := selected) format exit selectedCode selectedControls
    have request : (Runner.fp (.fromInt64 format) (uint64StickyHalf selected.rax) 0
        fun value => Runner.fp (.add format) value value k) =
        (Runner.fp (.fromInt64 format) (uint64StickyHalf x.rax) 0
          fun value => Runner.fp (.add format) value value k) := by
      rw [selectedInput]
    have continued := (congrArg (fun tree => Match L tree selected) request).mp leaf
    exact fpChoose_true placed (by simpa only [signed] using flag) continued
  | false =>
    simp only [fpFromUInt64, signed, Bool.false_eq_true, ↓reduceIte]
    let selected : X := choiceFallthrough z .s (fpFromIntBody format)
    have selectedCode : Code L.C selected.rip
        (integerBody format false ++ (.jmp (BitVec.ofNat 32 (lenOf (fpFromUIntHigh format))) ::
          fpFromUIntHigh format ++ tail)) := by
      simpa only [selected, choiceFallthrough, integerBody, Bool.false_eq_true, ↓reduceIte, fpFromIntBody,
        List.cons_append, List.nil_append, List.append_assoc] using fpChoose_no_code placed
    have selectedControls : Controls L t selected :=
      ⟨kept.pc, kept.frame, kept.table, kept.mode⟩
    have selectedInput : selected.rax = x.rax := input
    have leaf : Match L (Runner.fp (.fromInt64 format) selected.rax 0 k) selected :=
      integer_match (x := selected) format false
        (exit.jump (yes := fpFromUIntHigh format) (by cases format <;> decide))
        selectedCode selectedControls
    have request : Runner.fp (.fromInt64 format) selected.rax 0 k =
        Runner.fp (.fromInt64 format) x.rax 0 k := by rw [selectedInput]
    have continued := (congrArg (fun tree => Match L tree selected) request).mp leaf
    exact fpChoose_false placed (by simpa only [signed] using flag) continued

/-- All original operand reads, portable arms, destination requests and dispatch
    are composed from the certified joins at the same actual states. -/
theorem fp_fromUInt64_body {L : Lay} {y : X} (format : FPFormat)
    (htb : y.r14 = L.T) (hmode : y.fpReady = true) (hc : Code L.C y.rip (fpFromUIntH format)) :
    Match L (IR.f2 ⟨y.r12, y.r13⟩ fun a => IR.ld ⟨y.r12, y.r13⟩ a fun va =>
      IR.f3 ⟨y.r12, y.r13⟩ fun b => IR.ld ⟨y.r12, y.r13⟩ b fun _ =>
      fpFromUInt64 format va fun result => IR.ret1 ⟨y.r12, y.r13⟩ result) y := by
  let body : List Ins := [Ins.alu .test .rax .rax] ++
    fpChoose .s (fpFromUIntHigh format) (fpFromIntBody format)
  have complete : Code L.C y.rip (binH body) := by
    simpa only [fpFromUIntH, body] using hc
  apply read_body body (fpFromUInt64 format) htb hmode complete
  intro x controls code
  have placed : Code L.C x.rip
      ([Ins.alu .test .rax .rax] ++
        (fpChoose .s (fpFromUIntHigh format) (fpFromIntBody format) ++
          ([fld .rcx 1, sst .rcx .rax, .alui .add .r12 16] ++ dispatch))) := by
    simpa only [body, List.append_assoc] using code
  exact body_match (x := x) format (store_exit L _) placed controls

end Runner.Beweis
