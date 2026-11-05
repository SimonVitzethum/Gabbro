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

/-- One signed conversion, optionally doubled by its actual ADD instruction.
    Both the arbitrary answer and refusal of each request are retained. -/
private theorem integer_match {L : Lay} {t : IR.T} {x : X} {tail : List Ins}
    {k : W → Res IR.T} (format : FPFormat) (twice : Bool) (exit : Exit L t tail k)
    (code : Code L.C x.rip (integerBody format twice ++ tail)) (controls : Controls L t x) :
    Match L (Runner.fp (.fromInt64 format) x.rax 0 fun value =>
      if twice then Runner.fp (.add format) value value k else k value) x := by
  let converted (value : W) : X :=
    ({ x with rip := (x.rip + BitVec.ofNat 64
      (enc (.fromIntScalar format .xmm0 .rax)).length) }).setScalar format .xmm0 value
  let doubled (half value : W) : X :=
    ({ converted half with rip := ((converted half).rip + BitVec.ofNat 64
      (enc (.scalar .add format .xmm0 .xmm0)).length) }).setScalar format .xmm0 value
  let after (half value : W) : X :=
    let before := if twice then doubled half value else converted value
    ({ before with rip := (before.rip + BitVec.ofNat 64
      (enc (.movFromXmm format .rax .xmm0)).length) }).set .rax (before.xmmWord format .xmm0)
  let fromWord (value : W) := (NativeFPOp.fromInt64 format).resultWord value
  let addWord (value : W) := (NativeFPOp.add format).resultWord value
  have fromNormalized (value : W) : format.scalarBits (fromWord value) = fromWord value := by
    cases format <;> simp only [fromWord, NativeFPOp.resultWord, FPFormat.scalarBits, fpLow32_idem]
  have addNormalized (value : W) : format.scalarBits (addWord value) = addWord value := by
    cases format <;> simp only [addWord, NativeFPOp.resultWord, FPFormat.scalarBits, fpLow32_idem]
  have position (half value : W) :
      (after half value).rip = x.rip + BitVec.ofNat 64 (lenOfL (integerBody format twice)) := by
    cases twice
    all_goals
      simp only [after, Bool.false_eq_true, ↓reduceIte, set_rip, converted, doubled, setScalar_rip]
      simp [integerBody, lenOfL, BitVec.ofNat_add, BitVec.add_assoc]
  have output (half value : W) : (after half value).rax = format.scalarBits value := by
    cases twice <;> cases format <;>
      simp only [after, Bool.false_eq_true, ↓reduceIte, X.set, converted, doubled,
        xmmWord_setScalar, FPFormat.scalarBits]
  have kept (half value : W) : Controls L t (after half value) := by
    cases twice <;> cases format <;>
      exact ⟨controls.pc, controls.frame, controls.table, controls.mode⟩
  have placed := code_append code
  have finish (half value : W) (normalized : format.scalarBits value = value) :
      Match L (k value) (after half value) := by
    have continuationCode : Code L.C (after half value).rip tail := by
      rw [position]
      exact placed
    have leaf := exit.finish (after half value) continuationCode (kept half value)
    have actual : (after half value).rax = value := (output half value).trans normalized
    exact (congrArg (fun word => Match L (k word) (after half value)) actual).mp leaf
  apply go (integerBody format twice) x _ (by cases twice <;> cases format <;> decide) (code_prefix code)
  have ready := controls.mode
  simp only [X.fpReady, beq_iff_eq] at ready
  cases twice with
  | false =>
    cases format
    all_goals
      simp only [integerBody, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append]
      fp_reduce ready
      repeat (first
        | (apply corrM_ask; intro _; fp_reduce ready)
        | (apply corrM_opt; intro _; fp_reduce ready)
        | (rw [runL]; fp_reduce ready))
      rename_i _ value
      simp only [CorrM]
      change Match L (k (fromWord value.1)) (after 0 (fromWord value.1))
      exact finish 0 (fromWord value.1) (fromNormalized value.1)
  | true =>
    cases format
    all_goals
      simp only [integerBody, ↓reduceIte, List.cons_append, List.nil_append]
      fp_reduce ready
      repeat (first
        | (apply corrM_ask; intro _; fp_reduce ready)
        | (apply corrM_opt; intro _; fp_reduce ready)
        | (rw [runL]; fp_reduce ready))
      rename_i _ half _ value
      simp only [CorrM]
      change Match L (k (addWord value.1)) (after (fromWord half.1) (addWord value.1))
      exact finish (fromWord half.1) (addWord value.1) (addNormalized value.1)

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

private theorem body_match {L : Lay} {t : IR.T} {x : X} {tail : List Ins}
    {k : W → Res IR.T} (format : FPFormat) (exit : Exit L t tail k)
    (code : Code L.C x.rip
      ([.alu .test .rax .rax] ++ (fpChoose .s (fpFromUIntHigh format) (fpFromIntBody format) ++ tail)))
    (controls : Controls L t x) : Match L (fpFromUInt64 format x.rax k) x := by
  let z := aluStep { x with rip := (x.rip + BitVec.ofNat 64 (enc (.alu .test .rax .rax)).length) }
    .test .rax x.rax
  have flag : Cond.eval z .s = some x.rax.msb := by
    simp only [Cond.eval, z, aluStep, X.get, BitVec.and_self]
  have placed : Code L.C z.rip
      (fpChoose .s (fpFromUIntHigh format) (fpFromIntBody format) ++ tail) := code.2.2
  have kept : Controls L t z := ⟨controls.pc, controls.frame, controls.table, controls.mode⟩
  apply pure_match (body := [.alu .test .rax .rax]) (z := z) code (by decide) rfl
  cases signed : x.rax.msb with
  | true =>
    simp only [fpFromUInt64, signed, ↓reduceIte]
    apply fpChoose_true placed (by simpa only [signed] using flag)
    exact high_match format exit
      (fpChoose_yes_code placed (by cases format <;> decide))
      ⟨kept.pc, kept.frame, kept.table, kept.mode⟩
  | false =>
    simp only [fpFromUInt64, signed, Bool.false_eq_true, ↓reduceIte]
    apply fpChoose_false placed (by simpa only [signed] using flag)
    have selectedCode : Code L.C (choiceFallthrough z .s (fpFromIntBody format)).rip
        (integerBody format false ++ (.jmp (BitVec.ofNat 32 (lenOf (fpFromUIntHigh format))) ::
          fpFromUIntHigh format ++ tail)) := by
      simpa only [integerBody, Bool.false_eq_true, ↓reduceIte, fpFromIntBody,
        List.cons_append, List.nil_append, List.append_assoc] using fpChoose_no_code placed
    have leaf : Match L (Runner.fp (.fromInt64 format)
        (choiceFallthrough z .s (fpFromIntBody format)).rax 0 k)
        (choiceFallthrough z .s (fpFromIntBody format)) := integer_match format false
      (exit.jump (yes := fpFromUIntHigh format) (by cases format <;> decide)) selectedCode
      ⟨kept.pc, kept.frame, kept.table, kept.mode⟩
    exact leaf

/-- All original operand reads, portable arms, destination requests and dispatch
    are composed from the certified joins at the same actual states. -/
theorem fp_fromUInt64_body {L : Lay} {y : X} (format : FPFormat)
    (htb : y.r14 = L.T) (hmode : y.fpReady = true) (hc : Code L.C y.rip (fpFromUIntH format)) :
    Match L (IR.f2 ⟨y.r12, y.r13⟩ fun a => IR.ld ⟨y.r12, y.r13⟩ a fun va =>
      IR.f3 ⟨y.r12, y.r13⟩ fun b => IR.ld ⟨y.r12, y.r13⟩ b fun _ =>
      fpFromUInt64 format va fun result => IR.ret1 ⟨y.r12, y.r13⟩ result) y := by
  apply read_body ([.alu .test .rax .rax] ++
    fpChoose .s (fpFromUIntHigh format) (fpFromIntBody format)) (fpFromUInt64 format) htb hmode hc
  intro x controls code
  exact body_match format (store_exit L _) (by simpa only [List.append_assoc] using code) controls

end Runner.Beweis
