module
public import Runner.Beweis.Handler.Floating
public import Runner.Beweis.Handler.FloatingChoice
@[expose] public section

namespace Runner.Beweis
open Runner.X86 Runner.Prog

/-! Request-tree composition for the actual portable unsigned body. Numerical
    correspondence is supplied separately by the shared Std adapters; this
    theorem matches every primitive answer and every field/slot access. -/

theorem fp_fromUInt64_body {L : Lay} {y : X} (format : FPFormat)
    (htb : y.r14 = L.T) (hmode : y.fpReady = true) (hc : Code L.C y.rip (fpFromUIntH format)) :
    Match L (IR.f2 ⟨y.r12, y.r13⟩ fun a => IR.ld ⟨y.r12, y.r13⟩ a fun va =>
      IR.f3 ⟨y.r12, y.r13⟩ fun b => IR.ld ⟨y.r12, y.r13⟩ b fun _ =>
      fpFromUInt64 format va fun result => IR.ret1 ⟨y.r12, y.r13⟩ result) y := by
  let low := fpFromIntBody format
  let high := fpFromUIntHigh format
  let finish : List Ins := [fld .rcx 1, sst .rcx .rax, .alui .add .r12 16]
  let first : List Ins := [fld .rax 2, sld .rax .rax, fld .rdx 3, sld .rdx .rdx,
    .alu .test .rax .rax, .jcc .s (BitVec.ofNat 32 (lenOf low + lenOf [.jmp 0]))]
  have code : Code L.C y.rip
      (first ++ low ++ [.jmp (BitVec.ofNat 32 (lenOf high))] ++ high ++ finish ++ dispatch) := by
    simpa only [fpFromUIntH, binH, fpChoose, low, high, first, finish, nextI,
      List.cons_append, List.nil_append, List.append_assoc] using hc
  have lowCode := code_append (is := first) code
  have highCode := code_append (is := first ++ low ++ [.jmp (BitVec.ofNat 32 (lenOf high))])
    (js := high ++ finish ++ dispatch) (by simpa only [List.append_assoc] using code)
  have finishCode := code_append
    (is := first ++ low ++ [.jmp (BitVec.ofNat 32 (lenOf high))] ++ high)
    (js := finish ++ dispatch) (by simpa only [List.append_assoc] using code)
  have skipSmall : lenOf low + lenOf [.jmp 0] < 2 ^ 31 := by cases format <;> decide
  have highSmall : lenOf high < 2 ^ 31 := by cases format <;> decide
  have ready := hmode
  simp only [X.fpReady] at ready
  apply go first y _ (by decide) (code_prefix code)
  simp [IR.f2, IR.f3, IR.ld, IR.slot, fpFromUInt64, first, runL, exec, fld, sld,
    mb, ms, ea, X.get, X.set, aluStep, Cond.eval, rd64, rd32]
  repeat (first | (apply corrM_ask; intro _) | (apply corrM_opt; intro _))
  rename_i _ _ _ va _ _ _ vb
  simp only [CorrM]
  by_cases signed : va.1.msb = true
  · simp only [signed, ↓reduceIte]
    refine straight_go htb hmode (high ++ finish) _ _ (by decide) ?_ ?_
    · simpa (disch := omega) [first, low, high, finish, fpFromIntBody, fpFromUIntHigh,
        lenOfL, lenOf, enc, regEnc, memEnc, le32, BitVec.ofNat_add, BitVec.add_assoc,
        sx32_ofNat, X.set, aluStep] using highCode
    · cases format <;>
        simp only [high, fpFromUIntHigh, finish]
      all_goals fp_corr hmode
  · simp only [signed, ↓reduceIte]
    apply go (low ++ [.jmp (BitVec.ofNat 32 (lenOf high))]) _ _ (by decide)
      (code_prefix (by
        simpa [first, low, lenOfL, lenOf, enc, regEnc, memEnc, le32,
          BitVec.ofNat_add, BitVec.add_assoc, X.set, aluStep] using lowCode))
    cases format
    all_goals
      simp (disch := omega) [low, fpFromIntBody, high, fpFromUIntHigh, runL, exec,
        fpFromUInt64, Runner.fp, NativeFPOp.inputs, NativeFPOp.resultWord,
        X.fpReady, ready, X.get, X.set, X.xmmWord, X.setXmm, X.setScalar,
        fpLow32, BitVec.setWidth_setWidth_of_le]
      repeat (first | (apply corrM_ask; intro _) | (apply corrM_opt; intro _))
      simp only [CorrM]
      refine straight_go htb hmode finish _ _ (by decide) ?_ ?_
      · simpa (disch := omega) [first, low, high, finish, fpFromIntBody, fpFromUIntHigh,
          lenOfL, lenOf, enc, regEnc, memEnc, le32, BitVec.ofNat_add, BitVec.add_assoc,
          sx32_ofNat, X.get, X.set, X.setScalar, X.setXmm, X.nof, aluStep] using finishCode
      · simp only [finish]
        corr

end Runner.Beweis
