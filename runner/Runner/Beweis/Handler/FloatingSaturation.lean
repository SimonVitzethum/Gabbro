module
public import Runner.Beweis.Handler.Floating
public import Runner.Beweis.Handler.FloatingChoice
public import Runner.Beweis.Handler.FloatingGuards
@[expose] public section

namespace Runner.Beweis.FPSaturation
open Runner.X86 Runner.Prog

/-! Proof continuations for the existing saturation byte sequences. The only
    executable objects here are the original instruction lists and request
    trees. An Exit records the actual code and protected controls at a join. -/

structure Controls (L : Lay) (t : IR.T) (x : X) : Prop where
  pc : x.r12 = t.pc
  frame : x.r13 = t.fp
  table : x.r14 = L.T
  mode : x.fpReady = true

structure Exit (L : Lay) (t : IR.T) (tail : List Ins) (k : W → Res IR.T) : Prop where
  finish : ∀ x, Code L.C x.rip tail → Controls L t x → Match L (k x.rax) x

/-- State terms at the two targets in the existing fpChoose code lemmas. -/
abbrev choiceTaken (x : X) (condition : Cond) (no : List Ins) : X :=
  { x with rip := x.rip + BitVec.ofNat 64
      (enc (.jcc condition (BitVec.ofNat 32 (lenOf no + lenOf [.jmp 0])))).length +
      sx32 (BitVec.ofNat 32 (lenOf no + lenOf [.jmp 0])) }

abbrev choiceFallthrough (x : X) (condition : Cond) (no : List Ins) : X :=
  { x with rip := x.rip + BitVec.ofNat 64
      (enc (.jcc condition (BitVec.ofNat 32 (lenOf no + lenOf [.jmp 0])))).length }

theorem Exit.jump {L : Lay} {t : IR.T} {tail yes : List Ins} {k : W → Res IR.T}
    (exit : Exit L t tail k) (small : lenOf yes < 2 ^ 31) :
    Exit L t (.jmp (BitVec.ofNat 32 (lenOf yes)) :: yes ++ tail) k := by
  constructor
  intro x code controls
  refine .priv ((step_code code).trans rfl) ?_
  exact exit.finish _ (fpChoose_join_code code small)
    ⟨controls.pc, controls.frame, controls.table, controls.mode⟩

theorem pure_match {L : Lay} {x z : X} {body tail : List Ins} {r : Res IR.T}
    (code : Code L.C x.rip (body ++ tail))
    (fall : ∀ i ∈ body, Fall i = true) (run : runL body x = .next z)
    (next : Match L r z) : Match L r x := by
  apply go body x r ?_ (code_prefix code)
  · intro i hi
    exact fall i (List.dropLast_subset body hi)
  · simpa only [run, CorrM] using next

theorem scalar_idempotent (format : FPFormat) (value : W) :
    format.scalarBits (format.scalarBits value) = format.scalarBits value := by
  cases format <;> simp only [FPFormat.scalarBits, fpLow32_idem]

theorem magnitude_scalar (format : FPFormat) (value : W) :
    fpMagnitude format (format.scalarBits value) = fpMagnitude format value := by
  simp only [fpMagnitude, scalar_idempotent]

theorem negative_scalar (format : FPFormat) (value : W) :
    fpNegative format (format.scalarBits value) = fpNegative format value := by
  simp only [fpNegative, scalar_idempotent]

theorem nan_scalar (format : FPFormat) (value : W) :
    fpNaN format (format.scalarBits value) = fpNaN format value := by
  simp only [fpNaN, magnitude_scalar]

/-- Every result write, including a refused field read or write, is shared
    with the source request tree. The successor has the established FP mode. -/
theorem store_exit (L : Lay) (t : IR.T) :
    Exit L t ([fld .rcx 1, sst .rcx .rax, .alui .add .r12 16] ++ dispatch)
      (IR.ret1 t) := by
  constructor
  intro x code controls
  refine straight_go controls.table controls.mode
    [fld .rcx 1, sst .rcx .rax, .alui .add .r12 16] x _ (by decide) code ?_
  simp only [IR.ret1, IR.f1, IR.nxt]
  rw [← controls.pc, ← controls.frame]
  corr

/-- A constant leaf falls through into the supplied actual join. -/
theorem word_constant {L : Lay} {t : IR.T} {x : X} {tail : List Ins} {k : W → Res IR.T}
    (exit : Exit L t tail k) (value : BitVec 32)
    (code : Code L.C x.rip (.movi .rax value :: tail)) (controls : Controls L t x) :
    Match L (k (sx32 value)) x := by
  let z := ({ x with rip := x.rip + BitVec.ofNat 64 (enc (.movi .rax value)).length }).set .rax (sx32 value)
  apply pure_match (body := [.movi .rax value]) code (by decide) rfl
  exact exit.finish z code.2.2
    ⟨controls.pc, controls.frame, controls.table, controls.mode⟩

/-- Primitive leaves consume arbitrary/refused answers before entering their
    continuation. No NativeFPEval or hardware premise is used here. -/
theorem truncate {L : Lay} {t : IR.T} {x : X} {tail : List Ins} {k : W → Res IR.T}
    (format : FPFormat) (exit : Exit L t tail k)
    (code : Code L.C x.rip (fpTruncateBody format ++ tail)) (controls : Controls L t x) :
    Match L (Runner.fp (.truncateInt64 format) x.rax 0 k) x := by
  have placed := code_append code
  apply go (fpTruncateBody format) x _ (by cases format <;> decide) (code_prefix code)
  have ready := controls.mode
  simp only [X.fpReady, beq_iff_eq] at ready
  cases format
  all_goals
    simp only [fpTruncateBody, runL, exec, bind_next]
    fp_reduce ready
    apply corrM_ask
    intro answer
    apply corrM_opt
    intro result
    simp only [bind_next, runL, CorrM]
    apply exit.finish
    · simpa (disch := decide) [fpTruncateBody, lenOfL, enc, regEnc,
        BitVec.ofNat_add, BitVec.add_assoc, X.set, X.setXmm, X.setScalar] using placed
    · exact ⟨controls.pc, controls.frame, controls.table, controls.mode⟩

/-- The shared operand prefix reads both fields and full words, in their
    original order, before a saturation body is entered. -/
theorem read_body {L : Lay} {y : X} (body : List Ins)
    (convert : W → (W → Res IR.T) → Res IR.T)
    (table : y.r14 = L.T) (mode : y.fpReady = true)
    (code : Code L.C y.rip (binH body))
    (body_ok : ∀ x, Controls L ⟨y.r12, y.r13⟩ x →
      Code L.C x.rip
        (body ++ [fld .rcx 1, sst .rcx .rax, .alui .add .r12 16] ++ dispatch) →
      Match L (convert x.rax (IR.ret1 ⟨y.r12, y.r13⟩)) x) :
    Match L (IR.f2 ⟨y.r12, y.r13⟩ fun a => IR.ld ⟨y.r12, y.r13⟩ a fun va =>
      IR.f3 ⟨y.r12, y.r13⟩ fun b => IR.ld ⟨y.r12, y.r13⟩ b fun _ =>
      convert va (IR.ret1 ⟨y.r12, y.r13⟩)) y := by
  let first := [fld .rax 2, sld .rax .rax, fld .rdx 3, sld .rdx .rdx]
  have complete : Code L.C y.rip
      (first ++ (body ++ [fld .rcx 1, sst .rcx .rax, .alui .add .r12 16] ++ dispatch)) := by
    simpa only [first, binH, nextI, List.cons_append, List.nil_append, List.append_assoc] using code
  have placed : Code L.C (y.rip + BitVec.ofNat 64 (lenOfL first))
      (body ++ [fld .rcx 1, sst .rcx .rax, .alui .add .r12 16] ++ dispatch) := code_append complete
  apply go first y _ (by decide) (code_prefix complete)
  simp [IR.f2, IR.f3, IR.ld, IR.slot, first, runL, exec, fld, sld, mb, ms,
    ea, X.get, X.set, rd64, rd32]
  repeat (first | (apply corrM_ask; intro _) | (apply corrM_opt; intro _))
  simp only [CorrM]
  apply body_ok _ ⟨rfl, rfl, table, mode⟩
  simpa [first, lenOfL, enc, memEnc, regEnc, le32, BitVec.ofNat_add,
    BitVec.add_assoc, X.set] using placed

end Runner.Beweis.FPSaturation
