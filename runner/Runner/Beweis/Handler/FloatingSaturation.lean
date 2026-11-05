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
  { x with rip := (x.rip + BitVec.ofNat 64
      (enc (.jcc condition (BitVec.ofNat 32 (lenOf no + lenOf [.jmp 0])))).length +
      sx32 (BitVec.ofNat 32 (lenOf no + lenOf [.jmp 0]))) }

abbrev choiceFallthrough (x : X) (condition : Cond) (no : List Ins) : X :=
  { x with rip := (x.rip + BitVec.ofNat 64
      (enc (.jcc condition (BitVec.ofNat 32 (lenOf no + lenOf [.jmp 0])))).length) }

theorem Exit.jump {L : Lay} {t : IR.T} {tail yes : List Ins} {k : W → Res IR.T}
    (exit : Exit L t tail k) (small : lenOf yes < 2 ^ 31) :
    Exit L t (.jmp (BitVec.ofNat 32 (lenOf yes)) :: yes ++ tail) k := by
  constructor
  intro x code controls
  let joined : X := { x with rip := (x.rip + BitVec.ofNat 64
    (enc (.jmp (BitVec.ofNat 32 (lenOf yes)))).length +
    sx32 (BitVec.ofNat 32 (lenOf yes))) }
  refine .priv ((step_code code).trans rfl) ?_
  exact exit.finish joined (fpChoose_join_code code small)
    ⟨controls.pc, controls.frame, controls.table, controls.mode⟩

theorem pure_match {L : Lay} {x z : X} {body tail : List Ins} {r : Res IR.T}
    (code : Code L.C x.rip (body ++ tail))
    (fall : ∀ i ∈ body, Fall i = true) (run : runL body x = .next z)
    (next : Match L r z) : Match L r x := by
  have falling : ∀ i ∈ body.dropLast, Fall i = true := by
    intro i hi
    exact fall i (List.dropLast_subset body hi)
  have continued : CorrM L r (runL body x) := by
    simpa only [run, CorrM] using next
  exact go body x r falling (code_prefix code) continued

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
  have falling : ∀ i ∈ [.movi .rax value], Fall i = true := by
    intro i hi
    have same : i = .movi .rax value := List.mem_singleton.mp hi
    subst i
    rfl
  apply pure_match (body := [.movi .rax value]) (z := z) code falling rfl
  exact exit.finish z code.2.2
    ⟨controls.pc, controls.frame, controls.table, controls.mode⟩

/-- Primitive leaves consume arbitrary/refused answers before entering their
    continuation. No NativeFPEval or hardware premise is used here. -/
theorem truncate {L : Lay} {t : IR.T} {x : X} {tail : List Ins} {k : W → Res IR.T}
    (format : FPFormat) (exit : Exit L t tail k)
    (code : Code L.C x.rip (fpTruncateBody format ++ tail)) (controls : Controls L t x) :
    Match L (Runner.fp (.truncateInt64 format) x.rax 0 k) x := by
  let loaded : X := ({ x with rip := (x.rip + BitVec.ofNat 64
    (enc (.movToXmm format .xmm0 .rax)).length) }).setXmm .xmm0
      (match format with
        | .f32 => (x.rax.setWidth 32).setWidth 128
        | .f64 => x.rax.setWidth 128)
  let after (value : W) : X := ({ loaded with rip := (loaded.rip + BitVec.ofNat 64
    (enc (.truncateScalar format .rax .xmm0)).length) }).set .rax value
  have position (value : W) :
      (after value).rip = x.rip + BitVec.ofNat 64 (lenOfL (fpTruncateBody format)) := by
    dsimp only [after, loaded, X.set, X.setXmm]
    simp [fpTruncateBody, lenOfL, BitVec.ofNat_add, BitVec.add_assoc]
  have controlsAfter (value : W) : Controls L t (after value) :=
    ⟨controls.pc, controls.frame, controls.table, controls.mode⟩
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
    change Match L (k result.1) (after result.1)
    have continuationCode : Code L.C (after result.1).rip tail := by
      rw [position]
      exact placed
    exact exit.finish (after result.1) continuationCode (controlsAfter result.1)

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
  rename_i _ fieldA _ valueA _ fieldB _ valueB
  simp only [CorrM]
  -- Retain the actual four instruction advances in the continuation state.
  -- Only its separate RIP certificate reassociates the address additions.
  let after : X := { y with
    rax := valueA.1
    rdx := valueB.1
    rip := (((y.rip + BitVec.ofNat 64 (enc (fld .rax 2)).length) +
      BitVec.ofNat 64 (enc (sld .rax .rax)).length) +
      BitVec.ofNat 64 (enc (fld .rdx 3)).length) +
      BitVec.ofNat 64 (enc (sld .rdx .rdx)).length }
  change Match L (convert valueA.1 (IR.ret1 ⟨y.r12, y.r13⟩)) after
  have position : after.rip = y.rip + BitVec.ofNat 64 (lenOfL first) := by
    dsimp only [after]
    simp [first, lenOfL, BitVec.ofNat_add, BitVec.add_assoc]
  have continuationCode : Code L.C after.rip
      (body ++ [fld .rcx 1, sst .rcx .rax, .alui .add .r12 16] ++ dispatch) := by
    rw [position]
    exact placed
  have controlsAfter : Controls L ⟨y.r12, y.r13⟩ after := ⟨rfl, rfl, table, mode⟩
  exact body_ok after controlsAfter continuationCode

end Runner.Beweis.FPSaturation
