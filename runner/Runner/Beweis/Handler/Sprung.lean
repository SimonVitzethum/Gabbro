import Runner.Beweis.Handler.Gerade

/-! # The handlers that branch inside: `brz` and `spawn`

The first part reads, tests and ends in a conditional jump (`go`); each branch is a straight body followed by the
dispatch (`straight_go`). `spawn`'s branch is taken on the answer of `clone`: 0 in the new thread, which takes
`pc` and `fp` from `rbx` and `rbp`; the parent stores the answer into its result slot. -/

namespace Runner.Beweis
open Runner.X86 Runner.Prog

set_option linter.unusedSimpArgs false

theorem corrM_ask {L : Lay} {o : Op} {k : Ans → Res IR.T} {k' : Ans → Res X} (h : ∀ a, CorrM L (k a) (k' a)) :
    CorrM L (.ask o k) (.ask o k') := ⟨rfl, h⟩

theorem corrM_opt {σ : Type} {L : Lay} {o : Option σ} {f : σ → Res IR.T} {g : σ → Res X}
    (h : ∀ a, CorrM L (f a) (g a)) : CorrM L (opt o f) (opt o g) := by
  cases o
  · trivial
  · exact h _

theorem sx32_ofNat {n : Nat} (h : n < 2 ^ 31) : sx32 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    simp only [BitVec.msb_eq_decide, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  rw [sx32, BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

def brzSeg : List Ins :=
  [fld .rax 1, sld .rax .rax, .alu .test .rax .rax, .jcc .nz (BitVec.ofNat 32 (lenOf brzTaken))]

theorem h19_ok {L : Lay} {y : X} (h : HPre L 19 y) : Match L (IR.op 19 ⟨y.r12, y.r13⟩) y := by
  have hc : Code L.C y.rip (brzSeg ++ (brzTaken ++ nextI)) := h.code
  have hrest := code_append hc
  have hsum : y.rip + BitVec.ofNat 64 (lenOfL brzSeg) =
      y.rip + BitVec.ofNat 64 (enc (fld .rax 1)).length + BitVec.ofNat 64 (enc (sld .rax .rax)).length +
        BitVec.ofNat 64 (enc (Ins.alu .test .rax .rax)).length +
        BitVec.ofNat 64 (enc (Ins.jcc .nz (BitVec.ofNat 32 (lenOf brzTaken)))).length := by
    simp only [brzSeg, lenOfL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
      BitVec.ofNat_add, BitVec.add_assoc]
  simp only [fld, sld, mb, ms] at hsum
  rw [hsum] at hrest
  apply go brzSeg y _ (by decide) (code_prefix hc)
  simp [IR.op, IR.f1, IR.f2, IR.ld, IR.slot, IR.nxt, brzSeg, runL, exec, fld, sld, mb, ms, ea, X.get, X.set,
    aluStep, Cond.eval, rd64, rd32]
  repeat (first | (apply corrM_ask; intro _) | (apply corrM_opt; intro _))
  rename_i _ _ _ p
  simp only [CorrM]
  have ht : Code L.C _ ([fld .rax 2, .alu .add .r12 .rax] ++ dispatch) := code_prefix hrest
  have hn : Code L.C _ ([.alui .add .r12 16] ++ dispatch) := code_append hrest
  simp only [fld, mb, Nat.mul_one, sx32_ofNat (show lenOf brzTaken < 2 ^ 31 by decide)] at ht hn
  by_cases hz : p.1 = 0#64
  · simp only [hz, ↓reduceIte]
    refine straight_go h.tb [fld .rax 2, .alu .add .r12 .rax] _ _ (by decide) ht ?_
    corr
  · simp only [hz, ↓reduceIte]
    refine straight_go h.tb [.alui .add .r12 16] _ _ (by decide) ?_ ?_
    · rw [sx32_ofNat (show lenOf brzTaken < 2 ^ 31 by decide)]
      simpa [lenOfL, lenOf] using hn
    · corr

def spawnSeg : List Ins :=
  [fld .rcx 2, .lea .rcx (ms .r13 .rcx), .ld .rbx (mb .rcx), .ld .rbp (mb .rcx 8),
   .movi .rax (BitVec.ofNat 32 NR_CLONE), .movi .rdi (BitVec.ofNat 32 CLONE_FLAGS), .movi .rsi 0,
   .movi .rdx 0, .movi .r10 0, .movi .r8 0, .movi .r9 0, .syscall,
   .alu .test .rax .rax, .jcc .z (BitVec.ofNat 32 (lenOf spawnParent))]

theorem h24_ok {L : Lay} {y : X} (h : HPre L 24 y) : Match L (IR.op 24 ⟨y.r12, y.r13⟩) y := by
  have hc : Code L.C y.rip (spawnSeg ++ (spawnParent ++ ([.mov .r12 .rbx, .mov .r13 .rbp] ++ dispatch))) :=
    h.code
  have hrest := code_append hc
  have hp : Code L.C _ ([fld .rcx 1, sst .rcx .rax, .alui .add .r12 16] ++ dispatch) := code_prefix hrest
  have hk : Code L.C _ ([.mov .r12 .rbx, .mov .r13 .rbp] ++ dispatch) := code_append hrest
  have e1 : sx32 (BitVec.ofNat 32 NR_CLONE) = BitVec.ofNat 64 NR_CLONE := sx32_ofNat (by decide)
  have e2 : sx32 (BitVec.ofNat 32 CLONE_FLAGS) = BitVec.ofNat 64 CLONE_FLAGS := sx32_ofNat (by decide)
  have e3 : sx32 (BitVec.ofNat 32 (lenOf spawnParent)) = BitVec.ofNat 64 (lenOf spawnParent) :=
    sx32_ofNat (by decide)
  simp only [spawnSeg, lenOfL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
    BitVec.ofNat_add, ← BitVec.add_assoc, fld, mb, ms, Nat.mul_one] at hp hk
  apply go spawnSeg y _ (by decide) (code_prefix hc)
  simp [IR.op, IR.f2, IR.ld, IR.slot, spawnSeg, runL, exec, fld, sld, mb, ms, ea, X.get, X.set, X.nof,
    aluStep, Cond.eval, rd64, rd32, e1, e2, e3, cloneReq]
  repeat (first | (apply corrM_ask; intro _) | (apply corrM_opt; intro _))
  rename_i _ _ _ c _ f _ p
  simp only [CorrM]
  by_cases hz : p.1 = 0#64
  · simp only [hz, ↓reduceIte]
    refine straight_go h.tb [.mov .r12 .rbx, .mov .r13 .rbp] _ _ (by decide) ?_ ?_
    · simpa [lenOf, spawnParent, nextI, dispatch] using hk
    · corr
  · simp only [hz, ↓reduceIte]
    refine straight_go h.tb [fld .rcx 1, sst .rcx .rax, .alui .add .r12 16] _ _ (by decide) ?_ ?_
    · simpa [fld, sst, mb, ms] using hp
    · corr

end Runner.Beweis
