import Runner.Beweis.Handler.Gerade

/-! # `brz`: the handler branches inside

The first four instructions read the slot and test it; `jnz` skips the taken branch. Each branch is a straight
body followed by the dispatch, handled by `straight_at`. -/

namespace Runner.Beweis
open Runner.X86 Runner.Prog

theorem sx32_ofNat {n : Nat} (h : n < 2 ^ 31) : sx32 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    simp only [BitVec.msb_eq_decide, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  rw [sx32, BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

def brzSeg : List Ins :=
  [fld .rax 1, sld .rax .rax, .alu .test .rax .rax, .jcc .nz (BitVec.ofNat 32 (lenOf brzTaken))]

theorem h19_ok {L : Lay} {y : X} (h : HPre L 19 y) : HSim L (IR.op 19 ⟨y.r12, y.r13, y.mem⟩) y := by
  have hc' : Code y.mem y.rip (brzSeg ++ (brzTaken ++ nextI)) := h.code
  obtain ⟨_, htb, hi⟩ := h
  have hreach := reach_runL brzSeg y (code_prefix hc') (by decide)
  have hrest := Code.append hc'
  generalize hr : runL brzSeg y = r at hreach
  simp [brzSeg, runL, exec, fld, sld, mb, ms, ea, X.get, X.set, aluStep, Cond.eval] at hr
  simp only [IR.op, IR.f1, IR.f2, IR.ld, IR.slot, opt_map, ir_sx, BitVec.ofNat_eq_ofNat]
  cases h1 : y.mem.rd32 (y.r12 + 4#64) with
  | none => simp only [h1, opt_none] at hr ⊢; subst hr; exact hreach
  | some a =>
    cases h2 : y.mem.rd64 (y.r13 + sx32 a * 8#64) with
    | none => simp only [h1, h2, opt_none, opt_some] at hr ⊢; subst hr; exact hreach
    | some va =>
      simp only [h1, h2, opt_some] at hr ⊢
      subst hr
      apply HSim.prefix hreach
      have hsum : (y.rip + BitVec.ofNat 64 (enc (fld .rax 1)).length + BitVec.ofNat 64 (enc (sld .rax .rax)).length +
          BitVec.ofNat 64 (enc (Ins.alu .test .rax .rax)).length +
          BitVec.ofNat 64 (enc (Ins.jcc .nz (BitVec.ofNat 32 (lenOf brzTaken)))).length) =
          y.rip + BitVec.ofNat 64 (List.map (fun i => (enc i).length) brzSeg).sum := by
        simp only [brzSeg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
          BitVec.ofNat_add, BitVec.add_assoc]
      split
      · next hz =>
        subst hz
        refine straight_at (body := [fld .rax 2, .alu .add .r12 .rax]) (by decide) _ ?_ htb hi ?_
        · rw [← hsum] at hrest
          exact code_prefix hrest
        · corr
      · next hz =>
        refine straight_at (body := [.alui .add .r12 16]) (by decide) _ ?_ htb hi ?_
        · simp only [sx32_ofNat (show lenOf brzTaken < 2 ^ 31 by decide)]
          rw [← hsum] at hrest
          exact Code.append hrest
        · corr

end Runner.Beweis
