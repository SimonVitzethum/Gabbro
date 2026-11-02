module
public import Stage0.Senke.Ausdruck.Arithmetik.Simulation.Teil4a

public import Stage0.Senke.Ausdruck.Arithmetik.Schleife
public import Stage0.Senke.Ausdruck.Quant.Frame
public import Stage0.Senke.Anweisung.SchleifeTeile
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Stage0.Senke.Ausdruck.Arithmetik.Simulation.Teil3

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
section
variable [Kern] {D : Deklaration} {L : Lay D} {Γ : Ctx}
    {ρ : Env D Γ} {W : Runner.Mem → Prop} {pc fp : Runner.W}
    {K base top reserved : Nat} {code : List II} {origin target : Int}
    {originDistance budget : Nat}

set_option maxHeartbeats 1600000 in
/-- Execute all five emitted carry arithmetic instructions. Word results are
    exact, including the comparison-to-carry conversion, with all other frame
    slots retained. This is actual execution, independent of loop induction. -/
theorem floatNormalizeLoopL_large_carry_arithmetic
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} (h : Pre L m pc fp K base code ρ W reserved)
    (room : base+8 < K) (q r den test : Runner.W)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 base)) = some q)
    (rr : m.rd64 (slot fp (BitVec.ofNat 64 (base+1))) = some r)
    (rd : m.rd64 (slot fp (BitVec.ofNat 64 (base+7))) = some den)
    (rt : m.rd64 (slot fp (BitVec.ofNat 64 (base+6))) = some test) :
    ∃ m', Star ⟨pc+256, fp⟩ m ⟨pc+336, fp⟩ m' ∧
      Agree fp base K m m' ∧ Pre L m' pc fp K base code ρ W reserved ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 base)) = some (q + (1-test)) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+1))) = some (r - den*(1-test)) ∧
      (∀ i, i < K → i ≠ base → i ≠ base+1 → i ≠ base+7 → i ≠ base+8 →
        m'.rd64 (slot fp (BitVec.ofNat 64 i)) = m.rd64 (slot fp (BitVec.ofNat 64 i))) := by
  have sxslot (j : Nat) (hj : j < K) : sx (II.f (j : Int)) = BitVec.ofNat 64 j :=
    sx_nat (by have := h.small; omega)
  have kept (mem : Runner.Mem) (j i : Nat) (hi : i < K) (hj : j < K)
      (ne : i ≠ j) (v : Runner.W) :
      (write mem (slot fp (BitVec.ofNat 64 j)) 8 v.toNat).rd64
        (slot fp (BitVec.ofNat 64 i)) = mem.rd64 (slot fp (BitVec.ofNat 64 i)) := by
    apply rd64_write_far
    have a := slot_toNat (fp := fp) (i := i) h.frame.room hi
    have b := slot_toNat (fp := fp) (i := j) h.frame.room hj
    unfold Far
    simp only [a, b]
    have hr := h.frame.room
    omega
  have shape1 : 16 < code.length ∧ code[16]? = some (ci 1 (base+8) 1 0) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have entry1 : code[16] = ci 1 (base+8) 1 0 := by
    simpa only [List.getElem?_eq_getElem shape1.1, Option.some.injEq] using shape1.2
  have ins1 := h.code 16 shape1.1
  rw [entry1] at ins1
  simp only [ci] at ins1
  let v1 : Runner.W := (1 : Runner.W)
  let m1 := write m (slot fp (BitVec.ofNat 64 (base+8))) 8 v1.toNat
  have ag1 : Agree fp base K m m1 :=
    agree_write h.frame.room (by omega) (by omega) v1.toNat
  have pre1 : Pre L m1 pc fp K base code ρ W reserved :=
    ⟨h.ctx, h.small, h.frame.agree ag1, h.code.agree ag1 h.far, h.far,
      envAt_agree h.env ag1 h.frame h.ctx (by omega),
      h.wstab m m1 h.welt (ag1.mono (by omega)), h.wstab⟩
  have read1 : m1.rd64 (slot fp (BitVec.ofNat 64 (base+8))) = some v1 := by
    simp only [m1, Runner.Mem.rd64, write_rd, h.frame.rd (base+8) (by omega),
      ↓reduceIte, le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have run1 : Run (step ⟨pc+256, fp⟩) m ⟨pc+272, fp⟩ m1 := by
    have run : Run (step ⟨pc+256, fp⟩) m ⟨(pc+256)+16, fp⟩ m1 := by
      refine run_step ins1 (by decide) ?_
      simp only [op, ci]
      refine f2_run (t := ⟨pc+256, fp⟩) ins1 ?_
      simp only [ret1]
      refine f1_run (t := ⟨pc+256, fp⟩) ins1 ?_
      simp only [ci, nxt]
      rw [sx_lit (by decide : lit32 1 = true)]
      have sx8 : sx (II.f ((base : Int)+8)) = BitVec.ofNat 64 (base+8) := by
        exact_mod_cast sxslot (base+8) room
      rw [sx8]
      exact run_wr64 (wr64_some (h.frame.wr (base+8) room))
    simpa [BitVec.add_assoc] using run
  have shape2 : 17 < code.length ∧ code[17]? = some (ci 4 (base+8) (base+8) (base+6)) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have entry2 : code[17] = ci 4 (base+8) (base+8) (base+6) := by
    simpa only [List.getElem?_eq_getElem shape2.1, Option.some.injEq] using shape2.2
  have ins2 := pre1.code 17 shape2.1
  rw [entry2] at ins2
  simp only [ci] at ins2
  let v2 : Runner.W := (1-test)
  let m2 := write m1 (slot fp (BitVec.ofNat 64 (base+8))) 8 v2.toNat
  have ag2 : Agree fp base K m1 m2 :=
    agree_write pre1.frame.room (by omega) (by omega) v2.toNat
  have pre2 : Pre L m2 pc fp K base code ρ W reserved :=
    ⟨pre1.ctx, pre1.small, pre1.frame.agree ag2, pre1.code.agree ag2 pre1.far, pre1.far,
      envAt_agree pre1.env ag2 pre1.frame pre1.ctx (by omega),
      pre1.wstab m1 m2 pre1.welt (ag2.mono (by omega)), pre1.wstab⟩
  have read2 : m2.rd64 (slot fp (BitVec.ofNat 64 (base+8))) = some v2 := by
    simp only [m2, Runner.Mem.rd64, write_rd, pre1.frame.rd (base+8) (by omega),
      ↓reduceIte, le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have run2 : Run (step ⟨pc+272, fp⟩) m1 ⟨pc+288, fp⟩ m2 := by
    have sxa : sx (II.f ((base : Int)+8)) = BitVec.ofNat 64 (base+8) := by
      exact_mod_cast sxslot (base+8) (by omega)
    have sxb : sx (II.f ((base : Int)+6)) = BitVec.ofNat 64 (base+6) := by
      exact_mod_cast sxslot (base+6) (by omega)
    have sxd : sx (II.f ((base : Int)+8)) = BitVec.ofNat 64 (base+8) := by
      exact_mod_cast sxslot (base+8) (by omega)
    have ra : m1.rd64 (slot fp (BitVec.ofNat 64 (base+8))) = some (1 : Runner.W) := by
      exact read1
    have rb : m1.rd64 (slot fp (BitVec.ofNat 64 (base+6))) = some test := by
      rw [show m1 = write m (slot fp (BitVec.ofNat 64 (base+8))) 8 v1.toNat from rfl, kept _ _ _ (by omega) (by omega) (by omega)]
      exact rt
    have wr : m1.wr64 (slot fp (sx (II.f ((base : Int)+8)))) v2 = some m2 := by
      rw [sxd]; exact wr64_some (pre1.frame.wr (base+8) (by omega))
    have run := run_step (t := ⟨pc+272, fp⟩) ins2 (by decide)
      (run_bin (g := fun a b => some (a-b)) ins2
        (by rw [sxa]; exact ra) (by rw [sxb]; exact rb) rfl wr)
    simpa [nxt, BitVec.add_assoc] using run
  have shape3 : 18 < code.length ∧ code[18]? = some (ci 5 (base+7) (base+7) (base+8)) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have entry3 : code[18] = ci 5 (base+7) (base+7) (base+8) := by
    simpa only [List.getElem?_eq_getElem shape3.1, Option.some.injEq] using shape3.2
  have ins3 := pre2.code 18 shape3.1
  rw [entry3] at ins3
  simp only [ci] at ins3
  let v3 : Runner.W := (den*(1-test))
  let m3 := write m2 (slot fp (BitVec.ofNat 64 (base+7))) 8 v3.toNat
  have ag3 : Agree fp base K m2 m3 :=
    agree_write pre2.frame.room (by omega) (by omega) v3.toNat
  have pre3 : Pre L m3 pc fp K base code ρ W reserved :=
    ⟨pre2.ctx, pre2.small, pre2.frame.agree ag3, pre2.code.agree ag3 pre2.far, pre2.far,
      envAt_agree pre2.env ag3 pre2.frame pre2.ctx (by omega),
      pre2.wstab m2 m3 pre2.welt (ag3.mono (by omega)), pre2.wstab⟩
  have read3 : m3.rd64 (slot fp (BitVec.ofNat 64 (base+7))) = some v3 := by
    simp only [m3, Runner.Mem.rd64, write_rd, pre2.frame.rd (base+7) (by omega),
      ↓reduceIte, le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have run3 : Run (step ⟨pc+288, fp⟩) m2 ⟨pc+304, fp⟩ m3 := by
    have sxa : sx (II.f ((base : Int)+7)) = BitVec.ofNat 64 (base+7) := by
      exact_mod_cast sxslot (base+7) (by omega)
    have sxb : sx (II.f ((base : Int)+8)) = BitVec.ofNat 64 (base+8) := by
      exact_mod_cast sxslot (base+8) (by omega)
    have sxd : sx (II.f ((base : Int)+7)) = BitVec.ofNat 64 (base+7) := by
      exact_mod_cast sxslot (base+7) (by omega)
    have ra : m2.rd64 (slot fp (BitVec.ofNat 64 (base+7))) = some den := by
      rw [show m2 = write m1 (slot fp (BitVec.ofNat 64 (base+8))) 8 v2.toNat from rfl, kept _ _ _ (by omega) (by omega) (by omega)]
      rw [show m1 = write m (slot fp (BitVec.ofNat 64 (base+8))) 8 v1.toNat from rfl, kept _ _ _ (by omega) (by omega) (by omega)]
      exact rd
    have rb : m2.rd64 (slot fp (BitVec.ofNat 64 (base+8))) = some (1-test) := by
      exact read2
    have wr : m2.wr64 (slot fp (sx (II.f ((base : Int)+7)))) v3 = some m3 := by
      rw [sxd]; exact wr64_some (pre2.frame.wr (base+7) (by omega))
    have run := run_step (t := ⟨pc+288, fp⟩) ins3 (by decide)
      (run_bin (g := fun a b => some (a*b)) ins3
        (by rw [sxa]; exact ra) (by rw [sxb]; exact rb) rfl wr)
    simpa [nxt, BitVec.add_assoc] using run
  have shape4 : 19 < code.length ∧ code[19]? = some (ci 4 (base+1) (base+1) (base+7)) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have entry4 : code[19] = ci 4 (base+1) (base+1) (base+7) := by
    simpa only [List.getElem?_eq_getElem shape4.1, Option.some.injEq] using shape4.2
  have ins4 := pre3.code 19 shape4.1
  rw [entry4] at ins4
  simp only [ci] at ins4
  let v4 : Runner.W := (r-den*(1-test))
  let m4 := write m3 (slot fp (BitVec.ofNat 64 (base+1))) 8 v4.toNat
  have ag4 : Agree fp base K m3 m4 :=
    agree_write pre3.frame.room (by omega) (by omega) v4.toNat
  have pre4 : Pre L m4 pc fp K base code ρ W reserved :=
    ⟨pre3.ctx, pre3.small, pre3.frame.agree ag4, pre3.code.agree ag4 pre3.far, pre3.far,
      envAt_agree pre3.env ag4 pre3.frame pre3.ctx (by omega),
      pre3.wstab m3 m4 pre3.welt (ag4.mono (by omega)), pre3.wstab⟩
  have read4 : m4.rd64 (slot fp (BitVec.ofNat 64 (base+1))) = some v4 := by
    simp only [m4, Runner.Mem.rd64, write_rd, pre3.frame.rd (base+1) (by omega),
      ↓reduceIte, le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have run4 : Run (step ⟨pc+304, fp⟩) m3 ⟨pc+320, fp⟩ m4 := by
    have sxa : sx (II.f ((base : Int)+1)) = BitVec.ofNat 64 (base+1) := by
      exact_mod_cast sxslot (base+1) (by omega)
    have sxb : sx (II.f ((base : Int)+7)) = BitVec.ofNat 64 (base+7) := by
      exact_mod_cast sxslot (base+7) (by omega)
    have sxd : sx (II.f ((base : Int)+1)) = BitVec.ofNat 64 (base+1) := by
      exact_mod_cast sxslot (base+1) (by omega)
    have ra : m3.rd64 (slot fp (BitVec.ofNat 64 (base+1))) = some r := by
      rw [show m3 = write m2 (slot fp (BitVec.ofNat 64 (base+7))) 8 v3.toNat from rfl, kept _ _ _ (by omega) (by omega) (by omega)]
      rw [show m2 = write m1 (slot fp (BitVec.ofNat 64 (base+8))) 8 v2.toNat from rfl, kept _ _ _ (by omega) (by omega) (by omega)]
      rw [show m1 = write m (slot fp (BitVec.ofNat 64 (base+8))) 8 v1.toNat from rfl, kept _ _ _ (by omega) (by omega) (by omega)]
      exact rr
    have rb : m3.rd64 (slot fp (BitVec.ofNat 64 (base+7))) = some (den*(1-test)) := by
      exact read3
    have wr : m3.wr64 (slot fp (sx (II.f ((base : Int)+1)))) v4 = some m4 := by
      rw [sxd]; exact wr64_some (pre3.frame.wr (base+1) (by omega))
    have run := run_step (t := ⟨pc+304, fp⟩) ins4 (by decide)
      (run_bin (g := fun a b => some (a-b)) ins4
        (by rw [sxa]; exact ra) (by rw [sxb]; exact rb) rfl wr)
    simpa [nxt, BitVec.add_assoc] using run
  have shape5 : 20 < code.length ∧ code[20]? = some (ci 3 base base (base+8)) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have entry5 : code[20] = ci 3 base base (base+8) := by
    simpa only [List.getElem?_eq_getElem shape5.1, Option.some.injEq] using shape5.2
  have ins5 := pre4.code 20 shape5.1
  rw [entry5] at ins5
  simp only [ci] at ins5
  let v5 : Runner.W := (q+(1-test))
  let m5 := write m4 (slot fp (BitVec.ofNat 64 base)) 8 v5.toNat
  have ag5 : Agree fp base K m4 m5 :=
    agree_write pre4.frame.room (by omega) (by omega) v5.toNat
  have pre5 : Pre L m5 pc fp K base code ρ W reserved :=
    ⟨pre4.ctx, pre4.small, pre4.frame.agree ag5, pre4.code.agree ag5 pre4.far, pre4.far,
      envAt_agree pre4.env ag5 pre4.frame pre4.ctx (by omega),
      pre4.wstab m4 m5 pre4.welt (ag5.mono (by omega)), pre4.wstab⟩
  have read5 : m5.rd64 (slot fp (BitVec.ofNat 64 base)) = some v5 := by
    simp only [m5, Runner.Mem.rd64, write_rd, pre4.frame.rd base (by omega),
      ↓reduceIte, le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have run5 : Run (step ⟨pc+320, fp⟩) m4 ⟨pc+336, fp⟩ m5 := by
    have sxa : sx (II.f (base : Int)) = BitVec.ofNat 64 base := by
      exact_mod_cast sxslot base (by omega)
    have sxb : sx (II.f ((base : Int)+8)) = BitVec.ofNat 64 (base+8) := by
      exact_mod_cast sxslot (base+8) (by omega)
    have sxd : sx (II.f (base : Int)) = BitVec.ofNat 64 base := by
      exact_mod_cast sxslot base (by omega)
    have ra : m4.rd64 (slot fp (BitVec.ofNat 64 base)) = some q := by
      rw [show m4 = write m3 (slot fp (BitVec.ofNat 64 (base+1))) 8 v4.toNat from rfl, kept _ _ _ (by omega) (by omega) (by omega)]
      rw [show m3 = write m2 (slot fp (BitVec.ofNat 64 (base+7))) 8 v3.toNat from rfl, kept _ _ _ (by omega) (by omega) (by omega)]
      rw [show m2 = write m1 (slot fp (BitVec.ofNat 64 (base+8))) 8 v2.toNat from rfl, kept _ _ _ (by omega) (by omega) (by omega)]
      rw [show m1 = write m (slot fp (BitVec.ofNat 64 (base+8))) 8 v1.toNat from rfl, kept _ _ _ (by omega) (by omega) (by omega)]
      exact rq
    have rb : m4.rd64 (slot fp (BitVec.ofNat 64 (base+8))) = some (1-test) := by
      rw [show m4 = write m3 (slot fp (BitVec.ofNat 64 (base+1))) 8 v4.toNat from rfl, kept _ _ _ (by omega) (by omega) (by omega)]
      rw [show m3 = write m2 (slot fp (BitVec.ofNat 64 (base+7))) 8 v3.toNat from rfl, kept _ _ _ (by omega) (by omega) (by omega)]
      exact read2
    have wr : m4.wr64 (slot fp (sx (II.f (base : Int)))) v5 = some m5 := by
      rw [sxd]; exact wr64_some (pre4.frame.wr base (by omega))
    have run := run_step (t := ⟨pc+320, fp⟩) ins5 (by decide)
      (run_bin (g := fun a b => some (a+b)) ins5
        (by rw [sxa]; exact ra) (by rw [sxb]; exact rb) rfl wr)
    simpa [nxt, BitVec.add_assoc] using run
  refine ⟨m5, (Star.one run1).trans ((Star.one run2).trans
    ((Star.one run3).trans ((Star.one run4).trans (Star.one run5)))),
    ag1.trans (ag2.trans (ag3.trans (ag4.trans ag5))), pre5, read5, ?_, ?_⟩
  · rw [show m5 = write m4 (slot fp (BitVec.ofNat 64 base)) 8 v5.toNat from rfl,
      kept _ _ _ (by omega) (by omega) (by omega)]
    exact read4
  · intro i hi n0 n1 n7 n8
    simp only [m5, m4, m3, m2, m1,
      kept _ _ i hi (by omega) n0, kept _ _ i hi (by omega) n1,
      kept _ _ i hi (by omega) n7, kept _ _ i hi (by omega) n8]

#print axioms floatNormalizeLoopL_large_carry_arithmetic

end
end Gabbro.Stage0.Senke
