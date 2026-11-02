module

public import Stage0.Senke.Ausdruck.Arithmetik.Schleife
public import Stage0.Senke.Ausdruck.Quant.Frame
public import Stage0.Senke.Anweisung.SchleifeTeile
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Stage0.Senke.Ausdruck.Arithmetik.Simulation.Teil5

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
section
variable [Kern] {D : Deklaration} {L : Lay D} {Γ : Ctx}
    {ρ : Env D Γ} {W : Runner.Mem → Prop} {pc fp : Runner.W}
    {K base top reserved : Nat} {code : List II} {origin target : Int}
    {originDistance budget : Nat}

set_option maxHeartbeats 800000 in
/-- Commit the two SMALL results from their actual temporary slots. The
    distance, target and budget slots survive the emitted copies. -/
theorem floatNormalizeLoopL_small_copies
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} (h : Pre L m pc fp K base code ρ W reserved)
    (room : base+9 < K) (q r : Runner.W)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 (base+8))) = some q)
    (rr : m.rd64 (slot fp (BitVec.ofNat 64 (base+9))) = some r) :
    ∃ m', Star ⟨pc + BitVec.ofNat 64 (16*(code.length-6)), fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16*(code.length-4)), fp⟩ m' ∧
      Agree fp base K m m' ∧ Pre L m' pc fp K base code ρ W reserved ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 base)) = some q ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+1))) = some r ∧
      (∀ i, i < K → i ≠ base → i ≠ base+1 →
        m'.rd64 (slot fp (BitVec.ofNat 64 i)) = m.rd64 (slot fp (BitVec.ofNat 64 i))) := by
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
  have shape1 : code.length ≥ 6 ∧ code.length-6 < code.length ∧
      code[code.length-6]? = some (ci 2 base (base+8) 0) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have entry1 : code[code.length-6] = ci 2 base (base+8) 0 := by
    simpa only [List.getElem?_eq_getElem shape1.2.1, Option.some.injEq] using shape1.2.2
  have ins1 := h.code (code.length-6) shape1.2.1
  rw [entry1] at ins1
  simp only [ci] at ins1
  let m1 := write m (slot fp (BitVec.ofNat 64 base)) 8 q.toNat
  have ag1 : Agree fp base K m m1 :=
    agree_write h.frame.room (by omega) (by omega) q.toNat
  have pre1 : Pre L m1 pc fp K base code ρ W reserved :=
    ⟨h.ctx, h.small, h.frame.agree ag1, h.code.agree ag1 h.far, h.far,
      envAt_agree h.env ag1 h.frame h.ctx (by omega),
      h.wstab m m1 h.welt (ag1.mono (by omega)), h.wstab⟩
  have read1 : m1.rd64 (slot fp (BitVec.ofNat 64 base)) = some q := by
    simp only [m1, Runner.Mem.rd64, write_rd, h.frame.rd base (by omega),
      ↓reduceIte, le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have run1 : Run (step ⟨pc + BitVec.ofNat 64 (16*(code.length-6)), fp⟩) m
      ⟨pc + BitVec.ofNat 64 (16*(code.length-5)), fp⟩ m1 := by
    have sxd : sx (II.f (base : Int)) = BitVec.ofNat 64 base := by
      exact_mod_cast sx_nat (d := base) (by have := h.small; omega)
    have sxs : sx (II.f ((base : Int)+8)) = BitVec.ofNat 64 (base+8) := by
      exact_mod_cast sx_nat (d := base+8) (by have := h.small; omega)
    have read : m.rd64 (slot fp (BitVec.ofNat 64 (base+8))) = some q := by
      exact rq
    have run : Run (step ⟨pc + BitVec.ofNat 64 (16*(code.length-6)), fp⟩) m ⟨(pc + BitVec.ofNat 64 (16*(code.length-6)))+16, fp⟩ m1 := by
      refine run_step ins1 (by decide) ?_
      simp only [op]
      refine f2_run (t := ⟨pc + BitVec.ofNat 64 (16*(code.length-6)), fp⟩) ins1 ?_
      rw [sxs]
      refine run_rd64 read ?_
      simp only [ret1]
      refine f1_run (t := ⟨pc + BitVec.ofNat 64 (16*(code.length-6)), fp⟩) ins1 ?_
      rw [sxd]
      exact run_wr64 (wr64_some (h.frame.wr base (by omega)))
    have advance : BitVec.ofNat 64 (16*(code.length-6)) + 16 =
        BitVec.ofNat 64 (16*(code.length-5)) := by
      change BitVec.ofNat 64 (16*(code.length-6)) + BitVec.ofNat 64 16 = _
      rw [← BitVec.ofNat_add]
      congr 1
      omega
    simpa only [BitVec.add_assoc, advance] using run
  have shape2 : code.length ≥ 6 ∧ code.length-5 < code.length ∧
      code[code.length-5]? = some (ci 2 (base+1) (base+9) 0) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have entry2 : code[code.length-5] = ci 2 (base+1) (base+9) 0 := by
    simpa only [List.getElem?_eq_getElem shape2.2.1, Option.some.injEq] using shape2.2.2
  have ins2 := pre1.code (code.length-5) shape2.2.1
  rw [entry2] at ins2
  simp only [ci] at ins2
  let m2 := write m1 (slot fp (BitVec.ofNat 64 (base+1))) 8 r.toNat
  have ag2 : Agree fp base K m1 m2 :=
    agree_write pre1.frame.room (by omega) (by omega) r.toNat
  have pre2 : Pre L m2 pc fp K base code ρ W reserved :=
    ⟨pre1.ctx, pre1.small, pre1.frame.agree ag2, pre1.code.agree ag2 pre1.far, pre1.far,
      envAt_agree pre1.env ag2 pre1.frame pre1.ctx (by omega),
      pre1.wstab m1 m2 pre1.welt (ag2.mono (by omega)), pre1.wstab⟩
  have read2 : m2.rd64 (slot fp (BitVec.ofNat 64 (base+1))) = some r := by
    simp only [m2, Runner.Mem.rd64, write_rd, pre1.frame.rd (base+1) (by omega),
      ↓reduceIte, le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have run2 : Run (step ⟨pc + BitVec.ofNat 64 (16*(code.length-5)), fp⟩) m1
      ⟨pc + BitVec.ofNat 64 (16*(code.length-4)), fp⟩ m2 := by
    have sxd : sx (II.f ((base : Int)+1)) = BitVec.ofNat 64 (base+1) := by
      exact_mod_cast sx_nat (d := (base+1)) (by have := h.small; omega)
    have sxs : sx (II.f ((base : Int)+9)) = BitVec.ofNat 64 (base+9) := by
      exact_mod_cast sx_nat (d := base+9) (by have := h.small; omega)
    have read : m1.rd64 (slot fp (BitVec.ofNat 64 (base+9))) = some r := by
      rw [show m1 = write m (slot fp (BitVec.ofNat 64 base)) 8 q.toNat from rfl,
        kept _ _ _ (by omega) (by omega) (by omega)]
      exact rr
    have run : Run (step ⟨pc + BitVec.ofNat 64 (16*(code.length-5)), fp⟩) m1 ⟨(pc + BitVec.ofNat 64 (16*(code.length-5)))+16, fp⟩ m2 := by
      refine run_step ins2 (by decide) ?_
      simp only [op]
      refine f2_run (t := ⟨pc + BitVec.ofNat 64 (16*(code.length-5)), fp⟩) ins2 ?_
      rw [sxs]
      refine run_rd64 read ?_
      simp only [ret1]
      refine f1_run (t := ⟨pc + BitVec.ofNat 64 (16*(code.length-5)), fp⟩) ins2 ?_
      rw [sxd]
      exact run_wr64 (wr64_some (pre1.frame.wr (base+1) (by omega)))
    have advance : BitVec.ofNat 64 (16*(code.length-5)) + 16 =
        BitVec.ofNat 64 (16*(code.length-4)) := by
      change BitVec.ofNat 64 (16*(code.length-5)) + BitVec.ofNat 64 16 = _
      rw [← BitVec.ofNat_add]
      congr 1
      omega
    simpa only [BitVec.add_assoc, advance] using run
  refine ⟨m2, (Star.one run1).trans (Star.one run2), ag1.trans ag2, pre2, ?_, read2, ?_⟩
  · rw [show m2 = write m1 (slot fp (BitVec.ofNat 64 (base+1))) 8 r.toNat from rfl,
      kept _ _ _ (by omega) (by omega) (by omega)]
    exact read1
  · intro i hi n0 n1
    simp only [m2, m1, kept _ _ i hi (by omega) n0, kept _ _ i hi (by omega) n1]

#print axioms floatNormalizeLoopL_small_copies


end
end Gabbro.Stage0.Senke
