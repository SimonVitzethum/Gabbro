module
public import Stage0.Senke.Ausdruck.Arithmetik.Simulation.Teil3a

public import Stage0.Senke.Ausdruck.Arithmetik.Schleife
public import Stage0.Senke.Ausdruck.Quant.Frame
public import Stage0.Senke.Anweisung.SchleifeTeile
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Stage0.Senke.Ausdruck.Arithmetik.Simulation.Teil2

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
section
variable [Kern] {D : Deklaration} {L : Lay D} {Γ : Ctx}
    {ρ : Env D Γ} {W : Runner.Mem → Prop} {pc fp : Runner.W}
    {K base top reserved : Nat} {code : List II} {origin target : Int}
    {originDistance budget : Nat}
set_option maxHeartbeats 800000 in
theorem floatNormalizeLoopL_large_threshold_compare
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {distance : Nat}
    (h : Pre L m pc fp K base code ρ W reserved)
    (bound : distance < 2^63)
    (readDistance : m.rd64 (slot fp (BitVec.ofNat 64 (base+2))) =
      some (BitVec.ofNat 64 distance))
    (room : base+6 < K)
    (loaded : m.rd64 (slot fp (BitVec.ofNat 64 (base+6))) = some 63) :
    ∃ m', Star ⟨pc+176, fp⟩ m ⟨pc+192, fp⟩ m' ∧
      Agree fp (base+6) K m m' ∧
      Pre L m' pc fp K base code ρ W reserved ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+6))) =
        some (Runner.IR.bool (decide (distance < 63))) := by
  have shape : 11 < code.length ∧
      code[11]? = some (ci 13 (base+6) (base+2) (base+6)) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have entry : code[11] = ci 13 (base+6) (base+2) (base+6) := by
    simpa only [List.getElem?_eq_getElem shape.1, Option.some.injEq] using shape.2
  have ins := h.code 11 shape.1
  rw [entry] at ins
  simp only [ci] at ins
  let value := Runner.IR.bool (decide (distance < 63))
  let next := write m (slot fp (BitVec.ofNat 64 (base+6))) 8 value.toNat
  have ag : Agree fp (base+6) K m next := agree_write h.frame.room (by omega) room value.toNat
  have sx6 : sx (II.f ((base : Int)+6)) = BitVec.ofNat 64 (base+6) := by
    exact_mod_cast (sx_nat (d := base+6) (by have := h.small; omega))
  have sx2 : sx (II.f ((base : Int)+2)) = BitVec.ofNat 64 (base+2) := by
    exact_mod_cast (sx_nat (d := base+2) (by have := h.small; omega))
  have result : Runner.IR.bool ((BitVec.ofNat 64 distance).slt (63 : Runner.W)) = value := by
    have eq : BitVec.ofNat 64 distance = BitVec.ofInt 64 (distance : Int) := by simp
    rw [eq]
    change Runner.IR.bool ((BitVec.ofInt 64 (distance : Int)).slt (BitVec.ofInt 64 63)) = value
    rw [slt_in (by constructor <;> omega) (by constructor <;> norm_num)]
    simp [value]
  have comparison : Run (step ⟨pc+176, fp⟩) m ⟨pc+192, fp⟩ next := by
    have wr : m.wr64 (slot fp (sx (II.f ((base : Int)+6)))) value = some next := by
      rw [sx6]; exact wr64_some (h.frame.wr (base+6) room)
    have run := run_step (t := ⟨pc+176, fp⟩) ins (by decide)
      (run_bin (g := fun a b => some (Runner.IR.bool (a.slt b))) ins
        (by rw [sx2]; exact readDistance) (by rw [sx6]; exact loaded)
        (congrArg some result) wr)
    simpa [nxt, BitVec.add_assoc] using run
  have codeNext := h.code.agree ag h.far
  have preNext : Pre L next pc fp K base code ρ W reserved :=
    ⟨h.ctx, h.small, h.frame.agree ag, codeNext, h.far,
      envAt_agree h.env ag h.frame (by have := h.ctx; omega) (by omega),
      h.wstab m next h.welt (ag.mono (by omega)), h.wstab⟩
  refine ⟨next, Star.one comparison, ag, preNext, ?_⟩
  change (write m (slot fp (BitVec.ofNat 64 (base+6))) 8 value.toNat).rd64 _ = some value
  simp only [Runner.Mem.rd64, write_rd, h.frame.rd (base+6) room, ↓reduceIte,
      le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]


#print axioms floatNormalizeLoopL_large_threshold_compare

set_option maxHeartbeats 800000 in
theorem floatNormalizeLoopL_large_threshold_branch
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {distance : Nat}
    (h : Pre L m pc fp K base code ρ W reserved)
    (room : base+6 < K)
    (tested : m.rd64 (slot fp (BitVec.ofNat 64 (base+6))) =
      some (Runner.IR.bool (decide (distance < 63)))) :
    Run (step ⟨pc+192, fp⟩) m
      ⟨pc + (if distance < 63 then 208 else 336), fp⟩ m := by
  have shape : 12 < code.length ∧ code[12]? = some (ci 19 (base+6) 144 0) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have entry : code[12] = ci 19 (base+6) 144 0 := by
    simpa only [List.getElem?_eq_getElem shape.1, Option.some.injEq] using shape.2
  have ins := h.code 12 shape.1
  rw [entry] at ins
  simp only [ci] at ins
  have sx6 : sx (II.f ((base : Int)+6)) = BitVec.ofNat 64 (base+6) := by
    exact_mod_cast (sx_nat (d := base+6) (by have := h.small; omega))
  by_cases large : distance < 63
  · have readOne : m.rd64 (slot fp (sx (II.f ((base : Int)+6)))) = some 1 := by
      rw [sx6]; simpa [Runner.IR.bool, large] using tested
    have run := run_step (t := ⟨pc+192, fp⟩) ins (by decide)
      (run_brz_ne ins readOne (by decide))
    simpa [large, nxt, BitVec.add_assoc] using run
  · have readZero : m.rd64 (slot fp (sx (II.f ((base : Int)+6)))) = some 0 := by
      rw [sx6]; simpa [Runner.IR.bool, large] using tested
    have run := run_step (t := ⟨pc+192, fp⟩) ins (by decide)
      (run_brz_zero ins readZero)
    have offset : sx (II.f 144) = (144 : Runner.W) := by
      rw [sx_lit (by decide : lit32 144 = true)]; rfl
    simpa [large, offset, BitVec.add_assoc] using run


#print axioms floatNormalizeLoopL_large_threshold_branch

/-- Connected execution through the large carry decision preserves every
    state word already established at byte 160. -/
theorem floatNormalizeLoopL_large_carry_dispatch
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {fuel count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r)
    (room : base+6 < K) (large : 61 < distance) (active : q < target) :
    ∃ m', Star ⟨pc+48, fp⟩ m
        ⟨pc + (if distance-1 < 63 then 208 else 336), fp⟩ m' ∧
      Agree fp base K m m' ∧ Pre L m' pc fp K base code ρ W reserved ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 base)) = some (BitVec.ofInt 64 (2*q)) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+1))) = some (BitVec.ofInt 64 r) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+2))) = some (BitVec.ofNat 64 (distance-1)) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+3))) = some (BitVec.ofInt 64 target) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+4))) = some (BitVec.ofNat 64 fuel) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+5))) = some (BitVec.ofNat 64 count) ∧
      0 ≤ 2*q ∧ 2*q < 2^61 := by
  obtain ⟨m1, run1, ag1, pre1, rq, rr, rd, rt, rf, rc, bounds⟩ :=
    floatNormalizeLoopL_large_distance_dispatch hc head room large active
  obtain ⟨m2, run2, ag2, pre2, seed⟩ :=
    floatNormalizeLoopL_large_threshold_load hc pre1 room
  have rd2 : m2.rd64 (slot fp (BitVec.ofNat 64 (base+2))) =
      some (BitVec.ofNat 64 (distance-1)) := by
    rw [agree_rd_low ag2 pre1.frame.room (by omega) (by omega)]
    exact rd
  obtain ⟨m3, run3, ag3, pre3, tested⟩ :=
    floatNormalizeLoopL_large_threshold_compare hc pre2
      (by have := head.distanceWord; omega) rd2 room seed
  have run4 := floatNormalizeLoopL_large_threshold_branch hc pre3 room tested
  have ag := ag2.trans ag3
  have reads (i : Nat) (hi : i < base+6) :=
    agree_rd_low ag pre1.frame.room hi (show base+6 ≤ K by omega)
  refine ⟨m3, run1.trans (run2.trans (run3.trans (Star.one run4))),
    ag1.trans (ag.mono (by omega)), pre3, ?_, ?_, ?_, ?_, ?_, ?_, bounds⟩
  · rw [reads base (by omega)]; exact rq
  · rw [reads (base+1) (by omega)]; exact rr
  · rw [reads (base+2) (by omega)]; exact rd
  · rw [reads (base+3) (by omega)]; exact rt
  · rw [reads (base+4) (by omega)]; exact rf
  · rw [reads (base+5) (by omega)]; exact rc

#print axioms floatNormalizeLoopL_large_carry_dispatch

set_option maxHeartbeats 800000 in
/-- Execute the actual carry-path seed; only scratch is written. -/
theorem floatNormalizeLoopL_large_carry_seed
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem}
    (h : Pre L m pc fp K base code ρ W reserved)
    (room : base+6 < K) :
    ∃ m', Star ⟨pc+208, fp⟩ m ⟨pc+224, fp⟩ m' ∧
      Agree fp (base+6) K m m' ∧
      Pre L m' pc fp K base code ρ W reserved ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+6))) = some 1 := by
  have shape : 13 < code.length ∧ code[13]? = some (ci 1 (base+6) 1 0) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have entry : code[13] = ci 1 (base+6) 1 0 := by
    simpa only [List.getElem?_eq_getElem shape.1, Option.some.injEq] using shape.2
  have ins := h.code 13 shape.1
  rw [entry] at ins
  have singleton : CodeAt m (pc+208) [ci 1 (base+6) 1 0] := by
    intro i hi
    have iz : i = 0 := by simpa using hi
    subst i
    simpa [ci] using ins
  let next := write m (slot fp (BitVec.ofNat 64 (base+6))) 8 1
  have ag : Agree fp (base+6) K m next := agree_write h.frame.room (by omega) room 1
  have run : Star ⟨pc+208, fp⟩ m ⟨pc+224, fp⟩ next := by
    have hi := singleton 0 (by simp)
    simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
    have run : Run (step ⟨pc+208, fp⟩) m ⟨pc+208+16, fp⟩ next := by
      refine run_step hi (by decide) ?_
      simp only [op]
      refine f2_run (t := ⟨pc+208, fp⟩) hi ?_
      simp only [ret1]
      refine f1_run (t := ⟨pc+208, fp⟩) hi ?_
      have sx6 : sx (II.f ((base : Int)+6)) = BitVec.ofNat 64 (base+6) := by
        exact_mod_cast (sx_nat (d := base+6) (by have := h.small; omega))
      rw [sx_lit (by decide : lit32 1 = true), sx6]
      exact run_wr64 (wr64_some (h.frame.wr (base+6) room))
    exact Star.one (by simpa [BitVec.add_assoc] using run)
  have preNext : Pre L next pc fp K base code ρ W reserved :=
    ⟨h.ctx, h.small, h.frame.agree ag, h.code.agree ag h.far, h.far,
      envAt_agree h.env ag h.frame (by have := h.ctx; omega) (by omega),
      h.wstab m next h.welt (ag.mono (by omega)), h.wstab⟩
  refine ⟨next, run, ag, preNext, ?_⟩
  change (write m (slot fp (BitVec.ofNat 64 (base+6))) 8 (1 : Runner.W).toNat).rd64 _ = _
  simp only [Runner.Mem.rd64, write_rd, h.frame.rd (base+6) room, ↓reduceIte,
      le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]


#print axioms floatNormalizeLoopL_large_carry_seed

end
end Gabbro.Stage0.Senke
