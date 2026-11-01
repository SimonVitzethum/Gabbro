module

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

/-- Continue the mutated large state through the seed load and distance write.
    Only the distance and scratch seed change; in particular the doubled
    quotient and all remaining state words survive these actual instructions. -/
set_option maxHeartbeats 800000 in
theorem floatNormalizeLoopL_large_distance
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {distance : Nat}
    (h : Pre L m pc fp K base code ρ W reserved)
    (room : base+6 < K) (large : 61 < distance)
    (readDistance : m.rd64 (slot fp (BitVec.ofNat 64 (base+2))) =
      some (BitVec.ofNat 64 distance)) :
    ∃ m', Star ⟨pc+128, fp⟩ m ⟨pc+160, fp⟩ m' ∧
      Agree fp base K m m' ∧ Pre L m' pc fp K base code ρ W reserved ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+2))) =
        some (BitVec.ofNat 64 (distance-1)) ∧
      (∀ i, i < K → i ≠ base+2 → i ≠ base+6 →
        m'.rd64 (slot fp (BitVec.ofNat 64 i)) =
          m.rd64 (slot fp (BitVec.ofNat 64 i))) := by
  have shape : 9 < code.length ∧
      code[8]? = some (ci 1 (base+6) 1 0) ∧
      code[9]? = some (ci 4 (base+2) (base+2) (base+6)) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have ins8 := h.code 8 (by omega)
  have ins9 := h.code 9 shape.1
  have e8 : code[8] = ci 1 (base+6) 1 0 := by
    simpa only [List.getElem?_eq_getElem (show 8 < code.length by omega),
      Option.some.injEq] using shape.2.1
  have e9 : code[9] = ci 4 (base+2) (base+2) (base+6) := by
    simpa only [List.getElem?_eq_getElem shape.1, Option.some.injEq] using shape.2.2
  rw [e8] at ins8
  rw [e9] at ins9
  simp only [ci] at ins8
  have sx2 : sx (II.f ((base : Int)+2)) = BitVec.ofNat 64 (base+2) := by
    exact_mod_cast (sx_nat (d := base+2) (by have := h.small; omega))
  have sx6 : sx (II.f ((base : Int)+6)) = BitVec.ofNat 64 (base+6) := by
    exact_mod_cast (sx_nat (d := base+6) (by have := h.small; omega))
  let m1 := write m (slot fp (BitVec.ofNat 64 (base+6))) 8 (1 : Runner.W).toNat
  have ag1 : Agree fp (base+6) K m m1 :=
    agree_write h.frame.room (by omega) room (1 : Runner.W).toNat
  have run1 : Run (step ⟨pc+128, fp⟩) m ⟨pc+144, fp⟩ m1 := by
    have run : Run (step ⟨pc+128, fp⟩) m ⟨(pc+128)+16, fp⟩ m1 := by
      refine run_step ins8 (by decide) ?_
      simp only [op, ci]
      refine f2_run (t := ⟨pc+128, fp⟩) ins8 ?_
      simp only [ret1]
      refine f1_run (t := ⟨pc+128, fp⟩) ins8 ?_
      simp only [ci, nxt]
      rw [sx_lit (by decide : lit32 1 = true), sx6]
      exact run_wr64 (wr64_some (h.frame.wr (base+6) room))
    simpa [BitVec.add_assoc] using run
  have pre1 : Pre L m1 pc fp K base code ρ W reserved :=
    ⟨h.ctx, h.small, h.frame.agree ag1, h.code.agree ag1 h.far, h.far,
      envAt_agree h.env ag1 h.frame (by have := h.ctx; omega) (by omega),
      h.wstab m m1 h.welt (ag1.mono (by omega)), h.wstab⟩
  have seed : m1.rd64 (slot fp (BitVec.ofNat 64 (base+6))) = some 1 := by
    change (write m _ 8 (1 : Runner.W).toNat).rd64 _ = _
    simp only [Runner.Mem.rd64, write_rd, h.frame.rd (base+6) room, ↓reduceIte,
      le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have dist1 : m1.rd64 (slot fp (BitVec.ofNat 64 (base+2))) =
      some (BitVec.ofNat 64 distance) := by
    rw [agree_rd_low ag1 h.frame.room (show base+2 < base+6 by omega) (by omega)]
    exact readDistance
  let value := BitVec.ofNat 64 (distance-1)
  let m2 := write m1 (slot fp (BitVec.ofNat 64 (base+2))) 8 value.toNat
  have ag2 : Agree fp base K m1 m2 :=
    agree_write pre1.frame.room (by omega) (by omega) value.toNat
  have arithmetic : BitVec.ofNat 64 distance - (1 : Runner.W) = value := by
    change BitVec.ofNat 64 distance - BitVec.ofNat 64 1 = BitVec.ofNat 64 (distance-1)
    exact BitVec.ofNat_sub_ofNat_of_le distance 1 (by decide) (by omega)
  have fetched := pre1.code 9 shape.1
  rw [e9] at fetched
  simp only [ci] at fetched
  have run2 : Run (step ⟨pc+144, fp⟩) m1 ⟨pc+160, fp⟩ m2 := by
    have wr : m1.wr64 (slot fp (sx (II.f ((base : Int)+2)))) value = some m2 := by
      rw [sx2]; exact wr64_some (pre1.frame.wr (base+2) (by omega))
    have run := run_step (t := ⟨pc+144, fp⟩) fetched (by decide)
      (run_bin (g := fun a b => some (a-b)) fetched
        (by rw [sx2]; exact dist1) (by rw [sx6]; exact seed)
        (congrArg some arithmetic) wr)
    simpa [nxt, BitVec.add_assoc] using run
  have pre2 : Pre L m2 pc fp K base code ρ W reserved :=
    ⟨pre1.ctx, pre1.small, pre1.frame.agree ag2, pre1.code.agree ag2 pre1.far, pre1.far,
      envAt_agree pre1.env ag2 pre1.frame pre1.ctx (by omega),
      pre1.wstab m1 m2 pre1.welt (ag2.mono (by omega)), pre1.wstab⟩
  have kept (mem : Runner.Mem) (j i : Nat) (hi : i < K) (hj : j < K) (ne : i ≠ j)
      (v : Nat) :
      (write mem (slot fp (BitVec.ofNat 64 j)) 8 v).rd64
        (slot fp (BitVec.ofNat 64 i)) = mem.rd64 (slot fp (BitVec.ofNat 64 i)) := by
    apply rd64_write_far
    have a := slot_toNat (fp := fp) (i := i) h.frame.room hi
    have b := slot_toNat (fp := fp) (i := j) h.frame.room hj
    unfold Far
    simp only [a, b]
    have hr := h.frame.room
    omega
  refine ⟨m2, (Star.one run1).trans (Star.one run2), (ag1.mono (by omega)).trans ag2,
    pre2, ?_, ?_⟩
  · change (write m1 _ 8 value.toNat).rd64 _ = some value
    simp only [Runner.Mem.rd64, write_rd, pre1.frame.rd (base+2) (by omega), ↓reduceIte,
      le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro i hi ne2 ne6
    change (write m1 _ 8 value.toNat).rd64 _ = _
    rw [kept m1 (base+2) i hi (by omega) ne2 value.toNat]
    exact kept m (base+6) i hi room ne6 _

#print axioms floatNormalizeLoopL_large_distance

/-- Connected large execution including the first distance mutation. -/
theorem floatNormalizeLoopL_large_distance_dispatch
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {fuel count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r)
    (room : base+6 < K) (large : 61 < distance) (active : q < target) :
    ∃ m', Star ⟨pc+48, fp⟩ m ⟨pc+160, fp⟩ m' ∧
      Agree fp base K m m' ∧ Pre L m' pc fp K base code ρ W reserved ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 base)) = some (BitVec.ofInt 64 (2*q)) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+1))) = some (BitVec.ofInt 64 r) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+2))) = some (BitVec.ofNat 64 (distance-1)) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+3))) = some (BitVec.ofInt 64 target) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+4))) = some (BitVec.ofNat 64 fuel) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+5))) = some (BitVec.ofNat 64 count) ∧
      0 ≤ 2*q ∧ 2*q < 2^61 := by
  obtain ⟨m1, run1, ag1, pre1, rq, rr, rd, rt, rf, rc, bounds⟩ :=
    floatNormalizeLoopL_large_dispatch hc head room large active
  obtain ⟨m2, run2, ag2, pre2, rd2, kept⟩ :=
    floatNormalizeLoopL_large_distance hc pre1 room large rd
  refine ⟨m2, run1.trans run2, ag1.trans ag2, pre2, ?_, ?_, rd2, ?_, ?_, ?_, bounds⟩
  · rw [kept base (by omega) (by omega) (by omega)]; exact rq
  · rw [kept (base+1) (by omega) (by omega) (by omega)]; exact rr
  · rw [kept (base+3) (by omega) (by omega) (by omega)]; exact rt
  · rw [kept (base+4) (by omega) (by omega) (by omega)]; exact rf
  · rw [kept (base+5) (by omega) (by omega) (by omega)]; exact rc

#print axioms floatNormalizeLoopL_large_distance_dispatch


set_option maxHeartbeats 800000 in
/-- Actual continuation after the distance decrement; only scratch is written. -/
theorem floatNormalizeLoopL_large_threshold_load
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem}
    (h : Pre L m pc fp K base code ρ W reserved)
    (room : base+6 < K) :
    ∃ m', Star ⟨pc+160, fp⟩ m ⟨pc+176, fp⟩ m' ∧
      Agree fp (base+6) K m m' ∧
      Pre L m' pc fp K base code ρ W reserved ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+6))) = some 63 := by
  have shape : 10 < code.length ∧ code[10]? = some (ci 1 (base+6) 63 0) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have entry : code[10] = ci 1 (base+6) 63 0 := by
    simpa only [List.getElem?_eq_getElem shape.1, Option.some.injEq] using shape.2
  have ins := h.code 10 shape.1
  rw [entry] at ins
  have singleton : CodeAt m (pc+160) [ci 1 (base+6) 63 0] := by
    intro i hi
    have iz : i = 0 := by simpa using hi
    subst i
    simpa [ci] using ins
  let next := write m (slot fp (BitVec.ofNat 64 (base+6))) 8 63
  have ag : Agree fp (base+6) K m next := agree_write h.frame.room (by omega) room 63
  have run : Star ⟨pc+160, fp⟩ m ⟨pc+176, fp⟩ next := by
    have hi := singleton 0 (by simp)
    simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
    have run : Run (step ⟨pc+160, fp⟩) m ⟨pc+160+16, fp⟩ next := by
      refine run_step hi (by decide) ?_
      simp only [op]
      refine f2_run (t := ⟨pc+160, fp⟩) hi ?_
      simp only [ret1]
      refine f1_run (t := ⟨pc+160, fp⟩) hi ?_
      have sx6 : sx (II.f ((base : Int)+6)) = BitVec.ofNat 64 (base+6) := by
        exact_mod_cast (sx_nat (d := base+6) (by have := h.small; omega))
      rw [sx_lit (by decide : lit32 63 = true), sx6]
      exact run_wr64 (wr64_some (h.frame.wr (base+6) room))
    exact Star.one (by simpa [BitVec.add_assoc] using run)
  have preNext : Pre L next pc fp K base code ρ W reserved :=
    ⟨h.ctx, h.small, h.frame.agree ag, h.code.agree ag h.far, h.far,
      envAt_agree h.env ag h.frame (by have := h.ctx; omega) (by omega),
      h.wstab m next h.welt (ag.mono (by omega)), h.wstab⟩
  refine ⟨next, run, ag, preNext, ?_⟩
  change (write m (slot fp (BitVec.ofNat 64 (base+6))) 8 (63 : Runner.W).toNat).rd64 _ = _
  simp only [Runner.Mem.rd64, write_rd, h.frame.rd (base+6) room, ↓reduceIte,
      le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]


#print axioms floatNormalizeLoopL_large_threshold_load

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
