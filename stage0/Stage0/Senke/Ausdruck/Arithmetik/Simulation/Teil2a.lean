module

public import Stage0.Senke.Ausdruck.Arithmetik.Schleife
public import Stage0.Senke.Ausdruck.Quant.Frame
public import Stage0.Senke.Anweisung.SchleifeTeile
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Stage0.Senke.Ausdruck.Arithmetik.Simulation.Teil1

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
section
variable [Kern] {D : Deklaration} {L : Lay D} {Γ : Ctx}
    {ρ : Env D Γ} {W : Runner.Mem → Prop} {pc fp : Runner.W}
    {K base top reserved : Nat} {code : List II} {origin target : Int}
    {originDistance budget : Nat}

set_option maxHeartbeats 800000 in
/-- Dispatch from the actual distance-test result to the emitted transfer paths. -/
theorem floatNormalizeLoopL_distance_branch
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {fuel count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r)
    (room : base+6 < K)
    (tested : m.rd64 (slot fp (BitVec.ofNat 64 (base+6))) =
      some (Runner.IR.bool (decide (61 < distance)))) :
    Run (step ⟨pc+80, fp⟩) m
      ⟨pc + (if 61 < distance then 96 else 352), fp⟩ m := by
  have h := head.pre
  have shape : 5 < code.length ∧ code[5]? = some (ci 19 (base+6) 272 0) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have entry : code[5] = ci 19 (base+6) 272 0 := by
    simpa only [List.getElem?_eq_getElem shape.1, Option.some.injEq] using shape.2
  have ins := h.code 5 shape.1
  rw [entry] at ins
  simp only [ci] at ins
  have sx6 : sx (II.f ((base : Int)+6)) = BitVec.ofNat 64 (base+6) := by
    exact_mod_cast (sx_nat (d := base+6) (by have := h.small; omega))
  by_cases large : 61 < distance
  · have readOne : m.rd64 (slot fp (sx (II.f ((base : Int)+6)))) = some 1 := by
      rw [sx6]; simpa [Runner.IR.bool, large] using tested
    have run := run_step (t := ⟨pc+80, fp⟩) ins (by decide)
      (run_brz_ne ins readOne (by decide))
    simpa [large, nxt, BitVec.add_assoc] using run
  · have readZero : m.rd64 (slot fp (sx (II.f ((base : Int)+6)))) = some 0 := by
      rw [sx6]; simpa [Runner.IR.bool, large] using tested
    have run := run_step (t := ⟨pc+80, fp⟩) ins (by decide)
      (run_brz_zero ins readZero)
    have offset : sx (II.f 272) = (272 : Runner.W) := by
      rw [sx_lit (by decide : lit32 272 = true)]; rfl
    simpa [large, offset, BitVec.add_assoc] using run

#print axioms floatNormalizeLoopL_distance_branch

/-- Connected continuation from byte 48, with the actual discriminator fetched
    and executed. No active-iteration premise is used for this prefix. -/
theorem floatNormalizeLoopL_active_dispatch
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {fuel count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r)
    (room : base+6 < K) :
    ∃ m', Star ⟨pc+48, fp⟩ m
        ⟨pc + (if 61 < distance then 96 else 352), fp⟩ m' ∧
      Agree fp base K m m' ∧
      FloatNormalizeHead L ρ W pc fp K base reserved code origin
        originDistance budget target m' fuel count distance q r := by
  obtain ⟨m1, load, ag1, head1, read61⟩ := floatNormalizeLoopL_distance_load hc head room
  obtain ⟨m2, compare, ag2, head2, tested⟩ :=
    floatNormalizeLoopL_distance_compare hc head1 room read61
  have branch := floatNormalizeLoopL_distance_branch hc head2 room tested
  exact ⟨m2, load.trans (compare.trans (Star.one branch)), ag1.trans ag2, head2⟩

#print axioms floatNormalizeLoopL_active_dispatch

set_option maxHeartbeats 800000 in
/-- Execute the first real instruction of either transfer branch. The large
    path loads the doubling factor; the small path loads the denominator seed.
    Both continuations preserve the complete head before changing state. -/
theorem floatNormalizeLoopL_transfer_entry
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {fuel count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r)
    (room : base+6 < K) (large : Bool) :
    ∃ m', Star ⟨pc+(if large then 96 else 352), fp⟩ m ⟨pc+(if large then 112 else 368), fp⟩ m' ∧
      Agree fp base K m m' ∧
      FloatNormalizeHead L ρ W pc fp K base reserved code origin
        originDistance budget target m' fuel count distance q r ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+6))) = some (if large then 2 else 1) := by
  have h := head.pre
  let index : Nat := if large then 6 else 22
  let value : Int := if large then 2 else 1
  have shape : index < code.length ∧ code[index]? = some (ci 1 (base+6) value 0) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    cases large <;> norm_num [index, value, bin2]
  have entry : code[index] = ci 1 (base+6) value 0 := by
    simpa only [List.getElem?_eq_getElem shape.1, Option.some.injEq] using shape.2
  have ins := h.code index shape.1
  rw [entry] at ins
  have singleton : CodeAt m (pc+(if large then 96 else 352)) [ci 1 (base+6) value 0] := by
    intro i hi
    have iz : i = 0 := by simpa using hi
    subst i
    cases large <;> simpa [ci, index] using ins
  let next := write m (slot fp (BitVec.ofNat 64 (base+6))) 8 (BitVec.ofInt 64 value).toNat
  have ag : Agree fp (base+6) K m next := agree_write h.frame.room (by omega) room (BitVec.ofInt 64 value).toNat
  have run : Star ⟨pc+(if large then 96 else 352), fp⟩ m ⟨pc+(if large then 112 else 368), fp⟩ next := by
    have hi := singleton 0 (by simp)
    simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
    have run : Run (step ⟨pc+(if large then 96 else 352), fp⟩) m ⟨pc+(if large then 96 else 352)+16, fp⟩ next := by
      refine run_step hi (by decide) ?_
      simp only [op]
      refine f2_run (t := ⟨pc+(if large then 96 else 352), fp⟩) hi ?_
      simp only [ret1]
      refine f1_run (t := ⟨pc+(if large then 96 else 352), fp⟩) hi ?_
      have sx6 : sx (II.f ((base : Int)+6)) = BitVec.ofNat 64 (base+6) := by
        exact_mod_cast (sx_nat (d := base+6) (by have := h.small; omega))
      rw [sx_lit (by cases large <;> decide : lit32 value = true), sx6]
      exact run_wr64 (wr64_some (h.frame.wr (base+6) room))
    exact Star.one (by cases large <;> simpa [BitVec.add_assoc] using run)
  have preNext : Pre L next pc fp K base code ρ W reserved :=
    ⟨h.ctx, h.small, h.frame.agree ag, h.code.agree ag h.far, h.far,
      envAt_agree h.env ag h.frame (by have := h.ctx; omega) (by omega),
      h.wstab m next h.welt (ag.mono (by omega)), h.wstab⟩
  refine ⟨next, run, ag.mono (by omega), ?_, ?_⟩
  · have reads (i : Nat) (hi : i < base+6) := agree_rd_low ag h.frame.room hi (by omega)
    exact { head with pre := preNext
                      readQ := by rw [reads base (by omega)]; exact head.readQ
                      readR := by rw [reads (base+1) (by omega)]; exact head.readR
                      readDistance := by rw [reads (base+2) (by omega)]; exact head.readDistance
                      readTarget := by rw [reads (base+3) (by omega)]; exact head.readTarget
                      readFuel := by rw [reads (base+4) (by omega)]; exact head.readFuel
                      readCount := by rw [reads (base+5) (by omega)]; exact head.readCount }
  · change (write m (slot fp (BitVec.ofNat 64 (base+6))) 8 (BitVec.ofInt 64 value).toNat).rd64 _ = _
    simp only [Runner.Mem.rd64, write_rd, h.frame.rd (base+6) room, ↓reduceIte,
      le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    cases large <;> rfl

#print axioms floatNormalizeLoopL_transfer_entry

end
end Gabbro.Stage0.Senke
