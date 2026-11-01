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

/-- Dispatch from the actual distance-test result to the emitted transfer paths. -/
set_option maxHeartbeats 800000 in
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

set_option maxHeartbeats 800000 in
/-- Execute the small-branch denominator shift from the actual seed and
    distance words, preserving the complete head and its six state slots. -/
theorem floatNormalizeLoopL_small_denominator
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {fuel count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r)
    (room : base+7 < K) (small : distance ≤ 61)
    (loaded : m.rd64 (slot fp (BitVec.ofNat 64 (base+6))) = some 1) :
    ∃ m', Star ⟨pc+368, fp⟩ m ⟨pc+384, fp⟩ m' ∧
      Agree fp base K m m' ∧
      FloatNormalizeHead L ρ W pc fp K base reserved code origin
        originDistance budget target m' fuel count distance q r ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+7))) =
        some (BitVec.ofInt 64 ((2 : Int)^distance)) := by
  have h := head.pre
  have shape : 23 < code.length ∧
      code[23]? = some (ci 11 (base+7) (base+6) (base+2)) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have entry : code[23] = ci 11 (base+7) (base+6) (base+2) := by
    simpa only [List.getElem?_eq_getElem shape.1, Option.some.injEq] using shape.2
  have ins := h.code 23 shape.1
  rw [entry] at ins
  simp only [ci] at ins
  let value := BitVec.ofInt 64 ((2 : Int)^distance)
  let next := write m (slot fp (BitVec.ofNat 64 (base+7))) 8 value.toNat
  have ag : Agree fp (base+7) K m next := agree_write h.frame.room (by omega) room value.toNat
  have sx6 : sx (II.f ((base : Int)+6)) = BitVec.ofNat 64 (base+6) := by
    exact_mod_cast (sx_nat (d := base+6) (by have := h.small; omega))
  have sx2 : sx (II.f ((base : Int)+2)) = BitVec.ofNat 64 (base+2) := by
    exact_mod_cast (sx_nat (d := base+2) (by have := h.small; omega))
  have sx7 : sx (II.f ((base : Int)+7)) = BitVec.ofNat 64 (base+7) := by
    exact_mod_cast (sx_nat (d := base+7) (by have := h.small; omega))
  have result : (1 : Runner.W) <<< ((BitVec.ofNat 64 distance).toNat % 64) = value := by
    have shift : (BitVec.ofNat 64 distance).toNat % 64 = distance := by
      simp only [BitVec.toNat_ofNat]
      omega
    rw [shift]
    change (1 : Runner.W) <<< distance = BitVec.ofInt 64 ((2 : Int)^distance)
    rw [show (2 : Int)^distance = ((2^distance : Nat) : Int) by simp, BitVec.ofInt_natCast]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have comparison : Run (step ⟨pc+368, fp⟩) m ⟨pc+384, fp⟩ next := by
    have wr : m.wr64 (slot fp (sx (II.f ((base : Int)+7)))) value = some next := by
      rw [sx7]; exact wr64_some (h.frame.wr (base+7) room)
    have run := run_step (t := ⟨pc+368, fp⟩) ins (by decide)
      (run_bin (g := fun a b => some (a <<< (b.toNat % 64))) ins
        (by rw [sx6]; exact loaded) (by rw [sx2]; exact head.readDistance)
        (congrArg some result) wr)
    simpa [nxt, BitVec.add_assoc] using run
  have codeNext := h.code.agree ag h.far
  have preNext : Pre L next pc fp K base code ρ W reserved :=
    ⟨h.ctx, h.small, h.frame.agree ag, codeNext, h.far,
      envAt_agree h.env ag h.frame (by have := h.ctx; omega) (by omega),
      h.wstab m next h.welt (ag.mono (by omega)), h.wstab⟩
  refine ⟨next, Star.one comparison, ag.mono (by omega), ?_, ?_⟩
  · have reads (i : Nat) (hi : i < base+7) := agree_rd_low ag h.frame.room hi (by omega)
    exact { head with pre := preNext
                      readQ := by rw [reads base (by omega)]; exact head.readQ
                      readR := by rw [reads (base+1) (by omega)]; exact head.readR
                      readDistance := by rw [reads (base+2) (by omega)]; exact head.readDistance
                      readTarget := by rw [reads (base+3) (by omega)]; exact head.readTarget
                      readFuel := by rw [reads (base+4) (by omega)]; exact head.readFuel
                      readCount := by rw [reads (base+5) (by omega)]; exact head.readCount }

  · change (write m (slot fp (BitVec.ofNat 64 (base+7))) 8 value.toNat).rd64 _ = some value
    simp only [Runner.Mem.rd64, write_rd, h.frame.rd (base+7) room, ↓reduceIte,
      le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]

#print axioms floatNormalizeLoopL_small_denominator

/-- Continue the proved dispatcher through the real small-branch seed and
    denominator instructions; no execution prefix is restarted. -/
theorem floatNormalizeLoopL_small_dispatch
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {fuel count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r)
    (room : base+7 < K) (small : distance ≤ 61) :
    ∃ m', Star ⟨pc+48, fp⟩ m ⟨pc+384, fp⟩ m' ∧
      Agree fp base K m m' ∧
      FloatNormalizeHead L ρ W pc fp K base reserved code origin
        originDistance budget target m' fuel count distance q r ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+7))) =
        some (BitVec.ofInt 64 ((2 : Int)^distance)) := by
  obtain ⟨m1, dispatch, ag1, head1⟩ := floatNormalizeLoopL_active_dispatch hc head (by omega)
  have dispatch' : Star ⟨pc+48, fp⟩ m ⟨pc+352, fp⟩ m1 := by
    simpa [show ¬ 61 < distance by omega] using dispatch
  obtain ⟨m2, seed, ag2, head2, loaded⟩ :=
    floatNormalizeLoopL_transfer_entry hc head1 (by omega) false
  obtain ⟨m3, shift, ag3, head3, den⟩ :=
    floatNormalizeLoopL_small_denominator hc head2 room small (by simpa using loaded)
  have seed' : Star ⟨pc+352, fp⟩ m1 ⟨pc+368, fp⟩ m2 := by simpa using seed
  exact ⟨m3, dispatch'.trans (seed'.trans shift),
    ag1.trans (ag2.trans ag3), head3, den⟩

#print axioms floatNormalizeLoopL_small_dispatch

set_option maxHeartbeats 800000 in
/-- The large continuation changes the actual quotient word. Every other
    frame read is retained, as are code, environment and the external world.
    The old head is deliberately not asserted after this state mutation. -/
theorem floatNormalizeLoopL_large_double
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {fuel count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r)
    (room : base+6 < K)
    (loaded : m.rd64 (slot fp (BitVec.ofNat 64 (base+6))) = some 2)
    (active : q < target) :
    ∃ m', Star ⟨pc+112, fp⟩ m ⟨pc+128, fp⟩ m' ∧
      Agree fp base K m m' ∧
      Pre L m' pc fp K base code ρ W reserved ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 base)) = some (BitVec.ofInt 64 (2*q)) ∧
      (∀ i, i < K → i ≠ base →
        m'.rd64 (slot fp (BitVec.ofNat 64 i)) =
          m.rd64 (slot fp (BitVec.ofNat 64 i))) ∧
      0 ≤ 2*q ∧ 2*q < 2^61 := by
  have h := head.pre
  have shape : 7 < code.length ∧ code[7]? = some (ci 5 base base (base+6)) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have entry : code[7] = ci 5 base base (base+6) := by
    simpa only [List.getElem?_eq_getElem shape.1, Option.some.injEq] using shape.2
  have ins := h.code 7 shape.1
  rw [entry] at ins
  simp only [ci] at ins
  let value := BitVec.ofInt 64 (2*q)
  let next := write m (slot fp (BitVec.ofNat 64 base)) 8 value.toNat
  have ag : Agree fp base K m next := agree_write h.frame.room (by omega) (by omega) value.toNat
  have sx0 : sx (II.f (base : Int)) = BitVec.ofNat 64 base := sx_nat (by have := h.small; omega)
  have sx6 : sx (II.f ((base : Int)+6)) = BitVec.ofNat 64 (base+6) := by
    exact_mod_cast (sx_nat (d := base+6) (by have := h.small; omega))
  have result : BitVec.ofInt 64 q * (2 : Runner.W) = value := by
    change BitVec.ofInt 64 q * BitVec.ofInt 64 2 = BitVec.ofInt 64 (2*q)
    rw [← BitVec.ofInt_mul, Int.mul_comm]
  have run : Run (step ⟨pc+112, fp⟩) m ⟨pc+128, fp⟩ next := by
    have wr : m.wr64 (slot fp (sx (II.f (base : Int)))) value = some next := by
      rw [sx0]; exact wr64_some (h.frame.wr base (by omega))
    have run := run_step (t := ⟨pc+112, fp⟩) ins (by decide)
      (run_bin (g := fun a b => some (a*b)) ins
        (by rw [sx0]; exact head.readQ) (by rw [sx6]; exact loaded)
        (congrArg some result) wr)
    simpa [nxt, BitVec.add_assoc] using run
  have preNext : Pre L next pc fp K base code ρ W reserved :=
    ⟨h.ctx, h.small, h.frame.agree ag, h.code.agree ag h.far, h.far,
      envAt_agree h.env ag h.frame h.ctx (by omega),
      h.wstab m next h.welt (ag.mono (by omega)), h.wstab⟩
  refine ⟨next, Star.one run, ag, preNext, ?_, ?_,
    floatNormalizeLoop_large_word_bounds q target head.quotient.1 active head.targetBound.2⟩
  · change (write m (slot fp (BitVec.ofNat 64 base)) 8 value.toNat).rd64 _ = some value
    simp only [Runner.Mem.rd64, write_rd, h.frame.rd base (by omega), ↓reduceIte,
      le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro i hi ne
    apply rd64_write_far
    have a := slot_toNat (fp := fp) (i := i) h.frame.room hi
    have b := slot_toNat (fp := fp) (i := base) h.frame.room (show base < K by omega)
    unfold Far
    simp only [a, b]
    have hr := h.frame.room
    omega

#print axioms floatNormalizeLoopL_large_double

/-- Continue the retained dispatcher through the first state-changing large
    instruction. The quotient is doubled and the other five state words retain
    their exact meanings; this boundary is inside the active iteration. -/
theorem floatNormalizeLoopL_large_dispatch
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {fuel count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r)
    (room : base+6 < K) (large : 61 < distance) (active : q < target) :
    ∃ m', Star ⟨pc+48, fp⟩ m ⟨pc+128, fp⟩ m' ∧
      Agree fp base K m m' ∧ Pre L m' pc fp K base code ρ W reserved ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 base)) = some (BitVec.ofInt 64 (2*q)) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+1))) = some (BitVec.ofInt 64 r) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+2))) = some (BitVec.ofNat 64 distance) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+3))) = some (BitVec.ofInt 64 target) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+4))) = some (BitVec.ofNat 64 fuel) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+5))) = some (BitVec.ofNat 64 count) ∧
      0 ≤ 2*q ∧ 2*q < 2^61 := by
  obtain ⟨m1, dispatch, ag1, head1⟩ := floatNormalizeLoopL_active_dispatch hc head room
  have dispatch' : Star ⟨pc+48, fp⟩ m ⟨pc+96, fp⟩ m1 := by
    simpa [large] using dispatch
  obtain ⟨m2, entry, ag2, head2, loaded⟩ :=
    floatNormalizeLoopL_transfer_entry hc head1 room true
  obtain ⟨m3, double, ag3, pre3, readQ, kept, bounds⟩ :=
    floatNormalizeLoopL_large_double hc head2 room (by simpa using loaded) active
  have entry' : Star ⟨pc+96, fp⟩ m1 ⟨pc+112, fp⟩ m2 := by simpa using entry
  refine ⟨m3, dispatch'.trans (entry'.trans double), ag1.trans (ag2.trans ag3),
    pre3, readQ, ?_, ?_, ?_, ?_, ?_, bounds⟩
  · rw [kept (base+1) (by omega) (by omega)]; exact head2.readR
  · rw [kept (base+2) (by omega) (by omega)]; exact head2.readDistance
  · rw [kept (base+3) (by omega) (by omega)]; exact head2.readTarget
  · rw [kept (base+4) (by omega) (by omega)]; exact head2.readFuel
  · rw [kept (base+5) (by omega) (by omega)]; exact head2.readCount

#print axioms floatNormalizeLoopL_large_dispatch

end
end Gabbro.Stage0.Senke
