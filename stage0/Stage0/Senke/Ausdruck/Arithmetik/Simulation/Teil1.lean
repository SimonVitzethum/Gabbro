/- Whole-loop induction for the emitted normalization block. -/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Simulation.Teil1a

public import Stage0.Senke.Ausdruck.Arithmetik.Schleife
public import Stage0.Senke.Ausdruck.Quant.Frame
public import Stage0.Senke.Anweisung.SchleifeTeile
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith

@[expose] public section



namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem

section
variable [Kern] {D : Deklaration} {L : Lay D} {Γ : Ctx}
    {ρ : Env D Γ} {W : Runner.Mem → Prop} {pc fp : Runner.W}
    {K base top reserved : Nat} {code : List II} {origin target : Int}
    {originDistance budget : Nat}
set_option maxHeartbeats 800000 in
/-- Execute the actual positive-fuel, active-target prefix. The comparison
    temporary becomes one; all six state reads and the complete head survive. -/
theorem floatNormalizeLoopL_active_entry
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {fuel count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r)
    (room : base+6 < K) (positive : 0 < fuel) (active : q < target) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + 48, fp⟩ m' ∧
      Agree fp base K m m' ∧
      FloatNormalizeHead L ρ W pc fp K base reserved code origin
        originDistance budget target m' fuel count distance q r := by
  have h := head.pre
  have shape : 2 < code.length ∧
      code[1]? = some (ci 13 (base+6) base (base+3)) ∧
      code[2]? = some (ci 19 (base+6) ((16*(code.length-2) : Nat) : Int) 0) ∧
      lit32 (16*(code.length-2 : Nat)) = true := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2, lit32]
  have ins1 := h.code 1 (by omega)
  have ins2 := h.code 2 shape.1
  have e1 : code[1] = ci 13 (base+6) base (base+3) := by
    simpa only [List.getElem?_eq_getElem (by omega : 1 < code.length), Option.some.injEq] using shape.2.1
  have e2 : code[2] = ci 19 (base+6) ((16*(code.length-2) : Nat) : Int) 0 := by
    simpa only [List.getElem?_eq_getElem shape.1, Option.some.injEq] using shape.2.2.1
  rw [e1] at ins1
  simp only [ci] at ins1
  rw [e2] at ins2
  have small := h.small
  have entry := floatNormalizeLoopL_positive_entry hc h (by omega) head.readFuel
    (by intro eq; have fw := head.fuelWord; have := congrArg BitVec.toNat eq; change fuel % 2^64 = 0 at this;  omega)
  let next := write m (slot fp (BitVec.ofNat 64 (base+6))) 8 1
  have ag : Agree fp (base+6) K m next := agree_write h.frame.room (by omega) room 1
  have comparisonOne : Runner.IR.bool ((BitVec.ofInt 64 q).slt (BitVec.ofInt 64 target)) = 1 := by
    rw [slt_in (by have := head.quotient; constructor <;> omega)
      (by have := head.targetBound; constructor <;> omega)]
    simp [Runner.IR.bool, active]
  have sx0 : sx (II.f (base : Int)) = BitVec.ofNat 64 base := sx_nat (by omega)
  have sx3 : sx (II.f ((base : Int)+3)) = BitVec.ofNat 64 (base+3) := by
    exact_mod_cast (sx_nat (d := base+3) (by omega))
  have sx6 : sx (II.f ((base : Int)+6)) = BitVec.ofNat 64 (base+6) := by
    exact_mod_cast (sx_nat (d := base+6) (by omega))
  have compare : Run (step ⟨pc+16, fp⟩) m ⟨pc+32, fp⟩ next := by
    have ra : m.rd64 (slot fp (sx (II.f (base : Int)))) = some (BitVec.ofInt 64 q) := by
      rw [sx0]; exact head.readQ
    have rb : m.rd64 (slot fp (sx (II.f ((base : Int)+3)))) = some (BitVec.ofInt 64 target) := by
      rw [sx3]; exact head.readTarget
    have wr : m.wr64 (slot fp (sx (II.f ((base : Int)+6)))) 1 = some next := by
      rw [sx6]; exact wr64_some (h.frame.wr (base+6) room)
    have run := run_step (t := ⟨pc+16, fp⟩) ins1 (by decide)
      (run_bin (g := fun a b => some (Runner.IR.bool (a.slt b))) ins1 ra rb
        (congrArg some comparisonOne) wr)
    simpa only [nxt, show (16 : Runner.W)+16 = 32 from rfl, BitVec.add_assoc] using run
  have codeNext := h.code.agree ag h.far
  have insNext := codeNext 2 shape.1
  rw [e2] at insNext
  simp only [ci] at insNext
  have readOne : next.rd64 (slot fp (BitVec.ofNat 64 (base+6))) = some 1 := by
    change (write m (slot fp (BitVec.ofNat 64 (base+6))) 8 (1 : Runner.W).toNat).rd64 _ = _
    simp only [Runner.Mem.rd64, write_rd, h.frame.rd (base+6) room, ↓reduceIte,
      le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have branch : Run (step ⟨pc+32, fp⟩) next ⟨pc+48, fp⟩ next := by
    have run := run_step (t := ⟨pc+32, fp⟩) insNext (by decide)
      (run_brz_ne insNext (by rw [sx6]; exact readOne) (by decide))
    simpa only [nxt, show (32 : Runner.W)+16 = 48 from rfl, BitVec.add_assoc] using run
  have preNext : Pre L next pc fp K base code ρ W reserved :=
    ⟨h.ctx, h.small, h.frame.agree ag, codeNext, h.far,
      envAt_agree h.env ag h.frame (by have := h.ctx; omega) (by omega),
      h.wstab m next h.welt (ag.mono (by omega)), h.wstab⟩
  refine ⟨next, (Star.one entry).trans ((Star.one compare).trans (Star.one branch)),
    ag.mono (by omega), ?_⟩
  have reads (i : Nat) (hi : i < base+6) := agree_rd_low ag h.frame.room hi (by omega)
  exact { head with pre := preNext
                    readQ := by rw [reads base (by omega)]; exact head.readQ
                    readR := by rw [reads (base+1) (by omega)]; exact head.readR
                    readDistance := by rw [reads (base+2) (by omega)]; exact head.readDistance
                    readTarget := by rw [reads (base+3) (by omega)]; exact head.readTarget
                    readFuel := by rw [reads (base+4) (by omega)]; exact head.readFuel
                    readCount := by rw [reads (base+5) (by omega)]; exact head.readCount }

#print axioms floatNormalizeLoopL_active_entry

set_option maxHeartbeats 800000 in
/-- Continue the actual active entry with the distance threshold load.
    The six state words and the entire head contract survive the temporary write. -/
theorem floatNormalizeLoopL_distance_load
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {fuel count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r)
    (room : base+6 < K) :
    ∃ m', Star ⟨pc+48, fp⟩ m ⟨pc+64, fp⟩ m' ∧
      Agree fp base K m m' ∧
      FloatNormalizeHead L ρ W pc fp K base reserved code origin
        originDistance budget target m' fuel count distance q r ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+6))) = some 61 := by
  have h := head.pre
  have shape : 3 < code.length ∧ code[3]? = some (ci 1 (base+6) 61 0) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have entry : code[3] = ci 1 (base+6) 61 0 := by
    simpa only [List.getElem?_eq_getElem shape.1, Option.some.injEq] using shape.2
  have ins := h.code 3 shape.1
  rw [entry] at ins
  have singleton : CodeAt m (pc+48) [ci 1 (base+6) 61 0] := by
    intro i hi
    have iz : i = 0 := by simpa using hi
    subst i
    simpa [ci] using ins
  let next := write m (slot fp (BitVec.ofNat 64 (base+6))) 8 61
  have ag : Agree fp (base+6) K m next := agree_write h.frame.room (by omega) room 61
  have run : Star ⟨pc+48, fp⟩ m ⟨pc+64, fp⟩ next := by
    have hi := singleton 0 (by simp)
    simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
    have run : Run (step ⟨pc+48, fp⟩) m ⟨pc+48+16, fp⟩ next := by
      refine run_step hi (by decide) ?_
      simp only [op]
      refine f2_run (t := ⟨pc+48, fp⟩) hi ?_
      simp only [ret1]
      refine f1_run (t := ⟨pc+48, fp⟩) hi ?_
      have sx6 : sx (II.f ((base : Int)+6)) = BitVec.ofNat 64 (base+6) := by
        exact_mod_cast (sx_nat (d := base+6) (by have := h.small; omega))
      rw [sx_lit (by decide : lit32 61 = true), sx6]
      exact run_wr64 (wr64_some (h.frame.wr (base+6) room))
    exact Star.one (by simpa [BitVec.add_assoc] using run)
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
  · change (write m (slot fp (BitVec.ofNat 64 (base+6))) 8 (61 : Runner.W).toNat).rd64 _ = _
    simp only [Runner.Mem.rd64, write_rd, h.frame.rd (base+6) room, ↓reduceIte,
      le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]

#print axioms floatNormalizeLoopL_distance_load

set_option maxHeartbeats 800000 in
/-- Compare the loaded threshold with the actual distance word. -/
theorem floatNormalizeLoopL_distance_compare
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {fuel count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r)
    (room : base+6 < K)
    (loaded : m.rd64 (slot fp (BitVec.ofNat 64 (base+6))) = some 61) :
    ∃ m', Star ⟨pc+64, fp⟩ m ⟨pc+80, fp⟩ m' ∧
      Agree fp base K m m' ∧
      FloatNormalizeHead L ρ W pc fp K base reserved code origin
        originDistance budget target m' fuel count distance q r ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+6))) =
        some (Runner.IR.bool (decide (61 < distance))) := by
  have h := head.pre
  have shape : 4 < code.length ∧
      code[4]? = some (ci 13 (base+6) (base+6) (base+2)) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have entry : code[4] = ci 13 (base+6) (base+6) (base+2) := by
    simpa only [List.getElem?_eq_getElem shape.1, Option.some.injEq] using shape.2
  have ins := h.code 4 shape.1
  rw [entry] at ins
  simp only [ci] at ins
  let value := Runner.IR.bool (decide (61 < distance))
  let next := write m (slot fp (BitVec.ofNat 64 (base+6))) 8 value.toNat
  have ag : Agree fp (base+6) K m next := agree_write h.frame.room (by omega) room value.toNat
  have sx6 : sx (II.f ((base : Int)+6)) = BitVec.ofNat 64 (base+6) := by
    exact_mod_cast (sx_nat (d := base+6) (by have := h.small; omega))
  have sx2 : sx (II.f ((base : Int)+2)) = BitVec.ofNat 64 (base+2) := by
    exact_mod_cast (sx_nat (d := base+2) (by have := h.small; omega))
  have result : Runner.IR.bool ((61 : Runner.W).slt (BitVec.ofNat 64 distance)) = value := by
    have eq : BitVec.ofNat 64 distance = BitVec.ofInt 64 (distance : Int) := by simp
    rw [eq]
    change Runner.IR.bool ((BitVec.ofInt 64 61).slt (BitVec.ofInt 64 (distance : Int))) = value
    rw [slt_in (by constructor <;> norm_num)
      (by have := head.distanceWord; constructor <;> omega)]
    simp [value]
  have comparison : Run (step ⟨pc+64, fp⟩) m ⟨pc+80, fp⟩ next := by
    have wr : m.wr64 (slot fp (sx (II.f ((base : Int)+6)))) value = some next := by
      rw [sx6]; exact wr64_some (h.frame.wr (base+6) room)
    have run := run_step (t := ⟨pc+64, fp⟩) ins (by decide)
      (run_bin (g := fun a b => some (Runner.IR.bool (a.slt b))) ins
        (by rw [sx6]; exact loaded) (by rw [sx2]; exact head.readDistance)
        (congrArg some result) wr)
    simpa [nxt, BitVec.add_assoc] using run
  have codeNext := h.code.agree ag h.far
  have preNext : Pre L next pc fp K base code ρ W reserved :=
    ⟨h.ctx, h.small, h.frame.agree ag, codeNext, h.far,
      envAt_agree h.env ag h.frame (by have := h.ctx; omega) (by omega),
      h.wstab m next h.welt (ag.mono (by omega)), h.wstab⟩
  refine ⟨next, Star.one comparison, ag.mono (by omega), ?_, ?_⟩
  · have reads (i : Nat) (hi : i < base+6) := agree_rd_low ag h.frame.room hi (by omega)
    exact { head with pre := preNext
                      readQ := by rw [reads base (by omega)]; exact head.readQ
                      readR := by rw [reads (base+1) (by omega)]; exact head.readR
                      readDistance := by rw [reads (base+2) (by omega)]; exact head.readDistance
                      readTarget := by rw [reads (base+3) (by omega)]; exact head.readTarget
                      readFuel := by rw [reads (base+4) (by omega)]; exact head.readFuel
                      readCount := by rw [reads (base+5) (by omega)]; exact head.readCount }

  · change (write m (slot fp (BitVec.ofNat 64 (base+6))) 8 value.toNat).rd64 _ = some value
    simp only [Runner.Mem.rd64, write_rd, h.frame.rd (base+6) room, ↓reduceIte,
      le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]

#print axioms floatNormalizeLoopL_distance_compare

end
end Gabbro.Stage0.Senke
