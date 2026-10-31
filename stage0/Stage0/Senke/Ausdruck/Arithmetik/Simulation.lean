/- Whole-loop induction for the emitted normalization block. -/
import Stage0.Senke.Ausdruck.Arithmetik.Schleife
import Stage0.Senke.Ausdruck.Quant.Frame
import Stage0.Senke.Anweisung.SchleifeTeile
import Mathlib.Tactic.IntervalCases

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem

/-- The head invariant keeps the actual fetch/frame/read contract together
    with exact reconstruction. Multiplication by powers of two avoids rational
    arithmetic while allowing the large branch to reduce the distance.
    `origin` is the original numerator at denominator `2^originDistance`.
    `budget` includes both completed and remaining transfers. -/
structure FloatNormalizeHead {D : Deklaration} (L : Lay D) {Γ : Ctx}
    (ρ : Env D Γ) (W : Runner.Mem → Prop) (pc fp : Runner.W)
    (K base reserved : Nat) (code : List II) (origin : Int)
    (originDistance budget : Nat) (target : Int) (m : Runner.Mem)
    (fuel count distance : Nat) (q r : Int) : Prop where
  pre : Pre L m pc fp K base code ρ W reserved
  room : base+5 < K
  fuelWord : fuel < 2^63
  countWord : count < 2^63
  distanceWord : distance < 2^63
  quotient : 0 ≤ q ∧ q < 2^61
  remainder : 0 ≤ r ∧ r < 2^63 ∧ r < (2 : Int)^distance
  targetBound : 0 ≤ target ∧ target ≤ 2^60
  readQ : m.rd64 (slot fp (BitVec.ofNat 64 base)) = some (BitVec.ofInt 64 q)
  readR : m.rd64 (slot fp (BitVec.ofNat 64 (base+1))) = some (BitVec.ofInt 64 r)
  readDistance : m.rd64 (slot fp (BitVec.ofNat 64 (base+2))) = some (BitVec.ofNat 64 distance)
  readTarget : m.rd64 (slot fp (BitVec.ofNat 64 (base+3))) = some (BitVec.ofInt 64 target)
  readFuel : m.rd64 (slot fp (BitVec.ofNat 64 (base+4))) = some (BitVec.ofNat 64 fuel)
  readCount : m.rd64 (slot fp (BitVec.ofNat 64 (base+5))) = some (BitVec.ofNat 64 count)
  conservedBudget : count + fuel = budget
  reconstruction : (q * 2^distance + r) * 2^originDistance =
    origin * 2^(count+distance)

section
variable [Kern] {D : Deklaration} {L : Lay D} {Γ : Ctx}
    {ρ : Env D Γ} {W : Runner.Mem → Prop} {pc fp : Runner.W}
    {K base top reserved : Nat} {code : List II} {origin target : Int}
    {originDistance budget : Nat}

/-- The initial zero transfer count derives the total budget ceiling from the
    existing fuel word bound. Later heads use conservation, not a fresh bound
    on each increment in isolation. -/
theorem FloatNormalizeHead.initial_budget_bound
    {m : Runner.Mem} {fuel distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel 0 distance q r) :
    budget < 2^63 := by
  have := head.conservedBudget
  have := head.fuelWord
  omega

/-- A positive remaining budget pays for the next counter increment without
    signed overflow, and decrement/increment preserves the same total. -/
theorem FloatNormalizeHead.active_budget_bounds
    {m : Runner.Mem} {n count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m (n+1) count distance q r)
    (ceiling : budget < 2^63) :
    count+1 < 2^63 ∧ n < 2^63 ∧ (count+1)+n = budget := by
  have := head.conservedBudget
  omega

/-- Joint resource witness with both a completed and a pending transfer. -/
theorem floatNormalizeLoop_budget_zeuge :
    (1 : Nat)+1 < 2^63 ∧ (1 : Nat) < 2^63 ∧ ((1 : Nat)+1)+1 = 3 := by
  decide +kernel

#print axioms FloatNormalizeHead.initial_budget_bound
#print axioms FloatNormalizeHead.active_budget_bounds
#print axioms floatNormalizeLoop_budget_zeuge

/-- The last instruction of the actual emitted body returns to its head.
    This discharges the backedge PC obligation independently of body writes;
    the iteration proof must still restore the head precondition first. -/
theorem floatNormalizeLoopL_backedge
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem}
    (fetch : CodeAt m pc code) :
    Run (step ⟨pc + BitVec.ofNat 64 (16*(code.length-1)), fp⟩) m ⟨pc, fp⟩ m := by
  have shape : 0 < code.length ∧ code[code.length-1]? =
      some (ci 18 (-(16*((code.length-1 : Nat) : Int))) 0 0) ∧
      lit32 (-(16*((code.length-1 : Nat) : Int))) = true := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2, lit32]
  have index : code.length-1 < code.length := by omega
  have instruction := fetch (code.length-1) index
  have entry : code[code.length-1] =
      ci 18 (-(16*((code.length-1 : Nat) : Int))) 0 0 := by
    simpa only [List.getElem?_eq_getElem index, Option.some.injEq] using shape.2.1
  rw [entry] at instruction
  have run := run_step (t := ⟨pc + BitVec.ofNat 64 (16*(code.length-1)), fp⟩)
    instruction (by simp [ci]) (run_jmp instruction)
  have offset : sx (II.f (-(16*((code.length-1 : Nat) : Int)))) =
      -BitVec.ofNat 64 (16*(code.length-1)) := by
    rw [sx_lit shape.2.2, BitVec.ofInt_neg]
    congr 1
  simpa [ci, offset, ← BitVec.sub_eq_add_neg, BitVec.add_sub_cancel] using run

#print axioms floatNormalizeLoopL_backedge

set_option maxHeartbeats 800000 in
/-- Execute the emitted target test and exit. Only the comparison temporary
    changes; all six state words, frame permissions, code and environment survive. -/
theorem floatNormalizeLoopL_target_exit
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {fuel count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r)
    (room : base+6 < K) (positive : 0 < fuel) (stopped : target ≤ q) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16*code.length), fp⟩ m' ∧
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
  let next := write m (slot fp (BitVec.ofNat 64 (base+6))) 8 0
  have ag : Agree fp (base+6) K m next := agree_write h.frame.room (by omega) room 0
  have comparisonZero : Runner.IR.bool ((BitVec.ofInt 64 q).slt (BitVec.ofInt 64 target)) = 0 := by
    rw [slt_in (by have := head.quotient; constructor <;> omega)
      (by have := head.targetBound; constructor <;> omega)]
    simp [Runner.IR.bool, show ¬ q < target by omega]
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
    have wr : m.wr64 (slot fp (sx (II.f ((base : Int)+6)))) 0 = some next := by
      rw [sx6]; exact wr64_some (h.frame.wr (base+6) room)
    have run := run_step (t := ⟨pc+16, fp⟩) ins1 (by decide)
      (run_bin (g := fun a b => some (Runner.IR.bool (a.slt b))) ins1 ra rb
        (congrArg some comparisonZero) wr)
    simpa only [nxt, show (16 : Runner.W)+16 = 32 from rfl, BitVec.add_assoc] using run
  have codeNext := h.code.agree ag h.far
  have insNext := codeNext 2 shape.1
  rw [e2] at insNext
  simp only [ci] at insNext
  have readZero : next.rd64 (slot fp (BitVec.ofNat 64 (base+6))) = some 0 := by
    change (write m (slot fp (BitVec.ofNat 64 (base+6))) 8 (0 : Runner.W).toNat).rd64 _ = _
    simp only [Runner.Mem.rd64, write_rd, h.frame.rd (base+6) room, ↓reduceIte,
      le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have jump := run_step (t := ⟨pc + BitVec.ofNat 64 (16*2), fp⟩) insNext (by decide)
    (run_brz_zero (t := ⟨pc + BitVec.ofNat 64 (16*2), fp⟩) insNext
      (by rw [sx6]; exact readZero))
  have offset : sx (II.f ((16*(code.length-2) : Nat) : Int)) =
      BitVec.ofNat 64 (16*(code.length-2)) := by
    rw [sx_lit (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using shape.2.2.2)]
    exact BitVec.ofInt_natCast 64 _
  have pcEnd : pc + BitVec.ofNat 64 (16*2) + BitVec.ofNat 64 (16*(code.length-2)) =
      pc + BitVec.ofNat 64 (16*code.length) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  have exitRun : Run (step ⟨pc+32, fp⟩) next
      ⟨pc + BitVec.ofNat 64 (16*code.length), fp⟩ next := by
    have pcEnd32 : pc + 32 + BitVec.ofNat 64 (16*(code.length-2)) =
        pc + BitVec.ofNat 64 (16*code.length) := pcEnd
    simpa only [ci, offset, show BitVec.ofNat 64 (16*2) = (32 : Runner.W) from rfl, pcEnd32] using jump
  have preNext : Pre L next pc fp K base code ρ W reserved :=
    ⟨h.ctx, h.small, h.frame.agree ag, codeNext, h.far,
      envAt_agree h.env ag h.frame (by have := h.ctx; omega) (by omega),
      h.wstab m next h.welt (ag.mono (by omega)), h.wstab⟩
  refine ⟨next, (Star.one entry).trans ((Star.one compare).trans (Star.one exitRun)),
    ag.mono (by omega), ?_⟩
  have reads (i : Nat) (hi : i < base+6) := agree_rd_low ag h.frame.room hi (by omega)
  exact { head with pre := preNext
                    readQ := by rw [reads base (by omega)]; exact head.readQ
                    readR := by rw [reads (base+1) (by omega)]; exact head.readR
                    readDistance := by rw [reads (base+2) (by omega)]; exact head.readDistance
                    readTarget := by rw [reads (base+3) (by omega)]; exact head.readTarget
                    readFuel := by rw [reads (base+4) (by omega)]; exact head.readFuel
                    readCount := by rw [reads (base+5) (by omega)]; exact head.readCount }

#print axioms floatNormalizeLoopL_target_exit

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

set_option maxHeartbeats 800000 in
/-- Continue the mutated large state through the seed load and distance write.
    Only the distance and scratch seed change; in particular the doubled
    quotient and all remaining state words survive these actual instructions. -/
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

set_option maxHeartbeats 800000 in
/-- Materialize the carry threshold only after the actual distance guard. -/
theorem floatNormalizeLoopL_large_carry_denominator
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {distance : Nat}
    (h : Pre L m pc fp K base code ρ W reserved)
    (readDistance : m.rd64 (slot fp (BitVec.ofNat 64 (base+2))) =
      some (BitVec.ofNat 64 distance))
    (room : base+7 < K) (small : distance < 63)
    (loaded : m.rd64 (slot fp (BitVec.ofNat 64 (base+6))) = some 1) :
    ∃ m', Star ⟨pc+224, fp⟩ m ⟨pc+240, fp⟩ m' ∧
      Agree fp (base+6) K m m' ∧
      Pre L m' pc fp K base code ρ W reserved ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+7))) =
        some (BitVec.ofInt 64 ((2 : Int)^distance)) := by
  have shape : 14 < code.length ∧
      code[14]? = some (ci 11 (base+7) (base+6) (base+2)) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have entry : code[14] = ci 11 (base+7) (base+6) (base+2) := by
    simpa only [List.getElem?_eq_getElem shape.1, Option.some.injEq] using shape.2
  have ins := h.code 14 shape.1
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
  have comparison : Run (step ⟨pc+224, fp⟩) m ⟨pc+240, fp⟩ next := by
    have wr : m.wr64 (slot fp (sx (II.f ((base : Int)+7)))) value = some next := by
      rw [sx7]; exact wr64_some (h.frame.wr (base+7) room)
    have run := run_step (t := ⟨pc+224, fp⟩) ins (by decide)
      (run_bin (g := fun a b => some (a <<< (b.toNat % 64))) ins
        (by rw [sx6]; exact loaded) (by rw [sx2]; exact readDistance)
        (congrArg some result) wr)
    simpa [nxt, BitVec.add_assoc] using run
  have codeNext := h.code.agree ag h.far
  have preNext : Pre L next pc fp K base code ρ W reserved :=
    ⟨h.ctx, h.small, h.frame.agree ag, codeNext, h.far,
      envAt_agree h.env ag h.frame (by have := h.ctx; omega) (by omega),
      h.wstab m next h.welt (ag.mono (by omega)), h.wstab⟩
  refine ⟨next, Star.one comparison, ag.mono (by omega), preNext, ?_⟩
  change (write m (slot fp (BitVec.ofNat 64 (base+7))) 8 value.toNat).rd64 _ = some value
  simp only [Runner.Mem.rd64, write_rd, h.frame.rd (base+7) room, ↓reduceIte,
      le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]

#print axioms floatNormalizeLoopL_large_carry_denominator

set_option maxHeartbeats 800000 in
theorem floatNormalizeLoopL_large_carry_compare
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {distance : Nat} {r : Int}
    (h : Pre L m pc fp K base code ρ W reserved)
    (bound : 0 ≤ r ∧ r < 2^63) (small : distance < 63)
    (readR : m.rd64 (slot fp (BitVec.ofNat 64 (base+1))) =
      some (BitVec.ofInt 64 r))
    (room : base+6 < K)
    (loaded : m.rd64 (slot fp (BitVec.ofNat 64 (base+7))) = some (BitVec.ofInt 64 ((2 : Int)^distance))) :
    ∃ m', Star ⟨pc+240, fp⟩ m ⟨pc+256, fp⟩ m' ∧
      Agree fp (base+6) K m m' ∧
      Pre L m' pc fp K base code ρ W reserved ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+6))) =
        some (Runner.IR.bool (decide (r < (2 : Int)^distance))) ∧
      (∀ i, i < K → i ≠ base+6 →
        m'.rd64 (slot fp (BitVec.ofNat 64 i)) = m.rd64 (slot fp (BitVec.ofNat 64 i))) := by
  have shape : 15 < code.length ∧
      code[15]? = some (ci 13 (base+6) (base+1) (base+7)) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have entry : code[15] = ci 13 (base+6) (base+1) (base+7) := by
    simpa only [List.getElem?_eq_getElem shape.1, Option.some.injEq] using shape.2
  have ins := h.code 15 shape.1
  rw [entry] at ins
  simp only [ci] at ins
  let value := Runner.IR.bool (decide (r < (2 : Int)^distance))
  let next := write m (slot fp (BitVec.ofNat 64 (base+6))) 8 value.toNat
  have ag : Agree fp (base+6) K m next := agree_write h.frame.room (by omega) room value.toNat
  have sx6 : sx (II.f ((base : Int)+6)) = BitVec.ofNat 64 (base+6) := by
    exact_mod_cast (sx_nat (d := base+6) (by have := h.small; omega))
  have sx2 : sx (II.f ((base : Int)+1)) = BitVec.ofNat 64 (base+1) := by
    exact_mod_cast (sx_nat (d := base+1) (by have := h.small; omega))
  have sx7 : sx (II.f ((base : Int)+7)) = BitVec.ofNat 64 (base+7) := by
    exact_mod_cast (sx_nat (d := base+7) (by have := h.small; omega))
  have powerBound : (2 : Int)^distance ≤ 2^62 := by
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show distance ≤ 62 by omega))
  have powerPositive : (0 : Int) < 2^distance := Int.pow_pos (by decide)
  have result : Runner.IR.bool ((BitVec.ofInt 64 r).slt
      (BitVec.ofInt 64 ((2 : Int)^distance))) = value := by
    rw [slt_in (by constructor <;> omega) (by constructor <;> omega)]
  have comparison : Run (step ⟨pc+240, fp⟩) m ⟨pc+256, fp⟩ next := by
    have wr : m.wr64 (slot fp (sx (II.f ((base : Int)+6)))) value = some next := by
      rw [sx6]; exact wr64_some (h.frame.wr (base+6) room)
    have run := run_step (t := ⟨pc+240, fp⟩) ins (by decide)
      (run_bin (g := fun a b => some (Runner.IR.bool (a.slt b))) ins
        (by rw [sx2]; exact readR) (by rw [sx7]; exact loaded)
        (congrArg some result) wr)
    simpa [nxt, BitVec.add_assoc] using run
  have codeNext := h.code.agree ag h.far
  have preNext : Pre L next pc fp K base code ρ W reserved :=
    ⟨h.ctx, h.small, h.frame.agree ag, codeNext, h.far,
      envAt_agree h.env ag h.frame (by have := h.ctx; omega) (by omega),
      h.wstab m next h.welt (ag.mono (by omega)), h.wstab⟩
  refine ⟨next, Star.one comparison, ag, preNext, ?_, ?_⟩
  · change (write m (slot fp (BitVec.ofNat 64 (base+6))) 8 value.toNat).rd64 _ = some value
    simp only [Runner.Mem.rd64, write_rd, h.frame.rd (base+6) room, ↓reduceIte,
        le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]


  · intro i hi ne
    change (write m (slot fp (BitVec.ofNat 64 (base+6))) 8 value.toNat).rd64 _ = _
    apply rd64_write_far
    have a := slot_toNat (fp := fp) (i := i) h.frame.room hi
    have b := slot_toNat (fp := fp) (i := base+6) h.frame.room room
    unfold Far
    simp only [a, b]
    have hr := h.frame.room
    omega

#print axioms floatNormalizeLoopL_large_carry_compare

/-- Connected execution through the large carry decision preserves every
    state word already established at byte 160. -/
theorem floatNormalizeLoopL_large_carry_tested
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {fuel count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r)
    (room : base+7 < K) (large : 61 < distance) (active : q < target) :
    ∃ m', Star ⟨pc+48, fp⟩ m
        ⟨pc + (if distance-1 < 63 then 256 else 336), fp⟩ m' ∧
      Agree fp base K m m' ∧ Pre L m' pc fp K base code ρ W reserved ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 base)) = some (BitVec.ofInt 64 (2*q)) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+1))) = some (BitVec.ofInt 64 r) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+2))) = some (BitVec.ofNat 64 (distance-1)) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+3))) = some (BitVec.ofInt 64 target) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+4))) = some (BitVec.ofNat 64 fuel) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+5))) = some (BitVec.ofNat 64 count) ∧
      (0 ≤ 2*q ∧ 2*q < 2^61) ∧
      (distance-1 < 63 → m'.rd64 (slot fp (BitVec.ofNat 64 (base+6))) =
        some (Runner.IR.bool (decide (r < (2 : Int)^(distance-1))))) ∧
      (distance-1 < 63 → m'.rd64 (slot fp (BitVec.ofNat 64 (base+7))) =
        some (BitVec.ofInt 64 ((2 : Int)^(distance-1)))) := by
  obtain ⟨m1, run1, ag1, pre1, rq, rr, rd, rt, rf, rc, bounds⟩ :=
    floatNormalizeLoopL_large_carry_dispatch hc head (by omega) large active
  by_cases guarded : distance-1 < 63
  · obtain ⟨m2, run2, ag2, pre2, seed⟩ := floatNormalizeLoopL_large_carry_seed hc pre1 (by omega)
    have rd2 := rd
    rw [← agree_rd_low ag2 pre1.frame.room (show base+2 < base+6 by omega) (by omega)] at rd2
    obtain ⟨m3, run3, ag3, pre3, den⟩ :=
      floatNormalizeLoopL_large_carry_denominator hc pre2 rd2 room guarded seed
    have rr3 : m3.rd64 (slot fp (BitVec.ofNat 64 (base+1))) = some (BitVec.ofInt 64 r) := by
      rw [agree_rd_low (ag2.trans ag3) pre1.frame.room (by omega) (by omega)]; exact rr
    obtain ⟨m4, run4, ag4, pre4, tested, kept⟩ :=
      floatNormalizeLoopL_large_carry_compare hc pre3 ⟨head.remainder.1, head.remainder.2.1⟩
        guarded rr3 (by omega) den
    have ag := ag2.trans (ag3.trans ag4)
    have reads (i : Nat) (hi : i < base+6) :=
      agree_rd_low ag pre1.frame.room hi (show base+6 ≤ K by omega)
    refine ⟨m4, ?_, ag1.trans (ag.mono (by omega)), pre4, ?_, ?_, ?_, ?_, ?_, ?_, bounds, (fun _ => tested), (fun _ => ?_)⟩
    · have connectedPrefix : Star ⟨pc+48, fp⟩ m ⟨pc+208, fp⟩ m1 := by
        simpa only [guarded, ↓reduceIte] using run1
      simpa only [guarded, ↓reduceIte] using
        connectedPrefix.trans (run2.trans (run3.trans run4))
    · rw [reads base (by omega)]; exact rq
    · rw [reads (base+1) (by omega)]; exact rr
    · rw [reads (base+2) (by omega)]; exact rd
    · rw [reads (base+3) (by omega)]; exact rt
    · rw [reads (base+4) (by omega)]; exact rf
    · rw [reads (base+5) (by omega)]; exact rc
    · rw [kept (base+7) room (by omega)]; exact den
  · exact ⟨m1, by simpa [guarded] using run1, ag1, pre1, rq, rr, rd, rt, rf, rc, bounds, (fun h => (guarded h).elim), (fun h => (guarded h).elim)⟩

#print axioms floatNormalizeLoopL_large_carry_tested

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

/-- Both large paths skip the SMALL code using the emitted jump. -/
theorem floatNormalizeLoopL_large_skip_small
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} (fetch : CodeAt m pc code) :
    Run (step ⟨pc+336, fp⟩) m
      ⟨pc + BitVec.ofNat 64 (16*(code.length-4)), fp⟩ m := by
  have shape : 21 < code.length ∧ 25 ≤ code.length ∧
      code[21]? = some (ci 18 (16*((code.length-25 : Nat) : Int)) 0 0) ∧
      lit32 (16*((code.length-25 : Nat) : Int)) = true := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2, lit32]
  have entry : code[21] = ci 18 (16*((code.length-25 : Nat) : Int)) 0 0 := by
    simpa only [List.getElem?_eq_getElem shape.1, Option.some.injEq] using shape.2.2.1
  have ins := fetch 21 shape.1
  rw [entry] at ins
  have run := run_step (t := ⟨pc+336, fp⟩) ins (by simp [ci]) (run_jmp ins)
  have offset : sx (II.f (16*((code.length-25 : Nat) : Int))) =
      BitVec.ofNat 64 (16*(code.length-25)) := by
    rw [sx_lit shape.2.2.2]
    rw [show 16*((code.length-25 : Nat) : Int) = ((16*(code.length-25) : Nat) : Int) by omega,
      BitVec.ofInt_natCast]
  have total : 336 + 16*(code.length-25) = 16*(code.length-4) := by omega
  have sum : (336 : Runner.W) + BitVec.ofNat 64 (16*(code.length-25)) =
      BitVec.ofNat 64 (16*(code.length-4)) := by
    change BitVec.ofNat 64 336 + _ = _
    rw [← BitVec.ofNat_add, total]
  simpa only [ci, offset, BitVec.add_assoc, sum] using run

#print axioms floatNormalizeLoopL_large_skip_small

/-- Actual execution of both large paths from the established prefix through
    carry arithmetic and the emitted jump to the shared tail. -/
theorem floatNormalizeLoopL_large_to_tail
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {fuel count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r)
    (room : base+8 < K) (large : 61 < distance) (active : q < target) :
    let carry : Runner.W := if distance-1 < 63 then
      1 - Runner.IR.bool (decide (r < (2 : Int)^(distance-1))) else 0
    ∃ m', Star ⟨pc+48, fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16*(code.length-4)), fp⟩ m' ∧
      Agree fp base K m m' ∧ Pre L m' pc fp K base code ρ W reserved ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 base)) = some (BitVec.ofInt 64 (2*q) + carry) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+1))) =
        some (BitVec.ofInt 64 r - BitVec.ofInt 64 ((2 : Int)^(distance-1))*carry) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+2))) = some (BitVec.ofNat 64 (distance-1)) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+3))) = some (BitVec.ofInt 64 target) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+4))) = some (BitVec.ofNat 64 fuel) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+5))) = some (BitVec.ofNat 64 count) := by
  dsimp only
  obtain ⟨m1, run1, ag1, pre1, rq, rr, rd, rt, rf, rc, bounds, tested, den⟩ :=
    floatNormalizeLoopL_large_carry_tested hc head (by omega) large active
  by_cases guarded : distance-1 < 63
  · obtain ⟨m2, run2, ag2, pre2, rq2, rr2, kept⟩ :=
      floatNormalizeLoopL_large_carry_arithmetic hc pre1 room _ _ _ _ rq rr
        (den guarded) (tested guarded)
    have connectedPrefix : Star ⟨pc+48, fp⟩ m ⟨pc+256, fp⟩ m1 := by
      simpa only [guarded, ↓reduceIte] using run1
    refine ⟨m2, connectedPrefix.trans (run2.trans (Star.one
      (floatNormalizeLoopL_large_skip_small hc pre2.code))), ag1.trans ag2, pre2,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [guarded, ↓reduceIte] using rq2
    · simpa only [guarded, ↓reduceIte] using rr2
    · rw [kept (base+2) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact rd
    · rw [kept (base+3) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact rt
    · rw [kept (base+4) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact rf
    · rw [kept (base+5) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact rc
  · have connectedPrefix : Star ⟨pc+48, fp⟩ m ⟨pc+336, fp⟩ m1 := by
      simpa only [guarded, ↓reduceIte] using run1
    refine ⟨m1, connectedPrefix.trans (Star.one
      (floatNormalizeLoopL_large_skip_small hc pre1.code)), ag1, pre1,
      ?_, ?_, rd, rt, rf, rc⟩
    · simpa [guarded] using rq
    · simpa [guarded] using rr

#print axioms floatNormalizeLoopL_large_to_tail

/-- The actual large-path words denote the canonical integer transfer.
    This connects execution to reconstruction rather than assuming a body. -/
theorem floatNormalizeLoopL_large_canonical_output
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {fuel count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r)
    (room : base+8 < K) (large : 61 < distance) (active : q < target) :
    let c : Int := if r < (2 : Int)^(distance-1) then 0 else 1
    ∃ m', Star ⟨pc+48, fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16*(code.length-4)), fp⟩ m' ∧
      Agree fp base K m m' ∧ Pre L m' pc fp K base code ρ W reserved ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 base)) = some (BitVec.ofInt 64 (2*q+c)) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+1))) =
        some (BitVec.ofInt 64 (r-c*(2 : Int)^(distance-1))) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+2))) = some (BitVec.ofNat 64 (distance-1)) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+3))) = some (BitVec.ofInt 64 target) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+4))) = some (BitVec.ofNat 64 fuel) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+5))) = some (BitVec.ofNat 64 count) ∧
      (0 ≤ 2*q+c ∧ 2*q+c < 2^61) ∧
      (0 ≤ r-c*(2 : Int)^(distance-1) ∧ r-c*(2 : Int)^(distance-1) < 2^63 ∧
        r-c*(2 : Int)^(distance-1) < (2 : Int)^(distance-1)) ∧
      ((2*q+c)*(2 : Int)^(distance-1) + (r-c*(2 : Int)^(distance-1))) *
        (2 : Int)^originDistance = origin * (2 : Int)^(count+distance) := by
  dsimp only
  have dk : distance-1+1 = distance := by omega
  have transfer := floatNormalizeLoop_large_word_transfer q r target (distance-1)
    head.quotient.1 active head.targetBound.2 ⟨head.remainder.1, head.remainder.2.1⟩
    (by simpa only [dk] using head.remainder.2.2)
  dsimp only at transfer
  have carry : (if distance-1 < 63 then
      (1 : Runner.W) - Runner.IR.bool (decide (r < (2 : Int)^(distance-1))) else 0) =
      BitVec.ofInt 64 (if r < (2 : Int)^(distance-1) then 0 else 1) := by
    by_cases guarded : distance-1 < 63
    · by_cases below : r < (2 : Int)^(distance-1) <;>
        simp [guarded, below, Runner.IR.bool]
    · have below := floatNormalizeLoop_large_no_carry r (distance-1)
        head.remainder.2.1 (by omega)
      simp [guarded, below]
  obtain ⟨m', run, ag, pre, rq, rr, rd, rt, rf, rc⟩ :=
    floatNormalizeLoopL_large_to_tail hc head room large active
  rw [carry] at rq rr
  have qword : BitVec.ofInt 64 (2*q) = (BitVec.ofInt 64 q : Runner.W)*2 := by
    rw [show (2 : Runner.W) = BitVec.ofInt 64 2 from rfl, ← BitVec.ofInt_mul]
    congr 1
    ring
  rw [qword, transfer.1] at rq
  rw [transfer.2.1] at rr
  refine ⟨m', run, ag, pre, rq, rr, rd, rt, rf, rc,
    ⟨transfer.2.2.1, transfer.2.2.2.1⟩,
    ⟨transfer.2.2.2.2.2.1, transfer.2.2.2.2.2.2.2.1,
      transfer.2.2.2.2.2.2.1⟩, ?_⟩
  rw [transfer.2.2.2.2.1, dk]
  exact head.reconstruction

#print axioms floatNormalizeLoopL_large_canonical_output

set_option maxHeartbeats 800000 in
/-- Execute the common emitted counter/fuel tail and backedge. Only the
    temporary, count and fuel slots change; the transfer result is retained. -/
theorem floatNormalizeLoopL_shared_tail
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} (h : Pre L m pc fp K base code ρ W reserved)
    (room : base+6 < K) (fuel count : Runner.W)
    (rf : m.rd64 (slot fp (BitVec.ofNat 64 (base+4))) = some fuel)
    (rc : m.rd64 (slot fp (BitVec.ofNat 64 (base+5))) = some count) :
    ∃ m', Star ⟨pc + BitVec.ofNat 64 (16*(code.length-4)), fp⟩ m ⟨pc, fp⟩ m' ∧
      Agree fp base K m m' ∧ Pre L m' pc fp K base code ρ W reserved ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+4))) = some (fuel-1) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+5))) = some (count+1) ∧
      (∀ i, i < K → i ≠ base+4 → i ≠ base+5 → i ≠ base+6 →
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
  have shape1 : code.length ≥ 4 ∧ code.length-4 < code.length ∧
      code[code.length-4]? = some (ci 1 (base+6) 1 0) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have entry1 : code[code.length-4] = ci 1 (base+6) 1 0 := by
    simpa only [List.getElem?_eq_getElem shape1.2.1, Option.some.injEq] using shape1.2.2
  have ins1 := h.code (code.length-4) shape1.2.1
  rw [entry1] at ins1
  simp only [ci] at ins1
  let v1 : Runner.W := (1 : Runner.W)
  let m1 := write m (slot fp (BitVec.ofNat 64 (base+6))) 8 v1.toNat
  have ag1 : Agree fp base K m m1 :=
    agree_write h.frame.room (by omega) (by omega) v1.toNat
  have pre1 : Pre L m1 pc fp K base code ρ W reserved :=
    ⟨h.ctx, h.small, h.frame.agree ag1, h.code.agree ag1 h.far, h.far,
      envAt_agree h.env ag1 h.frame h.ctx (by omega),
      h.wstab m m1 h.welt (ag1.mono (by omega)), h.wstab⟩
  have read1 : m1.rd64 (slot fp (BitVec.ofNat 64 (base+6))) = some v1 := by
    simp only [m1, Runner.Mem.rd64, write_rd, h.frame.rd (base+6) (by omega),
      ↓reduceIte, le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have run1 : Run (step ⟨pc + BitVec.ofNat 64 (16*(code.length-4)), fp⟩) m
      ⟨pc + BitVec.ofNat 64 (16*(code.length-3)), fp⟩ m1 := by
    have run : Run (step ⟨pc + BitVec.ofNat 64 (16*(code.length-4)), fp⟩) m ⟨(pc + BitVec.ofNat 64 (16*(code.length-4)))+16, fp⟩ m1 := by
      refine run_step ins1 (by decide) ?_
      simp only [op]
      refine f2_run (t := ⟨pc + BitVec.ofNat 64 (16*(code.length-4)), fp⟩) ins1 ?_
      simp only [ret1]
      refine f1_run (t := ⟨pc + BitVec.ofNat 64 (16*(code.length-4)), fp⟩) ins1 ?_
      have sx6 : sx (II.f ((base : Int)+6)) = BitVec.ofNat 64 (base+6) := by
        exact_mod_cast sxslot (base+6) room
      rw [sx_lit (by decide : lit32 1 = true), sx6]
      exact run_wr64 (wr64_some (h.frame.wr (base+6) room))
    have advance : BitVec.ofNat 64 (16*(code.length-4)) + 16 =
        BitVec.ofNat 64 (16*(code.length-3)) := by
      change BitVec.ofNat 64 (16*(code.length-4)) + BitVec.ofNat 64 16 = _
      rw [← BitVec.ofNat_add]
      congr 1
      omega
    simpa only [nxt, BitVec.add_assoc, advance] using run
  have shape2 : code.length ≥ 4 ∧ code.length-3 < code.length ∧
      code[code.length-3]? = some (ci 3 (base+5) (base+5) (base+6)) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have entry2 : code[code.length-3] = ci 3 (base+5) (base+5) (base+6) := by
    simpa only [List.getElem?_eq_getElem shape2.2.1, Option.some.injEq] using shape2.2.2
  have ins2 := pre1.code (code.length-3) shape2.2.1
  rw [entry2] at ins2
  simp only [ci] at ins2
  let v2 : Runner.W := count+1
  let m2 := write m1 (slot fp (BitVec.ofNat 64 (base+5))) 8 v2.toNat
  have ag2 : Agree fp base K m1 m2 :=
    agree_write pre1.frame.room (by omega) (by omega) v2.toNat
  have pre2 : Pre L m2 pc fp K base code ρ W reserved :=
    ⟨pre1.ctx, pre1.small, pre1.frame.agree ag2, pre1.code.agree ag2 pre1.far, pre1.far,
      envAt_agree pre1.env ag2 pre1.frame pre1.ctx (by omega),
      pre1.wstab m1 m2 pre1.welt (ag2.mono (by omega)), pre1.wstab⟩
  have read2 : m2.rd64 (slot fp (BitVec.ofNat 64 (base+5))) = some v2 := by
    simp only [m2, Runner.Mem.rd64, write_rd, pre1.frame.rd (base+5) (by omega),
      ↓reduceIte, le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have run2 : Run (step ⟨pc + BitVec.ofNat 64 (16*(code.length-3)), fp⟩) m1
      ⟨pc + BitVec.ofNat 64 (16*(code.length-2)), fp⟩ m2 := by
    have sxa : sx (II.f ((base : Int)+5)) = BitVec.ofNat 64 (base+5) := by
      exact_mod_cast sxslot (base+5) (by omega)
    have sxb : sx (II.f ((base : Int)+6)) = BitVec.ofNat 64 (base+6) := by
      exact_mod_cast sxslot (base+6) (by omega)
    have sxd : sx (II.f ((base : Int)+5)) = BitVec.ofNat 64 (base+5) := by
      exact_mod_cast sxslot (base+5) (by omega)
    have ra : m1.rd64 (slot fp (BitVec.ofNat 64 (base+5))) = some count := by
      rw [show m1 = write m (slot fp (BitVec.ofNat 64 (base+6))) 8 v1.toNat from rfl,
        kept _ _ _ (by omega) (by omega) (by omega)]
      exact rc
    have rb : m1.rd64 (slot fp (BitVec.ofNat 64 (base+6))) = some (1 : Runner.W) := by
      exact read1
    have wr : m1.wr64 (slot fp (sx (II.f ((base : Int)+5)))) v2 = some m2 := by
      rw [sxd]; exact wr64_some (pre1.frame.wr (base+5) (by omega))
    have run := run_step (t := ⟨pc + BitVec.ofNat 64 (16*(code.length-3)), fp⟩) ins2 (by decide)
      (run_bin (g := fun a b => some (a+b)) ins2
        (by rw [sxa]; exact ra) (by rw [sxb]; exact rb) rfl wr)
    have advance : BitVec.ofNat 64 (16*(code.length-3)) + 16 =
        BitVec.ofNat 64 (16*(code.length-2)) := by
      change BitVec.ofNat 64 (16*(code.length-3)) + BitVec.ofNat 64 16 = _
      rw [← BitVec.ofNat_add]
      congr 1
      omega
    simpa only [nxt, BitVec.add_assoc, advance] using run
  have shape3 : code.length ≥ 4 ∧ code.length-2 < code.length ∧
      code[code.length-2]? = some (ci 4 (base+4) (base+4) (base+6)) := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
  have entry3 : code[code.length-2] = ci 4 (base+4) (base+4) (base+6) := by
    simpa only [List.getElem?_eq_getElem shape3.2.1, Option.some.injEq] using shape3.2.2
  have ins3 := pre2.code (code.length-2) shape3.2.1
  rw [entry3] at ins3
  simp only [ci] at ins3
  let v3 : Runner.W := fuel-1
  let m3 := write m2 (slot fp (BitVec.ofNat 64 (base+4))) 8 v3.toNat
  have ag3 : Agree fp base K m2 m3 :=
    agree_write pre2.frame.room (by omega) (by omega) v3.toNat
  have pre3 : Pre L m3 pc fp K base code ρ W reserved :=
    ⟨pre2.ctx, pre2.small, pre2.frame.agree ag3, pre2.code.agree ag3 pre2.far, pre2.far,
      envAt_agree pre2.env ag3 pre2.frame pre2.ctx (by omega),
      pre2.wstab m2 m3 pre2.welt (ag3.mono (by omega)), pre2.wstab⟩
  have read3 : m3.rd64 (slot fp (BitVec.ofNat 64 (base+4))) = some v3 := by
    simp only [m3, Runner.Mem.rd64, write_rd, pre2.frame.rd (base+4) (by omega),
      ↓reduceIte, le_write_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have run3 : Run (step ⟨pc + BitVec.ofNat 64 (16*(code.length-2)), fp⟩) m2
      ⟨pc + BitVec.ofNat 64 (16*(code.length-1)), fp⟩ m3 := by
    have sxa : sx (II.f ((base : Int)+4)) = BitVec.ofNat 64 (base+4) := by
      exact_mod_cast sxslot (base+4) (by omega)
    have sxb : sx (II.f ((base : Int)+6)) = BitVec.ofNat 64 (base+6) := by
      exact_mod_cast sxslot (base+6) (by omega)
    have sxd : sx (II.f ((base : Int)+4)) = BitVec.ofNat 64 (base+4) := by
      exact_mod_cast sxslot (base+4) (by omega)
    have ra : m2.rd64 (slot fp (BitVec.ofNat 64 (base+4))) = some fuel := by
      rw [show m2 = write m1 (slot fp (BitVec.ofNat 64 (base+5))) 8 v2.toNat from rfl,
        kept _ _ _ (by omega) (by omega) (by omega)]
      rw [show m1 = write m (slot fp (BitVec.ofNat 64 (base+6))) 8 v1.toNat from rfl,
        kept _ _ _ (by omega) (by omega) (by omega)]
      exact rf
    have rb : m2.rd64 (slot fp (BitVec.ofNat 64 (base+6))) = some (1 : Runner.W) := by
      rw [show m2 = write m1 (slot fp (BitVec.ofNat 64 (base+5))) 8 v2.toNat from rfl,
        kept _ _ _ (by omega) (by omega) (by omega)]
      exact read1
    have wr : m2.wr64 (slot fp (sx (II.f ((base : Int)+4)))) v3 = some m3 := by
      rw [sxd]; exact wr64_some (pre2.frame.wr (base+4) (by omega))
    have run := run_step (t := ⟨pc + BitVec.ofNat 64 (16*(code.length-2)), fp⟩) ins3 (by decide)
      (run_bin (g := fun a b => some (a-b)) ins3
        (by rw [sxa]; exact ra) (by rw [sxb]; exact rb) rfl wr)
    have advance : BitVec.ofNat 64 (16*(code.length-2)) + 16 =
        BitVec.ofNat 64 (16*(code.length-1)) := by
      change BitVec.ofNat 64 (16*(code.length-2)) + BitVec.ofNat 64 16 = _
      rw [← BitVec.ofNat_add]
      congr 1
      omega
    simpa only [nxt, BitVec.add_assoc, advance] using run
  refine ⟨m3, (Star.one run1).trans ((Star.one run2).trans
      ((Star.one run3).trans (Star.one (floatNormalizeLoopL_backedge hc pre3.code)))),
    ag1.trans (ag2.trans ag3), pre3, read3, ?_, ?_⟩
  · rw [show m3 = write m2 (slot fp (BitVec.ofNat 64 (base+4))) 8 v3.toNat from rfl,
      kept _ _ _ (by omega) (by omega) (by omega)]
    exact read2
  · intro i hi n4 n5 n6
    simp only [m3, m2, m1, kept _ _ i hi (by omega) n4,
      kept _ _ i hi (by omega) n5, kept _ _ i hi (by omega) n6]

#print axioms floatNormalizeLoopL_shared_tail

/-- A complete actual LARGE iteration returns to the canonical next head.
    The initial budget ceiling pays for the count increment. No execution
    or iteration premise is assumed. -/
theorem floatNormalizeLoopL_large_iteration
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {n count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m (n+1) count distance q r)
    (room : base+8 < K) (ceiling : budget < 2^63)
    (large : 61 < distance) (active : q < target) :
    let c : Int := if r < (2 : Int)^(distance-1) then 0 else 1
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc, fp⟩ m' ∧ Agree fp base K m m' ∧
      FloatNormalizeHead L ρ W pc fp K base reserved code origin
        originDistance budget target m' n (count+1) (distance-1)
        (2*q+c) (r-c*(2 : Int)^(distance-1)) := by
  dsimp only
  obtain ⟨m0, entry, ag0, h0⟩ :=
    floatNormalizeLoopL_active_entry hc head (by omega) (by omega) active
  obtain ⟨m1, body, ag1, pre1, rq, rr, rd, rt, rf, rc, qb, rb, reconstruct⟩ :=
    floatNormalizeLoopL_large_canonical_output hc h0 room large active
  obtain ⟨m2, tail, ag2, pre2, rf2, rc2, kept⟩ :=
    floatNormalizeLoopL_shared_tail hc pre1 (by omega) _ _ rf rc
  have resource := head.active_budget_bounds ceiling
  have fuelWord : (BitVec.ofNat 64 (n+1) : Runner.W)-1 = BitVec.ofNat 64 n := by
    rw [BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  have countWord : (BitVec.ofNat 64 count : Runner.W)+1 = BitVec.ofNat 64 (count+1) := by
    rw [BitVec.ofNat_add]
    rfl
  refine ⟨m2, entry.trans (body.trans tail), ag0.trans (ag1.trans ag2),
    { pre := pre2
      room := head.room
      fuelWord := resource.2.1
      countWord := resource.1
      distanceWord := by have := head.distanceWord; omega
      quotient := qb
      remainder := rb
      targetBound := head.targetBound
      readQ := ?_
      readR := ?_
      readDistance := ?_
      readTarget := ?_
      readFuel := by simpa only [fuelWord] using rf2
      readCount := by simpa only [countWord] using rc2
      conservedBudget := resource.2.2
      reconstruction := ?_ }⟩
  · rw [kept base (by omega) (by omega) (by omega) (by omega)]; exact rq
  · rw [kept (base+1) (by omega) (by omega) (by omega) (by omega)]; exact rr
  · rw [kept (base+2) (by omega) (by omega) (by omega) (by omega)]; exact rd
  · rw [kept (base+3) (by omega) (by omega) (by omega) (by omega)]; exact rt
  · simpa only [show count+1+(distance-1) = count+distance by omega] using reconstruct

#print axioms floatNormalizeLoopL_large_iteration

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

private abbrev normalizeWordTy : Ty := .int (-2^63) (2^63-1)

private theorem normalizeFrameEnv {m : Runner.Mem} {fp : Runner.W} {K n : Nat}
    (frame : FrameOK m fp K) (room : FB+n ≤ K) :
    ∃ ρ : Env D (List.replicate n normalizeWordTy), EnvAt L m fp ρ := by
  induction n with
  | zero => exact ⟨Env.nil, fun _ x => nomatch x⟩
  | succ n ih =>
    obtain ⟨ρ, env⟩ := ih (by omega)
    obtain ⟨w, read⟩ : ∃ w, m.rd64 (slot fp (BitVec.ofNat 64 (FB+n))) = some w := by
      simp only [Runner.Mem.rd64, frame.rd (FB+n) (by omega), ↓reduceIte]
      exact ⟨_, rfl⟩
    let z : Zahl (-2^63) (2^63-1) :=
      ⟨w.toInt, by simpa using BitVec.le_toInt w, by simpa using BitVec.toInt_le (x := w)⟩
    refine ⟨Env.cons z ρ, envAt_cons (w := w) env ?_ ?_⟩
    · simpa [frei] using read
    · exact BitVec.ofInt_toInt.symm

private theorem normalizeFrameVar (n i : Nat) (hi : i < n) :
    ∃ x : Var (List.replicate n normalizeWordTy) normalizeWordTy, vslot x = FB+i := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : i < n
    · obtain ⟨x, hx⟩ := ih h
      exact ⟨Var.there x, by simpa only [vslot_there] using hx⟩
    · exact ⟨Var.here, by simp [vslot_here, frei]; omega⟩

private theorem normalizeContextLoad {Δ : Ctx} (η : Env D Δ)
    (x : Var Δ normalizeWordTy) (i : Nat) (hx : vslot x = i) :
    WordCode (L := L) η (fun _ => True)
      (fun j => some ([ci 2 j i 0], j+1)) (BitVec.ofInt 64 (η.get x).n) := by
  intro fp K j c t hc ht m pc hp
  cases hc
  obtain ⟨w, hr, he⟩ := hp.env _ x
  rw [hx] at hr
  change w = BitVec.ofInt 64 (η.get x).n at he
  subst w
  have bound : i < j := by
    have := idx_lt x
    have := hp.ctx
    simp only [vslot, frei] at hx this
    omega
  exact mov_ok hp (by omega) (by omega) hr

#print axioms normalizeFrameEnv
#print axioms normalizeContextLoad

/-- Execute an adaptive arithmetic result from concrete retained frame inputs.
    The auxiliary environment is constructed from memory, never assumed. -/
theorem floatNormalizeStepL_slots
    {m : Runner.Mem} {entryPc : Runner.W} {out : Bool} {dst : Nat}
    {body : List II} {limit : Nat} (q r den target : Int)
    (hq : 0 ≤ q ∧ q < 2^62) (hd : 0 < den ∧ den < 2^62)
    (hr : 0 ≤ r ∧ r < den) (ht : 0 ≤ target ∧ target < 2^62)
    (hc : floatNormalizeStepL out dst
      (fun j => some ([ci 2 j base 0], j+1))
      (fun j => some ([ci 2 j (base+1) 0], j+1))
      (fun j => some ([ci 2 j (base+7) 0], j+1))
      (fun j => some ([ci 2 j (base+3) 0], j+1)) = some (body, limit))
    (hp : Pre L m entryPc fp K dst body ρ W reserved)
    (hb : FB ≤ base) (free : base+8 ≤ dst) (room : limit ≤ K)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 base)) = some (BitVec.ofInt 64 q))
    (rr : m.rd64 (slot fp (BitVec.ofNat 64 (base+1))) = some (BitVec.ofInt 64 r))
    (rd : m.rd64 (slot fp (BitVec.ofNat 64 (base+7))) = some (BitVec.ofInt 64 den))
    (rt : m.rd64 (slot fp (BitVec.ofNat 64 (base+3))) = some (BitVec.ofInt 64 target)) :
    Ok m entryPc fp K dst body (· = BitVec.ofInt 64
      (if out then (floatNormalizeStep q r den target).2
       else (floatNormalizeStep q r den target).1)) := by
  have dstBound : dst < limit := by
    unfold floatNormalizeStepL at hc
    cases out <;> simp [wordL] at hc <;>
      obtain ⟨rfl, rfl⟩ := hc <;> omega
  obtain ⟨η, env⟩ := normalizeFrameEnv (L := L) (n := base+8-FB) hp.frame (by omega)
  have producer (i : Nat) (hi : base ≤ i) (hi' : i < base+8)
      (v : Int) (hv : -2^63 ≤ v ∧ v < 2^63)
      (read : m.rd64 (slot fp (BitVec.ofNat 64 i)) = some (BitVec.ofInt 64 v)) :
      WordCode (L := L) η (fun _ => True)
        (fun j => some ([ci 2 j i 0], j+1)) (BitVec.ofInt 64 v) := by
    obtain ⟨x, hx⟩ := normalizeFrameVar (base+8-FB) (i-FB) (by omega)
    have hx' : vslot x = i := by omega
    obtain ⟨w, read', enc⟩ := env _ x
    rw [hx', read] at read'
    cases read'
    change BitVec.ofInt 64 v = BitVec.ofInt 64 (η.get x).n at enc
    have eq := congrArg BitVec.toInt enc
    rw [toInt_ofInt_in hv.1 hv.2,
      toInt_ofInt_in (η.get x).lo_le (by have := (η.get x).le_hi; omega)] at eq
    rw [eq]
    intro fp' K' j c t hc ht m' pc' hp'
    exact normalizeContextLoad (L := L) η x i hx' hc ht m' pc' hp'
  have pre : Pre L m entryPc fp K dst body η (fun _ => True) :=
    ⟨by simp [frei]; omega, hp.small, hp.frame, hp.code, hp.far,
      env, trivial, wstab_true _ _⟩
  exact floatNormalizeStepL_ok q r den target out hq hd hr ht
    (producer base (by omega) (by omega) q (by constructor <;> omega) rq)
    (producer (base+1) (by omega) (by omega) r (by constructor <;> omega) rr)
    (producer (base+7) (by omega) (by omega) den (by constructor <;> omega) rd)
    (producer (base+3) (by omega) (by omega) target (by constructor <;> omega) rt)
    hc room m entryPc pre

#print axioms floatNormalizeStepL_slots

set_option maxHeartbeats 1600000 in
/-- Run both real SMALL arithmetic expressions, retaining the six head slots.
    The output words are ready for the emitted copies, without assuming a body. -/
theorem floatNormalizeLoopL_small_calculation
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {fuel count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r)
    (ceiling : top ≤ K) (small : distance ≤ 61)
    (rd : m.rd64 (slot fp (BitVec.ofNat 64 (base+7))) =
      some (BitVec.ofInt 64 ((2 : Int)^distance))) :
    ∃ m', Star ⟨pc+384, fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16*(code.length-6)), fp⟩ m' ∧
      Agree fp (base+8) K m m' ∧
      FloatNormalizeHead L ρ W pc fp K base reserved code origin
        originDistance budget target m' fuel count distance q r ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+8))) =
        some (BitVec.ofInt 64 (floatNormalizeStep q r (2^distance) target).1) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+9))) =
        some (BitVec.ofInt 64 (floatNormalizeStep q r (2^distance) target).2) := by
  let load := fun (s j : Nat) => some ([ci 2 j s 0], j+1)
  obtain ⟨cq, eqQ⟩ : ∃ cq, floatNormalizeStepL false (base+8)
      (load base) (load (base+1)) (load (base+7)) (load (base+3)) = some cq := by
    simp [floatNormalizeStepL, load, wordL]
  obtain ⟨cr, eqR⟩ : ∃ cr, floatNormalizeStepL true (base+9)
      (load base) (load (base+1)) (load (base+7)) (load (base+3)) = some cr := by
    simp [floatNormalizeStepL, load, wordL]
  have shape : base+9 < top ∧ cq.2 ≤ top ∧ cr.2 ≤ top ∧
      24+cq.1.length+cr.1.length = code.length-6 ∧
      24+cq.1.length+cr.1.length ≤ code.length ∧
      (∀ i, i < cq.1.length → code[24+i]? = cq.1[i]?) ∧
      (∀ i, i < cr.1.length → code[24+cq.1.length+i]? = cr.1[i]?) := by
    simp [floatNormalizeStepL, load, wordL] at eqQ eqR
    obtain ⟨rfl, rfl⟩ := eqQ
    obtain ⟨rfl, rfl⟩ := eqR
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2]
    constructor <;> intro i hi <;> interval_cases i <;> norm_num
  have part (start : Nat) (body : List II)
      (bound : start+body.length ≤ code.length)
      (entries : ∀ i, i < body.length → code[start+i]? = body[i]?) :
      CodeAt m (pc + BitVec.ofNat 64 (16*start)) body := by
    intro i hi
    have ins := head.pre.code (start+i) (by omega)
    have eq := entries i hi
    simp only [List.getElem?_eq_getElem (by omega : start+i < code.length),
      List.getElem?_eq_getElem hi, Option.some.injEq] at eq
    rw [eq, ← pc_add] at ins
    exact ins
  have hb : FB ≤ base := by have := head.pre.ctx; unfold frei at this; omega
  have hd : 0 < (2 : Int)^distance ∧ (2 : Int)^distance < 2^62 := by
    exact ⟨Int.pow_pos (by decide), by
      exact_mod_cast (Nat.pow_lt_pow_right (by decide : 1 < 2) (show distance < 62 by omega))⟩
  have preQ : Pre L m (pc+384) fp K (base+8) cq.1 ρ W reserved :=
    ⟨by have := head.pre.ctx; omega, head.pre.small, head.pre.frame,
      by simpa using part 24 cq.1 (by omega) shape.2.2.2.2.2.1,
      by simpa using codeFar_at head.pre.far (i := 24) (k := cq.1.length) (by omega),
      head.pre.env, head.pre.welt, head.pre.wstab⟩
  obtain ⟨m1, runQ, agQ, wq, rq, valQ⟩ := floatNormalizeStepL_slots q r (2^distance) target
    (by have := head.quotient; constructor <;> omega) hd
    ⟨head.remainder.1, head.remainder.2.2⟩
    (by have := head.targetBound; constructor <;> omega)
    eqQ preQ hb (by omega) (by omega) head.readQ head.readR rd head.readTarget
  subst wq
  have pre1 : Pre L m1 pc fp K base code ρ W reserved :=
    ⟨head.pre.ctx, head.pre.small, head.pre.frame.agree agQ,
      head.pre.code.agree agQ head.pre.far, head.pre.far,
      envAt_agree head.pre.env agQ head.pre.frame (by have := head.pre.ctx; omega) (by omega),
      head.pre.wstab m m1 head.pre.welt (agQ.mono (by omega)), head.pre.wstab⟩
  have keepQ (i : Nat) (hi : i < base+8) := agree_rd_low agQ head.pre.frame.room hi (by omega)
  have codeR := (part (24+cq.1.length) cr.1 shape.2.2.2.2.1 shape.2.2.2.2.2.2).agree agQ
    (codeFar_at head.pre.far shape.2.2.2.2.1)
  have preR : Pre L m1 (pc+BitVec.ofNat 64 (16*(24+cq.1.length))) fp K (base+9) cr.1 ρ W reserved :=
    ⟨by have := head.pre.ctx; omega, pre1.small, pre1.frame, codeR,
      codeFar_at head.pre.far shape.2.2.2.2.1, pre1.env, pre1.welt, pre1.wstab⟩
  obtain ⟨m2, runR, agR, wr, rr, valR⟩ := floatNormalizeStepL_slots q r (2^distance) target
    (by have := head.quotient; constructor <;> omega) hd
    ⟨head.remainder.1, head.remainder.2.2⟩
    (by have := head.targetBound; constructor <;> omega)
    eqR preR hb (by omega) (by omega)
    (by rw [keepQ base (by omega)]; exact head.readQ)
    (by rw [keepQ (base+1) (by omega)]; exact head.readR)
    (by rw [keepQ (base+7) (by omega)]; exact rd)
    (by rw [keepQ (base+3) (by omega)]; exact head.readTarget)
  subst wr
  have ag := agQ.trans (agR.mono (by omega))
  have pre2 : Pre L m2 pc fp K base code ρ W reserved :=
    ⟨pre1.ctx, pre1.small, pre1.frame.agree agR, pre1.code.agree agR pre1.far, pre1.far,
      envAt_agree pre1.env agR pre1.frame (by have := pre1.ctx; omega) (by omega),
      pre1.wstab m1 m2 pre1.welt (agR.mono (by omega)), pre1.wstab⟩
  have keep (i : Nat) (hi : i < base+8) := agree_rd_low ag head.pre.frame.room hi (by omega)
  refine ⟨m2, ?_, ag, ?_, ?_, rr⟩
  · have qpc : pc+384+BitVec.ofNat 64 (16*cq.1.length) =
        pc+BitVec.ofNat 64 (16*(24+cq.1.length)) := by simpa using pc_add pc 24 cq.1.length
    rw [qpc] at runQ
    have endpc := pc_add pc (24+cq.1.length) cr.1.length
    rw [shape.2.2.2.1] at endpc
    rw [endpc] at runR
    exact runQ.trans runR
  · exact { head with pre := pre2
                      readQ := by rw [keep base (by omega)]; exact head.readQ
                      readR := by rw [keep (base+1) (by omega)]; exact head.readR
                      readDistance := by rw [keep (base+2) (by omega)]; exact head.readDistance
                      readTarget := by rw [keep (base+3) (by omega)]; exact head.readTarget
                      readFuel := by rw [keep (base+4) (by omega)]; exact head.readFuel
                      readCount := by rw [keep (base+5) (by omega)]; exact head.readCount }
  · rw [agree_rd_low agR pre1.frame.room (by omega : base+8 < base+9) (by omega)]
    exact rq

#print axioms floatNormalizeLoopL_small_calculation

/-- Complete the SMALL branch through arithmetic, copies and the real backedge. -/
theorem floatNormalizeLoopL_small_iteration
    (hc : floatNormalizeLoopL base = some (code, top))
    {m : Runner.Mem} {n count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m (n+1) count distance q r)
    (room : top ≤ K) (ceiling : budget < 2^63)
    (small : distance ≤ 61) (active : q < target) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc, fp⟩ m' ∧ Agree fp base K m m' ∧
      FloatNormalizeHead L ρ W pc fp K base reserved code origin
        originDistance budget target m' n (count+1) distance
        (floatNormalizeStep q r (2^distance) target).1
        (floatNormalizeStep q r (2^distance) target).2 := by
  have slots : base+9 < K := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2] at room
    omega
  obtain ⟨m0, entry, ag0, h0⟩ :=
    floatNormalizeLoopL_active_entry hc head (by omega) (by omega) active
  obtain ⟨m1, dispatch, ag1, h1, den⟩ :=
    floatNormalizeLoopL_small_dispatch hc h0 (by omega) small
  obtain ⟨m2, arithmetic, ag2, h2, rq, rr⟩ :=
    floatNormalizeLoopL_small_calculation hc h1 room small den
  obtain ⟨m3, copies, ag3, pre3, rq3, rr3, kept3⟩ :=
    floatNormalizeLoopL_small_copies hc h2.pre slots _ _ rq rr
  obtain ⟨m4, tail, ag4, pre4, rf4, rc4, kept4⟩ :=
    floatNormalizeLoopL_shared_tail hc pre3 (by omega) _ _
      (by rw [kept3 (base+4) (by omega) (by omega) (by omega)]; exact h2.readFuel)
      (by rw [kept3 (base+5) (by omega) (by omega) (by omega)]; exact h2.readCount)
  have resource := head.active_budget_bounds ceiling
  have bounds := floatNormalizeStep_bounds q r (2^distance) target head.quotient.1
    (Int.pow_pos (by decide)) ⟨head.remainder.1, head.remainder.2.2⟩
  have qb : (floatNormalizeStep q r (2^distance) target).1 < 2^61 := by
    have := head.targetBound
    unfold floatNormalizeStep floatNormalizeActive floatNormalizeCarry
    simp only [active, ↓reduceIte]
    split <;> simp_all <;> omega
  have denBound : (2 : Int)^distance < 2^63 := by
    exact_mod_cast (Nat.pow_lt_pow_right (by decide : 1 < 2) (show distance < 63 by omega))
  refine ⟨m4, entry.trans (dispatch.trans (arithmetic.trans (copies.trans tail))),
    ag0.trans (ag1.trans ((ag2.mono (by omega)).trans (ag3.trans ag4))),
    { pre := pre4
      room := head.room
      fuelWord := resource.2.1
      countWord := resource.1
      distanceWord := head.distanceWord
      quotient := ⟨bounds.1, qb⟩
      remainder := ⟨bounds.2.1, by omega, bounds.2.2⟩
      targetBound := head.targetBound
      readQ := ?_
      readR := ?_
      readDistance := ?_
      readTarget := ?_
      readFuel := ?_
      readCount := ?_
      conservedBudget := resource.2.2
      reconstruction := ?_ }⟩
  · rw [kept4 base (by omega) (by omega) (by omega) (by omega)]; exact rq3
  · rw [kept4 (base+1) (by omega) (by omega) (by omega) (by omega)]; exact rr3
  · rw [kept4 (base+2) (by omega) (by omega) (by omega) (by omega),
      kept3 (base+2) (by omega) (by omega) (by omega)]; exact h2.readDistance
  · rw [kept4 (base+3) (by omega) (by omega) (by omega) (by omega),
      kept3 (base+3) (by omega) (by omega) (by omega)]; exact h2.readTarget
  · have eq : (BitVec.ofNat 64 (n+1) : Runner.W)-1 = BitVec.ofNat 64 n := by
      rw [BitVec.ofNat_add]
      exact BitVec.add_sub_cancel _ _
    simpa only [eq] using rf4
  · have eq : (BitVec.ofNat 64 count : Runner.W)+1 = BitVec.ofNat 64 (count+1) := by
      rw [BitVec.ofNat_add]
      rfl
    simpa only [eq] using rc4
  · have exactness := floatNormalizeStep_exact q r (2^distance) target
    simp only [floatNormalizeActive, active, ↓reduceIte] at exactness
    rw [exactness, show count+1+distance = (count+distance)+1 by omega, pow_succ]
    calc
      (q * 2^distance+r)*2*2^originDistance =
          ((q * 2^distance+r)*2^originDistance)*2 := by ring
      _ = _ := by rw [head.reconstruction]; ring

#print axioms floatNormalizeLoopL_small_iteration

/-- Central induction, with the complete active iteration still explicit.
    The target exit is discharged by actual emitted execution above.
    The iteration premise is not an implementation of the missing proof.
    In particular a word-arithmetic lemma alone cannot discharge `iteration`:
    it must supply actual Runner execution and re-establish the entire head.
    This theorem is not sufficient to enable the lowering hook. -/
theorem floatNormalizeLoopL_induction
    (hc : floatNormalizeLoopL base = some (code, top))
    (room : base+6 < K)
    (iteration : ∀ m n count distance q r,
      FloatNormalizeHead L ρ W pc fp K base reserved code origin
        originDistance budget target m (n+1) count distance q r → q < target →
      ∃ m' distance' q' r', Star ⟨pc, fp⟩ m ⟨pc, fp⟩ m' ∧
        Agree fp base K m m' ∧
        FloatNormalizeHead L ρ W pc fp K base reserved code origin
          originDistance budget target m' n (count+1) distance' q' r')
    {m : Runner.Mem} {fuel count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r) :
    ∃ m' fuel' count' distance' q' r',
      Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16*code.length), fp⟩ m' ∧
      Agree fp base K m m' ∧
      FloatNormalizeHead L ρ W pc fp K base reserved code origin
        originDistance budget target m' fuel' count' distance' q' r' ∧
      (fuel' = 0 ∨ target ≤ q') ∧ count ≤ count' ∧ count' ≤ budget := by
  induction fuel generalizing m count distance q r with
  | zero =>
    have hz := floatNormalizeLoopL_zero hc head.pre (by have := head.room; omega)
      (by simpa using head.readFuel)
    exact ⟨m, 0, count, distance, q, r, hz.1, hz.2, head,
      Or.inl rfl, Nat.le_refl _, by have := head.conservedBudget; omega⟩
  | succ n ih =>
    by_cases active : q < target
    · obtain ⟨next, d, a, b, run, agree, nextHead⟩ :=
        iteration m n count distance q r head active
      obtain ⟨last, f, c, d', a', b', rest, kept, finalHead, stop, lower, upper⟩ :=
        ih nextHead
      exact ⟨last, f, c, d', a', b', run.trans rest, agree.trans kept,
        finalHead, stop, by omega, upper⟩
    · have stopped : target ≤ q := by omega
      obtain ⟨last, run, agree, finalHead⟩ :=
        floatNormalizeLoopL_target_exit hc head room (by omega) stopped
      exact ⟨last, n+1, count, distance, q, r, run, agree, finalHead,
        Or.inr stopped, Nat.le_refl _, by have := head.conservedBudget; omega⟩

#print axioms floatNormalizeLoopL_induction

/-- The actual generic iteration chooses the emitted LARGE or SMALL path. -/
theorem floatNormalizeLoopL_iteration
    (hc : floatNormalizeLoopL base = some (code, top)) (room : top ≤ K)
    (ceiling : budget < 2^63)
    {m : Runner.Mem} {n count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m (n+1) count distance q r) (active : q < target) :
    ∃ m' distance' q' r', Star ⟨pc, fp⟩ m ⟨pc, fp⟩ m' ∧ Agree fp base K m m' ∧
      FloatNormalizeHead L ρ W pc fp K base reserved code origin
        originDistance budget target m' n (count+1) distance' q' r' := by
  by_cases large : 61 < distance
  · have slots : base+8 < K := by
      unfold floatNormalizeLoopL at hc
      simp [floatNormalizeStepL, wordL] at hc
      obtain ⟨rfl, rfl⟩ := hc
      norm_num [bin2] at room
      omega
    obtain ⟨m', run, agree, next⟩ :=
      floatNormalizeLoopL_large_iteration hc head slots ceiling large active
    exact ⟨m', _, _, _, run, agree, next⟩
  · obtain ⟨m', run, agree, next⟩ :=
      floatNormalizeLoopL_small_iteration hc head room ceiling (by omega) active
    exact ⟨m', _, _, _, run, agree, next⟩

/-- The complete emitted loop returns the Euclidean quotient and exact remainder
    of the original magnitude at the final scale. The common power-of-two
    factor is mathematical only: even very large distances require no wide
    machine denominator. This connects actual execution to canonical rounding
    without assuming the values of either output slot. -/
theorem floatNormalizeLoopL_complete
    (hc : floatNormalizeLoopL base = some (code, top)) (room : top ≤ K)
    {m : Runner.Mem} {fuel distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel 0 distance q r) :
    ∃ m' fuel' count' distance' q' r',
      Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16*code.length), fp⟩ m' ∧
      Agree fp base K m m' ∧
      FloatNormalizeHead L ρ W pc fp K base reserved code origin
        originDistance budget target m' fuel' count' distance' q' r' ∧
      (fuel' = 0 ∨ target ≤ q') ∧ count' ≤ budget ∧
      (origin * 2^(count'+distance')) / (2^(distance'+originDistance) : Int) = q' ∧
      (origin * 2^(count'+distance')) % (2^(distance'+originDistance) : Int) =
        r' * 2^originDistance := by
  have slots : base+6 < K := by
    unfold floatNormalizeLoopL at hc
    simp [floatNormalizeStepL, wordL] at hc
    obtain ⟨rfl, rfl⟩ := hc
    norm_num [bin2] at room
    omega
  obtain ⟨m', f, c, d, a, b, run, agree, finalHead, stop, _, bound⟩ :=
    floatNormalizeLoopL_induction hc slots
      (fun _ _ _ _ _ _ h a => floatNormalizeLoopL_iteration hc room
        head.initial_budget_bound h a) head
  refine ⟨m', f, c, d, a, b, run, agree, finalHead, stop, bound, ?_⟩
  have positive : (0 : Int) < 2^originDistance := Int.pow_pos (by decide)
  apply (Int.ediv_emod_unique (Int.pow_pos (by decide))).mpr
  refine ⟨?_, Int.mul_nonneg finalHead.remainder.1 (by omega), ?_⟩
  · calc
      b * 2^originDistance + 2^(d+originDistance) * a =
          (a * 2^d + b) * 2^originDistance := by rw [pow_add]; ring
      _ = origin * 2^(c+d) := finalHead.reconstruction
  · rw [pow_add]
    exact Int.mul_lt_mul_of_pos_right finalHead.remainder.2.2 positive


/-- Construct the actual loop invariant from a nonnegative word-sized numerator.
    The six reads describe the entry memory; no reconstruction, canonical-tail
    or internal loop-correctness premise is required. The budget reserves one
    transfer per denominator bit and 64 further transfers. -/
theorem FloatNormalizeHead.of_numerator
    {m : Runner.Mem} (n : Int) (d : Nat)
    (hn : 0 ≤ n ∧ n < 2^61) (hd : d + 64 < 2^63)
    (ht : 0 ≤ target ∧ target ≤ 2^60)
    (pre : Pre L m pc fp K base code ρ W reserved) (slots : base+5 < K)
    (readQ : m.rd64 (slot fp (BitVec.ofNat 64 base)) = some (BitVec.ofInt 64 (n / 2^d)))
    (readR : m.rd64 (slot fp (BitVec.ofNat 64 (base+1))) = some (BitVec.ofInt 64 (n % 2^d)))
    (readD : m.rd64 (slot fp (BitVec.ofNat 64 (base+2))) = some (BitVec.ofNat 64 d))
    (readT : m.rd64 (slot fp (BitVec.ofNat 64 (base+3))) = some (BitVec.ofInt 64 target))
    (readF : m.rd64 (slot fp (BitVec.ofNat 64 (base+4))) = some (BitVec.ofNat 64 (d+64)))
    (readC : m.rd64 (slot fp (BitVec.ofNat 64 (base+5))) = some 0) :
    FloatNormalizeHead L ρ W pc fp K base reserved code n d (d+64) target
      m (d+64) 0 d (n / 2^d) (n % 2^d) := by
  have pos : (0 : Int) < 2^d := Int.pow_pos (by decide)
  have qpos := Int.ediv_nonneg hn.1 (by omega : (0 : Int) ≤ 2^d)
  have qle := Int.ediv_le_self (2^d) hn.1
  have rpos := Int.emod_nonneg n (by omega : (2 : Int)^d ≠ 0)
  have rlt := Int.emod_lt_of_pos n pos
  have split := Int.ediv_mul_add_emod n ((2 : Int)^d)
  have prod := Int.mul_nonneg qpos (by omega : (0 : Int) ≤ 2^d)
  refine ⟨pre, slots, hd, by decide, by omega, ⟨qpos, by omega⟩,
    ⟨rpos, by omega, rlt⟩, ht, readQ, readR, readD, readT, readF, readC,
    by omega, ?_⟩
  simp only [Nat.zero_add]
  rw [split]

/-- Execute the whole emitted loop from canonical entry reads derived from a
    numerator, rather than accepting an internal invariant as an assumption. -/
theorem floatNormalizeLoopL_from_numerator
    (hc : floatNormalizeLoopL base = some (code, top)) (room : top ≤ K)
    {m : Runner.Mem} (n : Int) (d : Nat)
    (hn : 0 ≤ n ∧ n < 2^61) (hd : d + 64 < 2^63)
    (ht : 0 ≤ target ∧ target ≤ 2^60)
    (pre : Pre L m pc fp K base code ρ W reserved) (slots : base+5 < K)
    (readQ : m.rd64 (slot fp (BitVec.ofNat 64 base)) = some (BitVec.ofInt 64 (n / 2^d)))
    (readR : m.rd64 (slot fp (BitVec.ofNat 64 (base+1))) = some (BitVec.ofInt 64 (n % 2^d)))
    (readD : m.rd64 (slot fp (BitVec.ofNat 64 (base+2))) = some (BitVec.ofNat 64 d))
    (readT : m.rd64 (slot fp (BitVec.ofNat 64 (base+3))) = some (BitVec.ofInt 64 target))
    (readF : m.rd64 (slot fp (BitVec.ofNat 64 (base+4))) = some (BitVec.ofNat 64 (d+64)))
    (readC : m.rd64 (slot fp (BitVec.ofNat 64 (base+5))) = some 0) :
    ∃ m' fuel' count' distance' q' r',
      Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16*code.length), fp⟩ m' ∧
      Agree fp base K m m' ∧
      FloatNormalizeHead L ρ W pc fp K base reserved code n d (d+64) target
        m' fuel' count' distance' q' r' ∧
      (fuel' = 0 ∨ target ≤ q') ∧ count' ≤ d+64 ∧
      (n * 2^(count'+distance')) / (2^(distance'+d) : Int) = q' ∧
      (n * 2^(count'+distance')) % (2^(distance'+d) : Int) = r' * 2^d := by
  exact floatNormalizeLoopL_complete hc room
    (FloatNormalizeHead.of_numerator n d hn hd ht pre slots
      readQ readR readD readT readF readC)

#print axioms FloatNormalizeHead.of_numerator
#print axioms floatNormalizeLoopL_from_numerator

#print axioms floatNormalizeLoopL_complete

end
end Gabbro.Stage0.Senke
