/- Whole-loop induction for the emitted normalization block. -/
import Stage0.Senke.Ausdruck.Arithmetik.Schleife

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
end
end Gabbro.Stage0.Senke
