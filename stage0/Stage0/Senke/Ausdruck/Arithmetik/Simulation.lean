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
