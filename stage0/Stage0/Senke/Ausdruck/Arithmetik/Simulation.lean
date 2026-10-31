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

/-- Central induction, with the two remaining emitted-code obligations explicit:
    target exit and a complete active iteration returning to the same PC.
    Neither obligation is an axiom or an implementation of the missing proof.
    In particular a word-arithmetic lemma alone cannot discharge `iteration`:
    it must supply actual Runner execution and re-establish the entire head.
    This theorem is not sufficient to enable the lowering hook. -/
theorem floatNormalizeLoopL_induction
    (hc : floatNormalizeLoopL base = some (code, top))
    (targetExit : ∀ m fuel count distance q r,
      FloatNormalizeHead L ρ W pc fp K base reserved code origin
        originDistance budget target m fuel count distance q r →
      0 < fuel → target ≤ q →
      ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16*code.length), fp⟩ m' ∧
        Agree fp base K m m' ∧
        FloatNormalizeHead L ρ W pc fp K base reserved code origin
          originDistance budget target m' fuel count distance q r)
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
        targetExit m (n+1) count distance q r head (by omega) stopped
      exact ⟨last, n+1, count, distance, q, r, run, agree, finalHead,
        Or.inr stopped, Nat.le_refl _, by have := head.conservedBudget; omega⟩

#print axioms floatNormalizeLoopL_induction
end
end Gabbro.Stage0.Senke
