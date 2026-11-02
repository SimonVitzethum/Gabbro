module
public import Stage0.Senke.Ausdruck.Arithmetik.Simulation.Teil7a

public import Stage0.Senke.Ausdruck.Arithmetik.Schleife
public import Stage0.Senke.Ausdruck.Quant.Frame
public import Stage0.Senke.Anweisung.SchleifeTeile
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Stage0.Senke.Ausdruck.Arithmetik.Simulation.Teil6

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
section
variable [Kern] {D : Deklaration} {L : Lay D} {Γ : Ctx}
    {ρ : Env D Γ} {W : Runner.Mem → Prop} {pc fp : Runner.W}
    {K base top reserved : Nat} {code : List II} {origin target : Int}
    {originDistance budget : Nat}

/-- Construct the actual loop invariant from a nonnegative word-sized numerator.
    The six reads describe the entry memory; no reconstruction, canonical-tail
    or internal loop-correctness premise is required. The caller chooses the fuel; sufficient precision budgets are proved separately. -/
theorem FloatNormalizeHead.of_numerator
    {m : Runner.Mem} (n : Int) (d fuel : Nat)
    (hn : 0 ≤ n ∧ n < 2^61) (hd : d < 2^63) (hf : fuel < 2^63)
    (ht : 0 ≤ target ∧ target ≤ 2^60)
    (pre : Pre L m pc fp K base code ρ W reserved) (slots : base+5 < K)
    (readQ : m.rd64 (slot fp (BitVec.ofNat 64 base)) = some (BitVec.ofInt 64 (n / 2^d)))
    (readR : m.rd64 (slot fp (BitVec.ofNat 64 (base+1))) = some (BitVec.ofInt 64 (n % 2^d)))
    (readD : m.rd64 (slot fp (BitVec.ofNat 64 (base+2))) = some (BitVec.ofNat 64 d))
    (readT : m.rd64 (slot fp (BitVec.ofNat 64 (base+3))) = some (BitVec.ofInt 64 target))
    (readF : m.rd64 (slot fp (BitVec.ofNat 64 (base+4))) = some (BitVec.ofNat 64 fuel))
    (readC : m.rd64 (slot fp (BitVec.ofNat 64 (base+5))) = some 0) :
    FloatNormalizeHead L ρ W pc fp K base reserved code n d fuel target
      m fuel 0 d (n / 2^d) (n % 2^d) := by
  have pos : (0 : Int) < 2^d := Int.pow_pos (by decide)
  have qpos := Int.ediv_nonneg hn.1 (by omega : (0 : Int) ≤ 2^d)
  have qle := Int.ediv_le_self (2^d) hn.1
  have rpos := Int.emod_nonneg n (by omega : (2 : Int)^d ≠ 0)
  have rlt := Int.emod_lt_of_pos n pos
  have split := Int.ediv_mul_add_emod n ((2 : Int)^d)
  have prod := Int.mul_nonneg qpos (by omega : (0 : Int) ≤ 2^d)
  refine ⟨pre, slots, hf, by decide, by omega, ⟨qpos, by omega⟩,
    ⟨rpos, by omega, rlt⟩, ht, readQ, readR, readD, readT, readF, readC,
    by omega, ?_⟩
  simp only [Nat.zero_add]
  rw [split]

/-- Execute the whole emitted loop from canonical entry reads derived from a
    numerator, rather than accepting an internal invariant as an assumption. -/
theorem floatNormalizeLoopL_from_numerator
    (hc : floatNormalizeLoopL base = some (code, top)) (room : top ≤ K)
    {m : Runner.Mem} (n : Int) (d fuel : Nat)
    (hn : 0 ≤ n ∧ n < 2^61) (hd : d < 2^63) (hf : fuel < 2^63)
    (ht : 0 ≤ target ∧ target ≤ 2^60)
    (pre : Pre L m pc fp K base code ρ W reserved) (slots : base+5 < K)
    (readQ : m.rd64 (slot fp (BitVec.ofNat 64 base)) = some (BitVec.ofInt 64 (n / 2^d)))
    (readR : m.rd64 (slot fp (BitVec.ofNat 64 (base+1))) = some (BitVec.ofInt 64 (n % 2^d)))
    (readD : m.rd64 (slot fp (BitVec.ofNat 64 (base+2))) = some (BitVec.ofNat 64 d))
    (readT : m.rd64 (slot fp (BitVec.ofNat 64 (base+3))) = some (BitVec.ofInt 64 target))
    (readF : m.rd64 (slot fp (BitVec.ofNat 64 (base+4))) = some (BitVec.ofNat 64 fuel))
    (readC : m.rd64 (slot fp (BitVec.ofNat 64 (base+5))) = some 0) :
    ∃ m' fuel' count' distance' q' r',
      Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16*code.length), fp⟩ m' ∧
      Agree fp base K m m' ∧
      FloatNormalizeHead L ρ W pc fp K base reserved code n d fuel target
        m' fuel' count' distance' q' r' ∧
      (fuel' = 0 ∨ target ≤ q') ∧ count' ≤ fuel ∧
      (n * 2^(count'+distance')) / (2^(distance'+d) : Int) = q' ∧
      (n * 2^(count'+distance')) % (2^(distance'+d) : Int) = r' * 2^d := by
  exact floatNormalizeLoopL_complete hc room
    (FloatNormalizeHead.of_numerator n d fuel hn hd hf ht pre slots
      readQ readR readD readT readF readC)

/-- With a positive aligned numerator and enough fuel for the format precision,
    actual execution reaches the target; fuel exhaustion is no longer an
    alternative conclusion. Entry reads still need an executed producer. -/
theorem floatNormalizeLoopL_reaches_target
    (hc : floatNormalizeLoopL base = some (code, top)) (room : top ≤ K)
    {m : Runner.Mem} {fuel distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel 0 distance q r)
    (precision : Nat) (targetFits : target ≤ 2^precision)
    (positive : 0 < origin) (sufficient : originDistance + precision ≤ budget) :
    ∃ m' fuel' count' distance' q' r',
      Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16*code.length), fp⟩ m' ∧
      Agree fp base K m m' ∧
      FloatNormalizeHead L ρ W pc fp K base reserved code origin
        originDistance budget target m' fuel' count' distance' q' r' ∧
      target ≤ q' ∧ count' ≤ budget ∧
      (origin * 2^(count'+distance')) / (2^(distance'+originDistance) : Int) = q' ∧
      (origin * 2^(count'+distance')) % (2^(distance'+originDistance) : Int) =
        r' * 2^originDistance := by
  obtain ⟨m', f, c, d, a, b, run, agree, finalHead, stop, bound, exactQ, exactR⟩ :=
    floatNormalizeLoopL_complete hc room head
  refine ⟨m', f, c, d, a, b, run, agree, finalHead, ?_, bound, exactQ, exactR⟩
  by_contra active
  have small := finalHead.active_count_bound precision targetFits positive (by omega)
  have exhausted : f = 0 := stop.resolve_right (by omega)
  have := finalHead.conservedBudget
  omega

#print axioms floatNormalizeLoopL_reaches_target

#print axioms FloatNormalizeHead.of_numerator
#print axioms floatNormalizeLoopL_from_numerator

#print axioms floatNormalizeLoopL_complete

/-- Zero is a genuine canonical loop input. Exact reconstruction forces both
    output words to remain zero at every reachable head, even when the target
    is positive and the loop consumes its entire fuel. -/
theorem FloatNormalizeHead.zero_words
    {m : Runner.Mem} {fuel count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code 0
      originDistance budget target m fuel count distance q r) :
    q = 0 ∧ r = 0 := by
  have po : (0 : Int) < 2^originDistance := Int.pow_pos (by decide)
  have pd : (0 : Int) < 2^distance := Int.pow_pos (by decide)
  have reconstruction := head.reconstruction
  simp only [Int.zero_mul] at reconstruction
  have hq := head.quotient.1
  have hr := head.remainder.1
  have product := mul_nonneg hq (le_of_lt pd)
  have sum : q * 2^distance + r = 0 := by nlinarith
  constructor <;> nlinarith

/-- A sufficient precision budget gives a total finite-magnitude conclusion:
    either exact cancellation returns two zero words, or the positive
    magnitude reaches the target. No positive-input assumption hides zero. -/
theorem floatNormalizeLoopL_finite_magnitude
    (hc : floatNormalizeLoopL base = some (code, top)) (room : top ≤ K)
    {m : Runner.Mem} {fuel distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel 0 distance q r)
    (nonnegative : 0 ≤ origin)
    (precision : Nat) (targetFits : target ≤ 2^precision)
    (sufficient : originDistance + precision ≤ budget) :
    ∃ m' fuel' count' distance' q' r',
      Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16*code.length), fp⟩ m' ∧
      Agree fp base K m m' ∧
      FloatNormalizeHead L ρ W pc fp K base reserved code origin
        originDistance budget target m' fuel' count' distance' q' r' ∧
      ((origin = 0 ∧ q' = 0 ∧ r' = 0) ∨ (0 < origin ∧ target ≤ q')) ∧
      count' ≤ budget ∧
      (origin * 2^(count'+distance')) / (2^(distance'+originDistance) : Int) = q' ∧
      (origin * 2^(count'+distance')) % (2^(distance'+originDistance) : Int) =
        r' * 2^originDistance := by
  obtain ⟨m', f, c, d, a, b, run, agree, finalHead, stop, bound, exactQ, exactR⟩ :=
    floatNormalizeLoopL_complete hc room head
  refine ⟨m', f, c, d, a, b, run, agree, finalHead, ?_, bound, exactQ, exactR⟩
  by_cases zero : origin = 0
  · subst origin
    exact Or.inl ⟨rfl, finalHead.zero_words⟩
  · have positive : 0 < origin := by omega
    refine Or.inr ⟨positive, ?_⟩
    by_contra active
    have small := finalHead.active_count_bound precision targetFits positive (by omega)
    have exhausted : f = 0 := stop.resolve_right (by omega)
    have := finalHead.conservedBudget
    omega

#print axioms FloatNormalizeHead.zero_words
#print axioms floatNormalizeLoopL_finite_magnitude

/-- Canonical scaling of the guard-scaled magnitude reconstructed by the
    executed loop: the represented rational is origin / (8 * 2^originDistance).
    The common distance factor retains that exact rational value; the
    three guard bits belong in its denominator. No canonical quotient or
    remainder is assumed. This is the arithmetic bridge, before choosing the
    source exponent and its normal/subnormal output branch. -/
theorem FloatNormalizeHead.normQD_output
    {m : Runner.Mem} {fuel count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r) (p : Nat) :
    let nd := Gleitkomma.normQD p ((p : Int)-1-count)
      (origin.toNat * 2^distance) (8 * 2^(distance+originDistance))
    nd.1 / nd.2 = (q/8).toNat ∧
    nd.1 % nd.2 = (q%8).toNat * 2^(distance+originDistance) +
      r.toNat * 2^originDistance ∧
    nd.2 = 8 * 2^(distance+originDistance) := by
  have pd : (0 : Int) < 2^distance := Int.pow_pos (by decide)
  have po : (0 : Int) < 2^originDistance := Int.pow_pos (by decide)
  have pc : (0 : Int) < 2^(count+distance) := Int.pow_pos (by decide)
  have reconstruction := head.reconstruction
  have nonnegative : 0 ≤ origin := by
    have h := mul_nonneg
      (add_nonneg (mul_nonneg head.quotient.1 (le_of_lt pd)) head.remainder.1)
      (le_of_lt po)
    rw [reconstruction] at h
    nlinarith
  have shift : (p : Int)-1-((p : Int)-1-count) = count := by omega
  simp only [Gleitkomma.normQD, shift, Nat.cast_nonneg, ↓reduceIte,
    Int.toNat_natCast]
  have numerator : (origin.toNat * 2^distance) * 2^count =
      (origin * 2^(count+distance)).toNat := by
    apply Int.ofNat_inj.mp
    rw [Int.toNat_of_nonneg (mul_nonneg nonnegative (le_of_lt pc))]
    push_cast
    rw [Int.toNat_of_nonneg nonnegative, pow_add]
    ring
  rw [numerator]
  have fields := head.output_fields
  have den : (0 : Int) < 8 * 2^(distance+originDistance) := by positivity
  constructor
  · apply Int.ofNat_inj.mp
    push_cast
    rw [Int.toNat_of_nonneg (Int.ediv_nonneg head.quotient.1 (by decide))]
    simpa only [Int.natCast_ediv, Int.toNat_of_nonneg
      (mul_nonneg nonnegative (le_of_lt pc))] using fields.1
  constructor
  · apply Int.ofNat_inj.mp
    push_cast
    rw [Int.toNat_of_nonneg (Int.emod_nonneg q (by decide)),
      Int.toNat_of_nonneg head.remainder.1]
    simpa only [Int.natCast_emod, Int.toNat_of_nonneg
      (mul_nonneg nonnegative (le_of_lt pc))] using fields.2.1
  · trivial

#print axioms FloatNormalizeHead.normQD_output

end
end Gabbro.Stage0.Senke
