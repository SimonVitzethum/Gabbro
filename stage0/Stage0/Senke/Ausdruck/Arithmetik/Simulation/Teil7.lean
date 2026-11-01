module

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


/-- Derive quotient and guard decomposition from the actual loop memory
    invariant. The exact tail keeps its common scale, even for large gaps;
    no desired output fields or universal fixed-read producer is assumed. -/
theorem FloatNormalizeHead.output_fields
    {m : Runner.Mem} {fuel count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r) :
    (origin * 2^(count+distance)) / (8 * 2^(distance+originDistance) : Int) = q / 8 ∧
    (origin * 2^(count+distance)) % (8 * 2^(distance+originDistance) : Int) =
      (q % 8) * 2^(distance+originDistance) + r * 2^originDistance ∧
    0 ≤ q % 8 ∧ q % 8 < 8 ∧
      (r * 2^originDistance = 0 ↔ r = 0) := by
  have pd : (0 : Int) < 2^distance := Int.pow_pos (by decide)
  have po : (0 : Int) < 2^originDistance := Int.pow_pos (by decide)
  have pg : (0 : Int) < 2^(distance+originDistance) := Int.pow_pos (by decide)
  have gl := Int.emod_nonneg q (by decide : (8 : Int) ≠ 0)
  have gh := Int.emod_lt_of_pos q (by decide : (0 : Int) < 8)
  have split := Int.ediv_mul_add_emod q 8
  suffices pair :
      (origin * 2^(count+distance)) / (8 * 2^(distance+originDistance) : Int) = q / 8 ∧
      (origin * 2^(count+distance)) % (8 * 2^(distance+originDistance) : Int) =
        (q % 8) * 2^(distance+originDistance) + r * 2^originDistance by
    refine ⟨pair.1, pair.2, gl, gh, ?_⟩
    constructor
    · intro zero
      exact (mul_eq_zero.mp zero).resolve_right (ne_of_gt po)
    · intro zero
      simp [zero]
  apply (Int.ediv_emod_unique (by positivity : (0 : Int) < 8 * 2^(distance+originDistance))).mpr
  refine ⟨?_, ?_, ?_⟩
  · rw [← head.reconstruction, pow_add]
    have scaled := congrArg (fun x : Int => x * 2^distance * 2^originDistance) split
    nlinarith only [scaled]
  · exact add_nonneg (mul_nonneg gl (le_of_lt pg))
      (mul_nonneg head.remainder.1 (le_of_lt po))
  · have tail := Int.mul_lt_mul_of_pos_right head.remainder.2.2 po
    rw [pow_add] at *
    nlinarith

#print axioms FloatNormalizeHead.output_fields

/-- Exact reconstruction bounds the number of active transfers by the original
    alignment distance and the target precision, independently of machine fuel.
    A positive numerator cannot remain below a target at most `2^precision` after
    `originDistance + precision` doublings. -/
theorem FloatNormalizeHead.active_count_bound
    {m : Runner.Mem} {fuel count distance : Nat} {q r : Int}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r)
    (precision : Nat) (targetFits : target ≤ 2^precision)
    (positive : 0 < origin) (active : q < target) :
    count < originDistance + precision := by
  by_contra h
  have lower : originDistance + precision ≤ count := by omega
  have powers : (2 : Int)^(originDistance+precision) ≤ 2^count := by
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 1 ≤ 2) lower)
  have pd : (0 : Int) < 2^distance := Int.pow_pos (by decide)
  have po : (0 : Int) < 2^originDistance := Int.pow_pos (by decide)
  have pc : (0 : Int) < 2^count := Int.pow_pos (by decide)
  have qbound : q + 1 ≤ 2^precision := by omega
  have small : q * 2^distance + r < 2^precision * (2^distance : Int) := by
    have := mul_le_mul_of_nonneg_right qbound (le_of_lt pd)
    have := head.remainder
    nlinarith
  have strict := mul_lt_mul_of_pos_right small po
  have reconstruction := head.reconstruction
  rw [pow_add] at reconstruction powers
  have originLower : 1 ≤ origin := by omega
  have grows : (2 : Int)^count ≤ origin * 2^count := by
    simpa using mul_le_mul_of_nonneg_right originLower (le_of_lt pc)
  have scaled := mul_le_mul_of_nonneg_right (le_trans powers grows) (le_of_lt pd)
  nlinarith [reconstruction]

#print axioms FloatNormalizeHead.active_count_bound

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
