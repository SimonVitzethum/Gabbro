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

end
end Gabbro.Stage0.Senke
