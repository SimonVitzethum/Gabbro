/- Actual bounded dyadic normalization in integer runner instructions. -/
import Stage0.Senke.Ausdruck.Arithmetik.Adaptiv

namespace Gabbro.Stage0.Senke
open Runner.IR

/-- State slots are quotient, exact remainder, denominator distance, target,
    remaining fuel, and completed transfers. Distances above 61 are retained
    explicitly: no machine shift attempts to materialize a large denominator.
    Preconditions for the pending simulation are a word-sized nonnegative
    remainder, target at most 2^60, and canonical input remainder.
    The large branch transfers a remainder bit at the 63/62 boundaries too. -/
def floatNormalizeLoopL (base : Nat) : Option (List II × Nat) := do
  let q := base
  let r := base+1
  let k := base+2
  let target := base+3
  let fuel := base+4
  let count := base+5
  let tmp := base+6
  let den := base+7
  let load := fun (s j : Nat) => some ([ci 2 j s 0], j+1)
  let cq ← floatNormalizeStepL false (base+8) (load q) (load r) (load den) (load target)
  let cr ← floatNormalizeStepL true (base+9) (load q) (load r) (load den) (load target)
  let small := [ci 1 tmp 1 0, ci 11 den tmp k] ++ cq.1 ++ cr.1 ++
    [ci 2 q (base+8) 0, ci 2 r (base+9) 0]
  -- After decrementing k, materialize the threshold only when k < 63.
  -- At larger distances every nonnegative signed-word remainder is below it.
  let carry := [ci 1 tmp 1 0, ci 11 den tmp k, ci 13 tmp r den,
    ci 1 (base+8) 1 0, ci 4 (base+8) (base+8) tmp,
    ci 5 den den (base+8), ci 4 r r den, ci 3 q q (base+8)]
  let large := [ci 1 tmp 2 0, ci 5 q q tmp, ci 1 tmp 1 0, ci 4 k k tmp,
    ci 1 tmp 63 0, ci 13 tmp k tmp, ci 19 tmp (16 * (1+carry.length)) 0] ++ carry
  let tail := [ci 1 tmp 1 0, ci 3 count count tmp, ci 4 fuel fuel tmp,
    ci 18 (-(16 * (6 + large.length + 1 + small.length + 3) : Int)) 0 0]
  let total := 6 + large.length + 1 + small.length + tail.length
  let head := [ci 19 fuel (16 * total) 0, ci 13 tmp q target,
    ci 19 tmp (16 * (total-2)) 0, ci 1 tmp 61 0,
    ci 13 tmp tmp k, ci 19 tmp (16 * (1 + large.length + 1)) 0]
  pure (head ++ large ++ [ci 18 (16 * (1 + small.length)) 0 0] ++ small ++ tail,
    max cq.2 cr.2)

/-- With no remainder carry, doubling the quotient and decrementing the
    distance preserves reconstruction. Canonicality additionally needs the
    bound at the new distance; the emitted branch now handles a carry too. -/
theorem floatNormalizeLoop_large_reconstruct (q r : Int) (k : Nat) :
    (2*q) * 2^k + r = q * 2^(k+1) + r := by
  rw [pow_succ]
  ring

/-- This is the precise preservation obligation for a zero-carry large step.
    Canonicality at the old distance alone does not imply this condition. -/
theorem floatNormalizeLoop_large_canonical (r : Int) (k : Nat) :
    (0 ≤ r ∧ r < 2^k) ↔ (0 ≤ r ∧ r < 2^(k+1) ∧ r < 2^k) := by
  have hp : (0 : Int) < 2^k := Int.pow_pos (by decide)
  rw [pow_succ]
  constructor <;> intro h
  · exact ⟨h.1, by omega, h.2⟩
  · exact ⟨h.1, h.2.2⟩

/-- A bounded exact tail suffices uniformly for every large distance, with
    no materialization of a denominator in a machine word. -/
theorem floatNormalizeLoop_large_tail_bound (r : Int) (k : Nat)
    (hr : 0 ≤ r ∧ r < 2^61) (hk : 61 ≤ k) :
    0 ≤ r ∧ r < 2^k := by
  have hp : (2 : Int)^61 ≤ 2^k := by
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk)
  exact ⟨hr.1, lt_of_lt_of_le hr.2 hp⟩

/-- Signed quotient doubling cannot overflow while the loop is active under
    its documented target ceiling. The counter requires its own initial bound. -/
theorem floatNormalizeLoop_large_word_bounds (q target : Int)
    (hq : 0 ≤ q) (ha : q < target) (ht : target ≤ 2^60) :
    0 ≤ 2*q ∧ 2*q < 2^61 := by omega

/-- The old-distance remainder bound and signed word bound do not suffice:
    the former carry-free k=62 branch left a noncanonical remainder at k=61. -/
theorem floatNormalizeLoop_large_boundary_zeuge :
    (0 : Int) ≤ 2^61 ∧ (2 : Int)^61 < 2^62 ∧
    (2 : Int)^61 < 2^63 ∧ ¬ ((2 : Int)^61 < 2^61) := by
  decide +kernel

#print axioms floatNormalizeLoop_large_reconstruct
#print axioms floatNormalizeLoop_large_canonical
#print axioms floatNormalizeLoop_large_tail_bound
#print axioms floatNormalizeLoop_large_word_bounds
#print axioms floatNormalizeLoop_large_boundary_zeuge

/-- Fetch the budget test from the actual emitted block. -/
theorem floatNormalizeLoopL_head (base : Nat) {code : List II} {top : Nat}
    (hc : floatNormalizeLoopL base = some (code, top)) :
    code[0]? = some (ci 19 (base+4) (16 * code.length) 0) := by
  unfold floatNormalizeLoopL at hc
  simp [floatNormalizeStepL, wordL] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp [bin2]

/-- The budget-test displacement fits its actual signed instruction field. -/
theorem floatNormalizeLoopL_exit_encoding (base : Nat) {code : List II} {top : Nat}
    (hc : floatNormalizeLoopL base = some (code, top)) :
    lit32 (16 * code.length) = true := by
  unfold floatNormalizeLoopL at hc
  simp [floatNormalizeStepL, wordL] at hc
  obtain ⟨rfl, rfl⟩ := hc
  norm_num [bin2, lit32]

open Gabbro.Grammatik Runner Runner.Mem

/-- Actual emitted budget exit: fetch the first instruction from the block,
    execute Runner.step, and reach precisely its end without any memory write.
    All frame bytes, permissions, pointers, and temporary slots are preserved. -/
theorem floatNormalizeLoopL_zero [Kern] {D : Deklaration} {L : Lay D}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K base top reserved : Nat}
    {code : List II}
    (hc : floatNormalizeLoopL base = some (code, top))
    (h : Pre L m pc fp K base code ρ W reserved)
    (hb : base+4 < K)
    (hz : m.rd64 (slot fp (BitVec.ofNat 64 (base+4))) = some 0) :
    Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16*code.length), fp⟩ m ∧
      Agree fp base K m m := by
  have he := floatNormalizeLoopL_head base hc
  have hn : 0 < code.length := by
    by_contra hh
    have hn : code[0]? = none := List.getElem?_eq_none (by omega)
    rw [hn] at he
    cases he
  have hi := h.code 0 hn
  have entry : code[0] = ci 19 (base+4) (16*code.length) 0 := by
    simpa only [List.getElem?_eq_getElem hn, Option.some.injEq] using he
  rw [entry] at hi
  simp only [ci, Nat.mul_zero, BitVec.add_zero] at hi
  have hs : sx (II.f ((base : Int)+4)) = BitVec.ofNat 64 (base+4) := by
    simpa using (sx_nat (d := base+4) (by have := h.small; omega))
  have hz' : m.rd64 (slot fp (sx (II.f ((base : Int)+4)))) = some 0 := by
    rw [hs]
    exact hz
  have run := run_step (t := ⟨pc, fp⟩) hi (by decide)
    (run_brz_zero (t := ⟨pc, fp⟩) hi hz')
  refine ⟨?_, Agree.refl _ _ _ _⟩
  have enc := floatNormalizeLoopL_exit_encoding base hc
  have ee : sx (II.f (16 * (code.length : Int))) =
      BitVec.ofNat 64 (16*code.length) := by
    rw [sx_lit enc]
    rw [show (16 * (code.length : Int)) = ((16*code.length : Nat) : Int) by omega]
    exact BitVec.ofInt_natCast 64 _
  simpa only [ee] using Star.one run


#print axioms floatNormalizeLoopL_head
#print axioms floatNormalizeLoopL_exit_encoding
#print axioms floatNormalizeLoopL_zero

/-- The corrected carry at a halved denominator preserves exact value and
    canonicality for every canonical input, including the old counterexample. -/
theorem floatNormalizeLoop_large_transfer (q r : Int) (k : Nat)
    (hr : 0 ≤ r ∧ r < 2^(k+1)) :
    let c : Int := if r < 2^k then 0 else 1
    (2*q+c)*2^k + (r-c*2^k) = q*2^(k+1)+r ∧
    0 ≤ r-c*2^k ∧ r-c*2^k < 2^k := by
  have hp : (0 : Int) < 2^k := Int.pow_pos (by decide)
  rw [pow_succ] at hr
  dsimp only
  split <;> constructor
  · rw [pow_succ]; ring
  · constructor <;> omega
  · rw [pow_succ]; ring
  · constructor <;> omega

/-- Skipping the threshold computation above the signed-word range loses
    no carry for any nonnegative signed-word remainder. -/
theorem floatNormalizeLoop_large_no_carry (r : Int) (k : Nat)
    (hr : r < 2^63) (hk : 63 ≤ k) : r < 2^k := by
  have hp : (2 : Int)^63 ≤ 2^k := by
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk)
  exact lt_of_lt_of_le hr hp

/-- The corrected quotient, including its carry, still fits a positive
    signed word under the existing target ceiling. No input restriction is added. -/
theorem floatNormalizeLoop_large_carry_word_bounds (q target c : Int)
    (hq : 0 ≤ q) (ha : q < target) (ht : target ≤ 2^60)
    (hc : 0 ≤ c ∧ c ≤ 1) :
    0 ≤ 2*q+c ∧ 2*q+c < 2^61 := by omega

#print axioms floatNormalizeLoop_large_carry_word_bounds

/-- Joint boundary witnesses for the corrected arithmetic, with a genuine
    carry at distance 62 and a retained tail before the next carry at 63. -/
theorem floatNormalizeLoop_large_transfer_zeuge :
    (1 : Int)*2^61 + 0 = 0*2^62+2^61 ∧
    (1 : Int)*2^62 + 0 = 0*2^63+2^62 ∧
    (0 : Int)*2^62 + 2^61 = 0*2^63+2^61 ∧
    (floatNormalizeStep 0 (2^60) (2^61) 8) = (1,0) := by
  decide +kernel

#print axioms floatNormalizeLoop_large_transfer
#print axioms floatNormalizeLoop_large_no_carry
#print axioms floatNormalizeLoop_large_transfer_zeuge

end Gabbro.Stage0.Senke
