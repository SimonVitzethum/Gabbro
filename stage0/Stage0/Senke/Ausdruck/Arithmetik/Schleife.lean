/- Actual bounded dyadic normalization in integer runner instructions. -/
import Stage0.Senke.Ausdruck.Arithmetik.Adaptiv

namespace Gabbro.Stage0.Senke
open Runner.IR

/-- State slots are quotient, exact remainder, denominator distance, target,
    remaining fuel, and completed transfers. Distances above 61 are retained
    explicitly: no machine shift attempts to materialize a large denominator.
    Preconditions for the pending simulation are a word-sized nonnegative
    remainder, target at most 2^60, and canonical input remainder. -/
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
  let large := [ci 1 tmp 2 0, ci 5 q q tmp, ci 1 tmp 1 0, ci 4 k k tmp]
  let tail := [ci 1 tmp 1 0, ci 3 count count tmp, ci 4 fuel fuel tmp,
    ci 18 (-(16 * (6 + large.length + 1 + small.length + 3) : Int)) 0 0]
  let total := 6 + large.length + 1 + small.length + tail.length
  let head := [ci 19 fuel (16 * total) 0, ci 13 tmp q target,
    ci 19 tmp (16 * (total-2)) 0, ci 1 tmp 61 0,
    ci 13 tmp tmp k, ci 19 tmp (16 * (1 + large.length + 1)) 0]
  pure (head ++ large ++ [ci 18 (16 * (1 + small.length)) 0 0] ++ small ++ tail,
    max cq.2 cr.2)

/-- The large-distance instructions double the quotient and decrement the
    denominator distance without touching the remainder. Reconstruction is
    exact, but canonicality requires a bound at the *new* distance. -/
theorem floatNormalizeLoop_large_reconstruct (q r : Int) (k : Nat) :
    (2*q) * 2^k + r = q * 2^(k+1) + r := by
  rw [pow_succ]
  ring

/-- This is the precise preservation obligation for the emitted large branch.
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
    the actual k=62 branch can leave a noncanonical remainder at k=61. -/
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

end Gabbro.Stage0.Senke
