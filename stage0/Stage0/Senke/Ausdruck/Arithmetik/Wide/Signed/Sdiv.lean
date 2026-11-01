/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Signed/Sdiv.lean
  Subject:   Signed multiword division and remainder with truncation toward zero.

  `Zahl.sdiv` / `Zahl.srem` are `Int.tdiv` / `Int.tmod` over a divisor range that excludes zero. The
  kernel works on magnitudes: the signs are the top bits of the operands, the magnitudes are
  conditionally negated copies, the unsigned division runs, and the signs are restored
  (`sign a * sign b` for the quotient, `sign a` for the remainder). It is exact modulo `2^(64k)` for
  every pair of operands in the signed `k`-limb range, so the quotient of the minimum by `-1`
  appears with the minimum's encoding; the typing excludes a result that does not fit.
-/
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Signed.Cond

namespace Gabbro.Stage0.Senke
open Runner.IR

theorem tdiv_sign (x y : Int) :
    x.tdiv y = if (x < 0 ↔ y < 0) then ((x.natAbs / y.natAbs : Nat) : Int) else -((x.natAbs / y.natAbs : Nat) : Int) := by
  obtain ⟨ua, hua⟩ : ∃ ua, ua = x.natAbs := ⟨_, rfl⟩
  obtain ⟨ub, hub⟩ : ∃ ub, ub = y.natAbs := ⟨_, rfl⟩
  rw [← hua, ← hub]
  by_cases hx : x < 0 <;> by_cases hy : y < 0
  · have e1 : x = -(ua : Int) := by omega
    have e2 : y = -(ub : Int) := by omega
    simp only [hx, hy, iff_self, ↓reduceIte]
    rw [e1, e2, Int.neg_tdiv_neg]
    rfl
  · have e1 : x = -(ua : Int) := by omega
    have e2 : y = (ub : Int) := by omega
    simp only [hx, hy, iff_false, not_true_eq_false, ↓reduceIte]
    rw [e1, e2, Int.neg_tdiv]
    rfl
  · have e1 : x = (ua : Int) := by omega
    have e2 : y = -(ub : Int) := by omega
    simp only [hx, hy, false_iff, not_true_eq_false, ↓reduceIte]
    rw [e1, e2, Int.tdiv_neg]
    rfl
  · have e1 : x = (ua : Int) := by omega
    have e2 : y = (ub : Int) := by omega
    simp only [hx, hy, iff_self, ↓reduceIte]
    rw [e1, e2]
    rfl

theorem tmod_sign (x y : Int) :
    x.tmod y = if x < 0 then -((x.natAbs % y.natAbs : Nat) : Int) else ((x.natAbs % y.natAbs : Nat) : Int) := by
  obtain ⟨ua, hua⟩ : ∃ ua, ua = x.natAbs := ⟨_, rfl⟩
  obtain ⟨ub, hub⟩ : ∃ ub, ub = y.natAbs := ⟨_, rfl⟩
  rw [← hua, ← hub]
  by_cases hx : x < 0 <;> by_cases hy : y < 0
  · have e1 : x = -(ua : Int) := by omega
    have e2 : y = -(ub : Int) := by omega
    simp only [hx, ↓reduceIte]
    rw [e1, e2, Int.tmod_neg, Int.neg_tmod]
    rfl
  · have e1 : x = -(ua : Int) := by omega
    have e2 : y = (ub : Int) := by omega
    simp only [hx, ↓reduceIte]
    rw [e1, e2, Int.neg_tmod]
    rfl
  · have e1 : x = (ua : Int) := by omega
    have e2 : y = -(ub : Int) := by omega
    simp only [hx, ↓reduceIte]
    rw [e1, e2, Int.tmod_neg]
    rfl
  · have e1 : x = (ua : Int) := by omega
    have e2 : y = (ub : Int) := by omega
    simp only [hx, ↓reduceIte]
    rw [e1, e2]
    rfl

end Gabbro.Stage0.Senke
