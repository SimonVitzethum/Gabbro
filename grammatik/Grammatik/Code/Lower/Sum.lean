import Grammatik.Kern.Semantik.Semantik

/-
  File:      Grammatik/Code/Lower/Sum.lean
  Subject:   TRACK L, PHASE L1 -- THE WORD OF A TAGGED VALUE (`sum cs`): case number and payload packed
             in ONE integer, so that a tagged value is a register and a cell like any number.

  A value of `sum cs` is a case `i` (below `L = cs.length`) and, if the case carries a number in
  `lo .. hi`, a payload `n`. Its word is `i + L * (n - lo)` (`i` for a case without payload). So the
  case number is the word modulo `L` and the payload offset is the word divided by `L`: `match` needs
  one unsigned remainder and one unsigned division by the constant `L`, never a shift and never a
  field. Every word lies in `0 .. L * S - 1`, `S` being the largest number of values a payload may take
  (at least 1); the word is carried at `Ar.wid 0 (L * S)` bits, so that `L` itself is below `2^w` and the
  divisor of those two instructions is never zero.

  WHAT IS HERE: the numbers (`spreadOf`, `spreadMax`, `sumTop`), the word of a value (`packZ`), its
  bounds and the decoding lemmas (`packZ_mod`, `packZ_div`).
-/

namespace Gabbro.Code.Lower

open Gabbro.Grammatik (Nutzlast Wert Zahl)

/-- The number of values a payload may take (`1` for a case without one). -/
def spreadOf : Option (Int × Int) → Int
  | none => 1
  | some (lo, hi) => hi - lo + 1

/-- The largest spread over all cases, and at least `1`. -/
def spreadMax (cs : List (Option (Int × Int))) : Int :=
  cs.foldr (fun c a => max (spreadOf c) a) 1

/-- The words of `sum cs` are below this bound. -/
def sumTop (cs : List (Option (Int × Int))) : Int := (cs.length : Int) * spreadMax cs

theorem spreadMax_pos (cs : List (Option (Int × Int))) : 1 ≤ spreadMax cs := by
  induction cs with
  | nil => exact Int.le_refl _
  | cons c cs ih =>
      simp only [spreadMax, List.foldr_cons] at ih ⊢
      exact Int.le_trans ih (Int.le_max_right _ _)

theorem spreadOf_le_max (cs : List (Option (Int × Int))) (i : Fin cs.length) :
    spreadOf (cs.get i) ≤ spreadMax cs := by
  induction cs with
  | nil => exact Fin.elim0 i
  | cons c cs ih =>
      obtain ⟨i, hi⟩ := i
      cases i with
      | zero => simp only [spreadMax, List.foldr_cons]; exact Int.le_max_left _ _
      | succ j =>
          have := ih ⟨j, Nat.lt_of_succ_lt_succ hi⟩
          simp only [spreadMax, List.foldr_cons] at this ⊢
          exact Int.le_trans this (Int.le_max_right _ _)

/-- The payload of a value, as a non-negative offset. -/
def payOff : (c : Option (Int × Int)) → Nutzlast c → Int
  | none, _ => 0
  | some (lo, hi), z => (z : Zahl lo hi).n - lo

theorem payOff_bounds : ∀ (c : Option (Int × Int)) (z : Nutzlast c),
    0 ≤ payOff c z ∧ payOff c z ≤ spreadOf c - 1
  | none, _ => by simp [payOff, spreadOf]
  | some (lo, hi), z => by
      have h1 := (z : Zahl lo hi).lo_le
      have h2 := (z : Zahl lo hi).le_hi
      simp only [payOff, spreadOf]
      omega

/-- The word of a value of `sum cs`. -/
def packZ {cs : List (Option (Int × Int))} (v : Σ i : Fin cs.length, Nutzlast (cs.get i)) : Int :=
  (v.1.val : Int) + (cs.length : Int) * payOff (cs.get v.1) v.2

theorem packZ_nonneg {cs : List (Option (Int × Int))} (v : Σ i : Fin cs.length, Nutzlast (cs.get i)) :
    0 ≤ packZ v := by
  have h1 := (payOff_bounds _ v.2).1
  have h2 : (0 : Int) ≤ (cs.length : Int) := Int.natCast_nonneg _
  have := Int.mul_nonneg h2 h1
  unfold packZ
  have := Int.natCast_nonneg v.1.val
  omega

theorem packZ_lt {cs : List (Option (Int × Int))} (v : Σ i : Fin cs.length, Nutzlast (cs.get i)) :
    packZ v < sumTop cs := by
  have hb := payOff_bounds _ v.2
  have hs := spreadOf_le_max cs v.1
  have hL : (0 : Int) ≤ (cs.length : Int) := Int.natCast_nonneg _
  have hi : (v.1.val : Int) + 1 ≤ (cs.length : Int) := by exact_mod_cast v.1.isLt
  have h3 : (cs.length : Int) * payOff (cs.get v.1) v.2 ≤ (cs.length : Int) * (spreadMax cs - 1) :=
    Int.mul_le_mul_of_nonneg_left (by omega) hL
  have e : (cs.length : Int) * (spreadMax cs - 1) = (cs.length : Int) * spreadMax cs - cs.length := by
    rw [Int.mul_sub, Int.mul_one]
  unfold packZ sumTop
  omega

theorem packZ_mod {cs : List (Option (Int × Int))} (v : Σ i : Fin cs.length, Nutzlast (cs.get i)) :
    packZ v % (cs.length : Int) = (v.1.val : Int) := by
  unfold packZ
  have hi : (v.1.val : Int) < (cs.length : Int) := by exact_mod_cast v.1.isLt
  rw [Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) hi

theorem packZ_div {cs : List (Option (Int × Int))} (v : Σ i : Fin cs.length, Nutzlast (cs.get i)) :
    packZ v / (cs.length : Int) = payOff (cs.get v.1) v.2 := by
  unfold packZ
  have hi : (v.1.val : Int) < (cs.length : Int) := by exact_mod_cast v.1.isLt
  have hpos : (0 : Int) < (cs.length : Int) := Int.lt_of_le_of_lt (Int.natCast_nonneg _) hi
  rw [Int.add_mul_ediv_left _ _ (Int.ne_of_gt hpos), Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _) hi]
  omega

end Gabbro.Code.Lower
