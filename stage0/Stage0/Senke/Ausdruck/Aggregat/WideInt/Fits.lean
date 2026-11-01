/-
  File:      stage0/Stage0/Senke/Ausdruck/Aggregat/WideInt/Fits.lean
  Subject:   Where the values of a bounded integer type lie, in the readings the multiword kernels need.

  A value of `Zahl lo hi` fits `integerWords lo hi` limbs in the reading its interval selects (`extSigned`):
  signed when the interval admits negatives, unsigned otherwise. The signed kernels read every operand in the
  signed range of `k` limbs, which `signedWords` guarantees. A kernel's `k`-limb output holds the result's
  canonical limbs in its first `integerWords` words.
-/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Literal.Extend
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.Place
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem

theorem signed_pow (k : Nat) (hk : 1 ≤ k) : (2 : Int) ^ (64 * k - 1) = 2 ^ 63 * 2 ^ (64 * (k - 1)) := by
  rw [← Int.pow_add]
  congr 1
  omega

theorem integerWords_pos' (lo hi : Int) : 1 ≤ integerWords lo hi := by
  have := valueWords_pos (.int lo hi)
  simp only [valueWords] at this
  omega

theorem wideFits_zahl {lo hi : Int} (z : Zahl lo hi) : WideFits (extSigned lo) (integerWords lo hi) z.n := by
  have pos := integerWords_pos' lo hi
  by_cases neg : lo < 0
  · have range := integerWords_signed neg z.lo_le z.le_hi
    rw [signed_pow _ pos] at range
    have flag : extSigned lo = true := by simp only [extSigned, decide_eq_true_eq]; exact neg
    rw [flag]
    simp only [WideFits, ite_true]
    exact range
  · have range := integerWords_nonnegative (by omega : 0 ≤ lo) z.lo_le z.le_hi
    have flag : extSigned lo = false := by simp only [extSigned, decide_eq_false_iff_not]; exact neg
    rw [flag]
    simp only [WideFits, Bool.false_eq_true, ite_false]
    exact range

/-- Every value fits the signed range of `k` limbs once `k ≥ signedWords`. -/
theorem signedFits_zahl {lo hi : Int} (z : Zahl lo hi) {k : Nat} (hk : signedWords lo hi ≤ k) :
    -(2 ^ 63 * 2 ^ (64 * (k - 1))) ≤ z.n ∧ z.n < 2 ^ 63 * 2 ^ (64 * (k - 1)) := by
  have pos := integerWords_pos' lo hi
  by_cases neg : lo < 0
  · have words : integerWords lo hi ≤ k := by simp only [signedWords, neg, ↓reduceIte] at hk; exact hk
    have flag : extSigned lo = true := by simp only [extSigned, decide_eq_true_eq]; exact neg
    have fits := wideFits_zahl z
    rw [flag] at fits
    have wide := wideFits_mono (signed := true) words fits
    simpa only [WideFits, ite_true] using wide
  · have words : integerWords lo hi + 1 ≤ k := by simp only [signedWords, neg, ↓reduceIte] at hk; exact hk
    have range := integerWords_nonnegative (by omega : 0 ≤ lo) z.lo_le z.le_hi
    have capacity : (2 : Int) ^ (64 * integerWords lo hi) ≤ 2 ^ (64 * (k - 1)) := by
      exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < 2) (show 64 * integerWords lo hi ≤ 64 * (k - 1) by omega)
    have positive : (0 : Int) < 2 ^ (64 * (k - 1)) := Int.pow_pos (by decide)
    have big : (2 : Int) ^ 63 = 9223372036854775808 := by norm_num
    rw [big]
    constructor <;> omega

/-- Both endpoints of a nonempty interval lie in the signed range of `k` limbs. -/
theorem signedFits_endpoints {lo hi : Int} (h : lo ≤ hi) {k : Nat} (hk : signedWords lo hi ≤ k) :
    (-(2 ^ 63 * 2 ^ (64 * (k - 1))) ≤ lo ∧ lo < 2 ^ 63 * 2 ^ (64 * (k - 1))) ∧
    (-(2 ^ 63 * 2 ^ (64 * (k - 1))) ≤ hi ∧ hi < 2 ^ 63 * 2 ^ (64 * (k - 1))) :=
  ⟨signedFits_zahl (⟨lo, Int.le_refl _, h⟩ : Zahl lo hi) hk, signedFits_zahl (⟨hi, h, Int.le_refl _⟩ : Zahl lo hi) hk⟩

theorem WordsAt.take {m : Runner.Mem} {fp : Runner.W} {base : Nat} {ws : List Runner.W}
    (h : WordsAt m fp base ws) (n : Nat) : WordsAt m fp base (ws.take n) := by
  intro i hi
  have hi' : i < ws.length := by
    rw [List.length_take] at hi
    omega
  simp only [List.getElem_take]
  exact h i hi'

/-- The first limbs of a wider canonical encoding are the canonical encoding of the result's own type. -/
theorem valueAt_int_of_wide {D : Deklaration} {L : Lay D} {lo hi : Int} (v : Zahl lo hi) {k : Nat}
    (hk : integerWords lo hi ≤ k) {m : Runner.Mem} {fp : Runner.W} {base : Nat}
    (h : WordsAt m fp base (integerEncoding k v.n)) : ValueAt L m fp base (.int lo hi) v := by
  refine ⟨trivial, ?_⟩
  change WordsAt m fp base (integerEncoding (integerWords lo hi) v.n)
  rw [← integerEncoding_take v.n hk]
  exact h.take _

/-- The canonical limbs of a value hold its own value in the first word. -/
theorem wordsAt_first {m : Runner.Mem} {fp : Runner.W} {base k : Nat} {z : Int} (positive : 0 < k)
    (h : WordsAt m fp base (integerEncoding k z)) :
    m.rd64 (slot fp (BitVec.ofNat 64 base)) = some (BitVec.ofInt 64 z) := by
  cases k with
  | zero => omega
  | succ k => exact h 0 (by simp [integerEncoding])

theorem arithWords_left (l1 h1 l2 h2 lr hr : Int) : integerWords l1 h1 ≤ arithWords l1 h1 l2 h2 lr hr :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)

theorem arithWords_right (l1 h1 l2 h2 lr hr : Int) : integerWords l2 h2 ≤ arithWords l1 h1 l2 h2 lr hr :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)

theorem arithWords_result (l1 h1 l2 h2 lr hr : Int) : integerWords lr hr ≤ arithWords l1 h1 l2 h2 lr hr :=
  Nat.le_max_right _ _

theorem integerWords_le_signedWords (lo hi : Int) : integerWords lo hi ≤ signedWords lo hi := by
  unfold signedWords
  split <;> omega

theorem signedArithWords_left (l1 h1 l2 h2 lr hr : Int) :
    signedWords l1 h1 ≤ signedArithWords l1 h1 l2 h2 lr hr :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)

theorem signedArithWords_right (l1 h1 l2 h2 lr hr : Int) :
    signedWords l2 h2 ≤ signedArithWords l1 h1 l2 h2 lr hr :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)

theorem signedArithWords_result (l1 h1 l2 h2 lr hr : Int) :
    integerWords lr hr ≤ signedArithWords l1 h1 l2 h2 lr hr :=
  Nat.le_max_right _ _

end Gabbro.Stage0.Senke
