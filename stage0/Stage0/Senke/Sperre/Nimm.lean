/-
  File:      stage0/Stage0/Senke/Sperre/Nimm.lean
  Subject:   Where a piece of code lies in a larger one (`At`) and the comparison results the lock code reads.
-/
module
public import Stage0.Senke.Sperre.Schritt
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

/-- The code `xs` lies in `code` from instruction `p` on. -/
def At (code : List II) (p : Nat) (xs : List II) : Prop := ∀ j, j < xs.length → code[p + j]? = xs[j]?

theorem At.get {code xs : List II} {p : Nat} (h : At code p xs) {j : Nat} {x : II} (hx : xs[j]? = some x) :
    code[p + j]? = some x := by
  obtain ⟨hj, _⟩ := List.getElem?_eq_some_iff.mp hx
  rw [h j hj, hx]

theorem At.left {code xs ys : List II} {p : Nat} (h : At code p (xs ++ ys)) : At code p xs := fun j hj => by
  rw [h j (by simp; omega), List.getElem?_append_left hj]

theorem At.right {code xs ys : List II} {p : Nat} (h : At code p (xs ++ ys)) : At code (p + xs.length) ys :=
  fun j hj => by
    rw [Nat.add_assoc, h (xs.length + j) (by simp; omega), List.getElem?_append_right (by omega)]
    simp

theorem At.whole (code : List II) : At code 0 code := fun j _ => by rw [Nat.zero_add]

theorem bool_eq_self (x : W) : bool (x == x) = 1 := by simp [Runner.IR.bool]

theorem bool_ne {x y : W} (h : x ≠ y) : bool (x == y) = 0 := by simp [Runner.IR.bool, h]

end Gabbro.Stage0.Senke
