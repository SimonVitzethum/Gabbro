module

public import Grammatik.Kern.Syntax.Typen.Produkt
public import Init.Data.List.TakeDrop

@[expose] public section

namespace Gabbro.Grammatik

variable {F : Type} {passt : F → Nat → Bool}

/-!
Aggregate value laws for O20/P1. `Val` represents arrays by functions, strings by
bounded byte lists, products by tuples, and tagged payloads by dependent pairs.
None of these carries an aggregate storage address or observable copy operation.
The product get/set/frame/extensionality laws already live in `Typen.Produkt`.

These are facts about G values, not a heap-sharing simulation. A compiler must
still relate its storage to these values and preserve every surviving alias when
it reuses storage. Equality of values does not imply unique ownership of storage.
In particular, an aggregate can contain `.ref` values: copying it copies the
reference numbers, not the cells to which those references grant access.
-/

/-- The replaced array element reads back its replacement. -/
theorem arrSetW_same {α : Type} {n : Nat} (a : Fin n → α) (k : Fin n) (v : α) :
    arrSetW a k v k = v := by
  simp only [arrSetW, ite_true]

/-- Every other array element retains its old value. -/
theorem arrSetW_other {α : Type} {n : Nat} (a : Fin n → α) (k j : Fin n)
    (v : α) (h : j ≠ k) : arrSetW a k v j = a j := by
  simp only [arrSetW, if_neg h]

/-- A proposed array update has exactly G's value iff it changes the selected
element as specified and preserves every other element. This characterizes the
result value; it makes no claim about ownership of a physical array. -/
theorem arrSetW_characterization {α : Type} {n : Nat} (a b : Fin n → α)
    (k : Fin n) (v : α) :
    b = arrSetW a k v ↔ b k = v ∧ ∀ j, j ≠ k → b j = a j := by
  constructor
  · intro h
    subst b
    exact ⟨arrSetW_same a k v, fun j hj => arrSetW_other a k j v hj⟩
  · rintro ⟨hsame, hother⟩
    funext j
    by_cases h : j = k
    · subst j
      rw [arrSetW_same]
      exact hsame
    · rw [arrSetW_other a k j v h]
      exact hother j h

/-- Writing the value already present leaves the entire array value unchanged. -/
theorem arrSetW_read {α : Type} {n : Nat} (a : Fin n → α) (k : Fin n) :
    arrSetW a k (a k) = a := by
  funext j
  by_cases h : j = k
  · subst j
    exact arrSetW_same a k (a k)
  · exact arrSetW_other a k j (a k) h

/-- A later replacement at the same position discards the earlier replacement. -/
theorem arrSetW_overwrite {α : Type} {n : Nat} (a : Fin n → α) (k : Fin n)
    (v w : α) : arrSetW (arrSetW a k v) k w = arrSetW a k w := by
  funext j
  by_cases h : j = k <;> simp only [arrSetW, h, if_true, if_false]

/-- Repeated replacement of a record field needs only its latest value. Together
with `prodGetW_prodSetW_of_disj` and `ProdVal.prod_ext`, this supplies the record
counterpart of the array result characterization above. -/
theorem prodSetW_overwrite :
    ∀ {fs : List Ty} {τ : Ty} (i : FieldAt fs τ) (a : ProdVal F passt fs)
      (v w : Val F passt τ), prodSetW i (prodSetW i a v) w = prodSetW i a w
  | _, _, .head, _, _, _ => rfl
  | _, _, .tail i, a, v, w => by
      change ProdVal.pcons (ProdVal.hd a) (prodSetW i (prodSetW i (ProdVal.tl a) v) w) =
        ProdVal.pcons (ProdVal.hd a) (prodSetW i (ProdVal.tl a) w)
      exact congrArg (ProdVal.pcons (ProdVal.hd a)) (prodSetW_overwrite i (ProdVal.tl a) v w)

/-- Reading inside the existing string-prefix operation gives the original byte.
This includes indices beyond the actual length: both reads use G's zero default.
It is the value fact needed for a retained-source representation of `strWeit`.
General substring/subarray expressions are not yet constructors of G. -/
theorem strGetW_strWeitW {n : Nat} (m : Nat)
    (s : { bs : List (Zahl 0 255) // bs.length ≤ n })
    (i : Int) (h : i.toNat < m) :
    strGetW (strWeitW m s) i = strGetW s i := by
  by_cases hnonneg : 0 ≤ i
  · simp only [strGetW, if_pos hnonneg, strWeitW]
    rw [List.getElem?_take_of_lt h]
  · simp only [strGetW, if_neg hnonneg]

/-- Widening a string's bound preserves its complete byte list, without padding. -/
theorem strWeitW_bytes_of_le {n : Nat} (m : Nat)
    (s : { bs : List (Zahl 0 255) // bs.length ≤ n })
    (h : n ≤ m) : (strWeitW m s).1 = s.1 := by
  exact List.take_of_length_le (by have := s.2; omega)

end Gabbro.Grammatik
