/-
  File:      Grammatik/Bausteine/Arena/ArenaStaticReset.lean
  Subject:   C18, Kern side: the checked reset of a static-array range.

  The source range form `reset A at i count n` is for a zero-initialized
  STATIC ARRAY, never an arena (`reset A;` keeps its whole-arena counter
  store). This file carries the model half that the elaborator and the
  future lowering share:

  * `rangeOk` -- the range check in mathematical naturals: `i ≤ len`
    and `k ≤ len - i`. Empty ranges at `i = len` are allowed; nothing is
    clipped or wrapped.
  * `ZeroAdmitting` -- the types with a proved zero representation and no
    linear or live capability erased by the reset: numbers holding zero,
    truth values, arrays over such an element, strings. Function pointers,
    references, plain pointers, options, sums, reasons, `never` and floats
    are NOT admitted: zero bytes need not encode a valid `fnptr`, `ref` or
    nonzero range, and floats stay outside the kernel IEEE scope of this
    package.
  * `zeroValue` -- the zero of such a type, as a `Val`.
  * `resetFinW` -- the range store as a pure function update, with its two
    observation laws: zero at every selected index, unchanged outside.
  * `ResetRange` -- the checked derivation for one resolved static-array
    global: the global has an array type of known length, the range
    `[i, i + k)` is valid, the element type admits zero. Guard, mode and
    alias scope are admission duties beside this derivation, not fields of
    it. The lowering expands the source form into existing typed array
    stores; no second evaluator is added.

  Page return (releasing backing pages through an explicit user service)
  lives in `ArenaPageReturn.lean`; admission of the two together in
  `Zielsatz/Kern/Akzeptiert/Teil3.lean`. The lowering still refuses
  `UStmt.resetRange` by name until the generic range-store proof and the
  page-return bridge are connected.
-/
module

public import Grammatik.Kern.Syntax.Syntax.Teil1

@[expose] public section

namespace Gabbro.Grammatik

/-- The range check in mathematical naturals: the start lies in the array
    (`i = len` allowed for an empty range) and the count fits behind it.
    Invalid ranges are logical failures, never clipped or wrapped ranges. -/
def rangeOk (len i k : Nat) : Bool :=
  decide (i ≤ len) && decide (k ≤ len - i)

theorem rangeOk_iff {len i k : Nat} :
    rangeOk len i k = true ↔ i ≤ len ∧ k ≤ len - i := by
  simp only [rangeOk, Bool.and_eq_true, decide_eq_true_eq]

/-- Types with a proved zero representation and no linear or live
    capability erased by a reset. An `int` admits zero only when zero lies
    in its range; `bool` reads `false`; arrays and strings recurse. Not
    admitted: `fnptr`, `ptr`, `ref`, `opt`, `sum`, `why`, `never`, `fl`. -/
inductive ZeroAdmitting : Ty → Prop where
  | intZero {lo hi : Int} : lo ≤ 0 → 0 ≤ hi → ZeroAdmitting (.int lo hi)
  | boolZero : ZeroAdmitting .bool
  | arrZero {τ : Ty} {n : Nat} : ZeroAdmitting τ → ZeroAdmitting (.arr τ n)
  | strZero {n : Nat} : ZeroAdmitting (.str n)

/-- The same predicate, decided. -/
def zeroAdmittingB : Ty → Bool
  | .int lo hi => decide (lo ≤ 0) && decide (0 ≤ hi)
  | .bool => true
  | .arr τ _ => zeroAdmittingB τ
  | .str _ => true
  | _ => false

theorem zeroAdmittingB_iff {τ : Ty} : zeroAdmittingB τ = true ↔ ZeroAdmitting τ := by
  induction τ with
  | int lo hi =>
    simp only [zeroAdmittingB, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact .intZero h1 h2
    · intro h; cases h with | intZero h1 h2 => exact ⟨h1, h2⟩
  | bool =>
    simp only [zeroAdmittingB]
    constructor
    · intro _; exact .boolZero
    · intro _; rfl
  | opt n =>
    simp only [zeroAdmittingB]
    constructor
    · intro h; exact absurd h Bool.false_ne_true
    · intro h; cases h
  | sum cs =>
    simp only [zeroAdmittingB]
    constructor
    · intro h; exact absurd h Bool.false_ne_true
    · intro h; cases h
  | why n =>
    simp only [zeroAdmittingB]
    constructor
    · intro h; exact absurd h Bool.false_ne_true
    · intro h; cases h
  | never =>
    simp only [zeroAdmittingB]
    constructor
    · intro h; exact absurd h Bool.false_ne_true
    · intro h; cases h
  | fl _ =>
    simp only [zeroAdmittingB]
    constructor
    · intro h; exact absurd h Bool.false_ne_true
    · intro h; cases h
  | fnptr s =>
    simp only [zeroAdmittingB]
    constructor
    · intro h; exact absurd h Bool.false_ne_true
    · intro h; cases h
  | ptr cap =>
    simp only [zeroAdmittingB]
    constructor
    · intro h; exact absurd h Bool.false_ne_true
    · intro h; cases h
  | ref t =>
    simp only [zeroAdmittingB]
    constructor
    · intro h; exact absurd h Bool.false_ne_true
    · intro h; cases h
  | arr τ _ ih =>
    simp only [zeroAdmittingB]
    constructor
    · intro h; exact .arrZero (ih.mp h)
    · intro h; cases h with | arrZero h' => exact ih.mpr h'
  | str n =>
    simp only [zeroAdmittingB]
    constructor
    · intro _; exact .strZero
    · intro _; rfl

/-- The zero of a zero-admitting type, as a value. -/
def zeroValue {F : Type} {passt : F → Nat → Bool} : (τ : Ty) → ZeroAdmitting τ → Val F passt τ
  | _, .intZero h1 h2 => ⟨0, h1, h2⟩
  | _, .boolZero => false
  | _, .arrZero h' => fun _ => zeroValue _ h'
  | _, .strZero => ⟨[], Nat.zero_le _⟩

/-- The range store as a pure update: `zero` at every index of
    `[i, i + k)`, the old value everywhere else. -/
def resetFinW {α : Type} {n : Nat} (a : Fin n → α) (i k : Nat) (zero : α) :
    Fin n → α :=
  fun j => if i ≤ j.val ∧ j.val < i + k then zero else a j

/-- A selected index reads zero after the reset. -/
theorem resetFinW_get_in {α : Type} {n : Nat} (a : Fin n → α) (i k : Nat)
    (zero : α) (j : Fin n) (h1 : i ≤ j.val) (h2 : j.val < i + k) :
    resetFinW a i k zero j = zero := by
  have hc : i ≤ j.val ∧ j.val < i + k := ⟨h1, h2⟩
  simp only [resetFinW, hc, ↓reduceIte]

/-- An index outside the range keeps its old value, including padding and
    metadata outside the payload contract. -/
theorem resetFinW_get_out {α : Type} {n : Nat} (a : Fin n → α) (i k : Nat)
    (zero : α) (j : Fin n) (h : ¬ (i ≤ j.val ∧ j.val < i + k)) :
    resetFinW a i k zero j = a j := by
  simp only [resetFinW, h, ↓reduceIte]

/-- The checked reset derivation for one resolved static-array global: the
    global has array type `.arr elem len`, the range `[i, i + k)` is valid
    (`startOk` allows the empty range at `i = len`), and the element type
    admits zero. Guard, mode and alias scope are admission duties beside
    this derivation, not fields of it. -/
structure ResetRange (D : Deklaration) (g : D.Glob) where
  len : Nat
  elem : Ty
  arr : D.gtyp g = .arr elem len
  i k : Nat
  startOk : i ≤ len
  countOk : k ≤ len - i
  zero : ZeroAdmitting elem

/-- A selected element of a checked reset observes the typed zero. -/
theorem resetRange_reads_zero {D : Deklaration} {g : D.Glob}
    (R : ResetRange D g) (v : Wert D (D.gtyp g)) (j : Fin R.len)
    (h1 : R.i ≤ j.val) (h2 : j.val < R.i + R.k) :
    resetFinW (R.arr ▸ v) R.i R.k (zeroValue _ R.zero) j = zeroValue _ R.zero :=
  resetFinW_get_in _ _ _ _ _ h1 h2

/-- An element outside a checked reset keeps its old value. -/
theorem resetRange_outside_same {D : Deklaration} {g : D.Glob}
    (R : ResetRange D g) (v : Wert D (D.gtyp g)) (j : Fin R.len)
    (h : ¬ (R.i ≤ j.val ∧ j.val < R.i + R.k)) :
    resetFinW (R.arr ▸ v) R.i R.k (zeroValue _ R.zero) j = (R.arr ▸ v) j :=
  resetFinW_get_out _ _ _ _ _ h

theorem rangeOk_zeuge : rangeOk 4 1 2 = true := rfl

theorem rangeOk_empty_at_end_zeuge : rangeOk 4 4 0 = true := rfl

theorem rangeOk_negative_zeuge : rangeOk 4 3 2 = false := rfl

theorem zeroAdmittingB_zeuge : zeroAdmittingB (.arr (.int 0 255) 4) = true := rfl

theorem zeroAdmittingB_fnptr_zeuge : zeroAdmittingB (.fnptr 0) = false := rfl

theorem resetFinW_zeuge : ∀ j : Fin 4,
    resetFinW (fun j => j.val) 1 2 0 j =
      (if 1 ≤ j.val ∧ j.val < 3 then 0 else j.val) := fun _ => rfl

#print axioms rangeOk_iff
#print axioms zeroAdmittingB_iff
#print axioms resetFinW_get_in
#print axioms resetFinW_get_out
#print axioms resetRange_reads_zero
#print axioms resetRange_outside_same

end Gabbro.Grammatik
