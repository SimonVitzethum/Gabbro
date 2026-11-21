module

public import Grammatik.Parser.Elab.UebersetzeAllg.StringLength
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg

open Gabbro.Grammatik.LowLevel.Construct
open Uebersetze

variable {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}

/-- Build the value slice entirely from ordinary typed reads and array
    construction. Each index fits before a core term can be constructed. -/
def arraySpan {τ : Ty} {length : Nat} (operand : Expr D Γ Λ (.arr τ length)) :
    (first count : Nat) → first + count ≤ length → Expr D Γ Λ (.arr τ count)
  | _, 0, _ => .arrNil
  | first, count + 1, fits => by
    have low : 0 ≤ (first : Int) := by omega
    have high : (first : Int) ≤ (length : Int) - 1 := by omega
    exact .arrCons (.arrGet operand (.widen low high (.lit (first : Int))))
      (arraySpan operand (first + 1) count (by omega))
termination_by structural _ count _ => count

/-- Materialising an array may duplicate its operand. The production
    reader admits that expansion only if the read footprint is preserved. -/
theorem arraySpan_reads {τ : Ty} {length : Nat} (operand : Expr D Γ Λ (.arr τ length))
    (first count : Nat) (fits : first + count ≤ length)
    (allowed : count = 1 ∨ operand.orte.isEmpty = true) :
    (arraySpan operand first count fits).orte = operand.orte := by
  rcases allowed with one | lexical
  · subst count
    simp only [arraySpan, Expr.orte, List.append_nil]
  · have empty := List.isEmpty_iff.mp lexical
    induction count generalizing first with
    | zero => exact empty.symm
    | succ count ih =>
      simp only [arraySpan, Expr.orte, List.append_nil, ih (first + 1) (by omega), empty]

/-- Element selection has the half-open slice semantics on every world
    and environment, including values that were read from memory. -/
theorem eval_arraySpan {τ : Ty} {length : Nat} (operand : Expr D Γ Λ (.arr τ length))
    (initial world : World D) (env : Env D Γ) :
    ∀ (first count : Nat) (fits : first + count ≤ length) (index : Fin count),
      eval initial (arraySpan operand first count fits) world env index =
        eval initial operand world env ⟨first + index.val, by omega⟩
  | _, 0, _, index => index.elim0
  | first, count + 1, fits, index => by
    simp only [arraySpan, eval, arrConsW]
    split
    · next zero =>
      apply congrArg (eval initial operand world env)
      apply Fin.ext
      simp [Zahl.fin, Zahl.weiter, zero]
    · next nonzero =>
      rw [eval_arraySpan operand initial world env (first + 1) count (by omega)
        ⟨index.val - 1, by omega⟩]
      apply congrArg (eval initial operand world env)
      apply Fin.ext
      simp only
      omega

/-- Relate the typed construction to the language model's slice operation. -/
theorem arraySpan_refines {τ : Ty} {length : Nat} (operand : Expr D Γ Λ (.arr τ length))
    (initial world : World D) (env : Env D Γ) (first last : Nat)
    (bounds : SliceOk length first last) :
    eval initial (arraySpan operand first (last - first) (by
      have ordered := bounds.1; have high := bounds.2
      omega)) world env =
      arrSliceValue (eval initial operand world env) first last bounds := by
  funext index
  exact eval_arraySpan operand initial world env first (last - first) _ index

/-- An index in a slice is shifted only after checking its relative
    range. The result is an ordinary index into the original array. -/
def shiftedSliceIndex {length first last : Nat} (bounds : SliceOk length first last)
    (index : Expr D Γ Λ (.index ((last - first : Nat) : Int))) : Expr D Γ Λ (.index length) := by
  have low : 0 ≤ (first : Int) + 0 := by omega
  have high : (first : Int) + (((last - first : Nat) : Int) - 1) ≤ (length : Int) - 1 := by
    have ordered := bounds.1
    have inside := bounds.2
    omega
  exact .widen low high (.add (.lit (first : Int)) index)

theorem eval_indexedArraySlice {τ : Ty} {length first last : Nat}
    (operand : Expr D Γ Λ (.arr τ length)) (bounds : SliceOk length first last)
    (index : Expr D Γ Λ (.index ((last - first : Nat) : Int)))
    (initial world : World D) (env : Env D Γ) :
    eval initial (.arrGet operand (shiftedSliceIndex bounds index)) world env =
      eval initial (.arrGet (arraySpan operand first (last - first) (by
        have ordered := bounds.1; have high := bounds.2; omega)) index) world env := by
  simp only [eval]
  rw [eval_arraySpan]
  apply congrArg (eval initial operand world env)
  apply Fin.ext
  have nonnegative := (eval initial index world env).lo_le
  simp only [shiftedSliceIndex, eval, Zahl.fin, Zahl.weiter, Zahl.add]
  omega

/-- Direct indexing reads the original array and the checked index once
    each, in their ordinary order. Both slice endpoints are constants. -/
theorem indexedSlice_reads {τ : Ty} {length first last : Nat}
    (operand : Expr D Γ Λ (.arr τ length)) (bounds : SliceOk length first last)
    (index : Expr D Γ Λ (.index ((last - first : Nat) : Int))) :
    (Expr.arrGet operand (shiftedSliceIndex bounds index)).orte =
      operand.orte ++ index.orte := by
  simp only [shiftedSliceIndex, Expr.orte, List.nil_append]

/-- Constant byte sequences can be folded. Runtime prefixes reuse
    ordinary string truncation after checking a minimum byte count. -/
def lowerSlice {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    (first last : Nat) : LowWert u Γ Λ → Except String (LowWert u Γ Λ)
  | ⟨.arr τ length, operand⟩ =>
    if bounds : SliceOk length first last then
      if last - first = 1 ∨ operand.orte.isEmpty = true then
        .ok ⟨.arr τ (last - first),
          arraySpan operand first (last - first) (by have ordered := bounds.1; have high := bounds.2; omega)⟩
      else .error "slice: bind the array to a local before slicing"
    else .error "slice: endpoint outside the array"
  | ⟨.str _, .strLit bytes _⟩ =>
    if bounds : SliceOk bytes.length first last then
      .ok ⟨.str (last - first), .strLit (sliceValue bytes first last)
        (Nat.le_of_eq (sliceValue_length bytes first last bounds))⟩
    else .error "slice: endpoint outside the string's bytes"
  | ⟨.str _, source⟩ =>
    if first = 0 ∧ last ≤ stringMinimum source then
      .ok ⟨.str last, .strWeit last source⟩
    else .error "slice: runtime string needs a certified prefix"
  | _ => .error "slice: expected an array or string value"

/-- A slice used directly as an index receiver avoids constructing the
    intermediate array. String indexing retains the ordinary behavior. -/
def lowerIndexedSlice {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    (first last : Nat) (base : LowWert u Γ Λ) (index : LowSide u Γ Λ) :
    Except String (LowWert u Γ Λ) :=
  match base with
  | ⟨.arr τ length, operand⟩ =>
    if bounds : SliceOk length first last then
      if low : 0 ≤ index.range.1 then
        if high : index.range.2 ≤ ((last - first : Nat) : Int) - 1 then
          .ok ⟨τ, .arrGet operand (shiftedSliceIndex bounds (.widen low high index.term))⟩
        else .error "slice: index outside the selected range"
      else .error "slice: index outside the selected range"
    else .error "slice: endpoint outside the array"
  | ⟨.str maximum, operand⟩ =>
    if SliceOk (stringMinimum operand) first last ∧
        0 ≤ index.range.1 ∧ index.range.2 < ((last - first : Nat) : Int) then
      .ok ⟨.int 0 255, stringSliceByte operand first index.term⟩
    else do idxW (← lowerSlice first last ⟨.str maximum, operand⟩) index
  | _ => .error "slice: expected an array or string value"

/-- The production reader returns the direct ordinary read for every
    statically certified byte access through a runtime string slice. -/
theorem lowerIndexedSlice_string {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    {maximum : Nat} (operand : Expr (declOf u) Γ Λ (.str maximum))
    (first last : Nat) (index : LowSide u Γ Λ)
    (bounds : SliceOk (stringMinimum operand) first last)
    (low : 0 ≤ index.range.1) (high : index.range.2 < ((last - first : Nat) : Int)) :
    lowerIndexedSlice first last (⟨.str maximum, operand⟩ : LowWert u Γ Λ) index =
      .ok ⟨.int 0 255, stringSliceByte operand first index.term⟩ := by
  simp only [lowerIndexedSlice, ite_eq_left (And.intro bounds (And.intro low high))]

theorem lowerSlice_concatPrefix {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    {n m last : Nat} (left : Expr (declOf u) Γ Λ (.str n))
    (right : Expr (declOf u) Γ Λ (.str m))
    (fits : last ≤ stringMinimum left + stringMinimum right) :
    lowerSlice 0 last (⟨.str (n + m), .strCat left right⟩ : LowWert u Γ Λ) =
      .ok ⟨.str last, .strWeit last (.strCat left right)⟩ := by
  simp only [lowerSlice, stringMinimum, fits, and_self]

theorem lowerIndexedSlice_array {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    {τ : Ty} {length : Nat} (operand : Expr (declOf u) Γ Λ (.arr τ length))
    (first last : Nat) (bounds : SliceOk length first last) (index : LowSide u Γ Λ)
    (low : 0 ≤ index.range.1) (high : index.range.2 ≤ ((last - first : Nat) : Int) - 1) :
    lowerIndexedSlice first last (⟨.arr τ length, operand⟩ : LowWert u Γ Λ) index =
      .ok ⟨τ, .arrGet operand (shiftedSliceIndex bounds (.widen low high index.term))⟩ := by
  simp only [lowerIndexedSlice, dite_eq_left bounds, dite_eq_left low, dite_eq_left high]

theorem lowerSlice_array {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    {τ : Ty} {length : Nat} (operand : Expr (declOf u) Γ Λ (.arr τ length))
    (first last : Nat) (bounds : SliceOk length first last)
    (allowed : last - first = 1 ∨ operand.orte.isEmpty = true) :
    lowerSlice first last (⟨.arr τ length, operand⟩ : LowWert u Γ Λ) =
      .ok ⟨.arr τ (last - first), arraySpan operand first (last - first)
        (by have ordered := bounds.1; have high := bounds.2; omega)⟩ := by
  simp only [lowerSlice, dite_eq_left bounds, ite_eq_left allowed]

theorem lowerSlice_string {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    (bytes : List (Zahl 0 255)) {maximum : Nat} (stored : bytes.length ≤ maximum)
    (first last : Nat) (bounds : SliceOk bytes.length first last) :
    lowerSlice first last (⟨.str maximum, .strLit bytes stored⟩ : LowWert u Γ Λ) =
      .ok ⟨.str (last - first), .strLit (sliceValue bytes first last)
        (Nat.le_of_eq (sliceValue_length bytes first last bounds))⟩ := by
  simp only [lowerSlice, dite_eq_left bounds]

theorem eval_stringSlice {maximum : Nat} (bytes : List (Zahl 0 255))
    (stored : bytes.length ≤ maximum) (first last : Nat)
    (bounds : SliceOk bytes.length first last) (initial world : World D) (env : Env D Γ) :
    eval initial (Expr.strLit (Λ := Λ) (sliceValue bytes first last)
      (Nat.le_of_eq (sliceValue_length bytes first last bounds))) world env =
      strSliceValue (⟨bytes, stored⟩ : Wert D (.str maximum)) first last bounds := by
  rw [eval]
  rfl

/-- The full-range view is inhabited at every length by every array value. -/
theorem arraySlice_erfuellbar {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    {τ : Ty} {length : Nat} (slot : Var Γ (.arr τ length)) :
    ∃ value : LowWert u Γ Λ,
      lowerSlice 0 length (⟨.arr τ length, .var slot⟩ : LowWert u Γ Λ) = .ok value ∧
      value.term.orte = [] ∧
      ∀ (initial world : World (declOf u)) (env : Env (declOf u) Γ),
        eval initial (arraySpan (Λ := Λ) (.var slot) 0 length (by omega)) world env = env.get slot := by
  have bounds : SliceOk length 0 length := ⟨Nat.zero_le _, Nat.le_refl _⟩
  have lexical : (Expr.var (D := declOf u) (Λ := Λ) slot).orte.isEmpty = true := rfl
  refine ⟨_, lowerSlice_array (.var slot) 0 length bounds (.inr lexical), ?_, ?_⟩
  · exact arraySpan_reads (.var slot) 0 _ _ (.inr lexical)
  intro initial world env
  funext index
  rw [eval_arraySpan]
  apply congrArg (env.get slot)
  exact Fin.ext (Nat.zero_add index.val)

end Gabbro.Grammatik.Parser.UebersetzeAllg
