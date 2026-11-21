module

public import Grammatik.Parser.Elab.UebersetzeAllg.Teil3Values
public import Grammatik.Niedrig.Konstrukte.Schnitt
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

/-- Constant byte sequences are sliced by their actual length. A runtime
    string needs a separate certified lower bound on its length. -/
def lowerSlice {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    (first last : Nat) : LowWert u Γ Λ → Except String (LowWert u Γ Λ)
  | ⟨.arr τ length, operand⟩ =>
    if bounds : SliceOk length first last then
      .ok ⟨.arr τ (last - first),
        arraySpan operand first (last - first) (by have ordered := bounds.1; have high := bounds.2; omega)⟩
    else .error "slice: endpoint outside the array"
  | ⟨.str _, .strLit bytes _⟩ =>
    if bounds : SliceOk bytes.length first last then
      .ok ⟨.str (last - first), .strLit (sliceValue bytes first last)
        (Nat.le_of_eq (sliceValue_length bytes first last bounds))⟩
    else .error "slice: endpoint outside the string's bytes"
  | ⟨.str _, _⟩ => .error "slice: runtime string length is not certified"
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
  | other => do idxW (← lowerSlice first last other) index

theorem lowerSlice_array {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    {τ : Ty} {length : Nat} (operand : Expr (declOf u) Γ Λ (.arr τ length))
    (first last : Nat) (bounds : SliceOk length first last) :
    lowerSlice first last (⟨.arr τ length, operand⟩ : LowWert u Γ Λ) =
      .ok ⟨.arr τ (last - first), arraySpan operand first (last - first)
        (by have ordered := bounds.1; have high := bounds.2; omega)⟩ := by
  simp only [lowerSlice, dite_eq_left bounds]

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
theorem arraySlice_erfuellbar {τ : Ty} {length : Nat} (operand : Expr D Γ Λ (.arr τ length))
    (initial world : World D) (env : Env D Γ) :
    eval initial (arraySpan operand 0 length (by omega)) world env =
      eval initial operand world env := by
  funext index
  rw [eval_arraySpan]
  apply congrArg (eval initial operand world env)
  exact Fin.ext (Nat.zero_add index.val)

end Gabbro.Grammatik.Parser.UebersetzeAllg
