module

public import Grammatik.Parser.Elab.UebersetzeAllg.Teil3Values
public import Grammatik.Niedrig.Konstrukte.Schnitt
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg

open Gabbro.Grammatik.LowLevel.Construct

variable {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}

/-- Guaranteed bytes, independent of the contents of local variables and
    memory. In particular a string's declared maximum is never a minimum. -/
def stringMinimum : {maximum : Nat} → Expr D Γ Λ (.str maximum) → Nat
  | _, .strLit bytes _ => bytes.length
  | _, .strCat left right => stringMinimum left + stringMinimum right
  | _, .strWeit maximum source => min maximum (stringMinimum source)
  | _, .wenn _ left right => min (stringMinimum left) (stringMinimum right)
  | _, _ => 0

theorem stringMinimum_sound (initial world : World D) (env : Env D Γ) :
    ∀ {maximum : Nat} (source : Expr D Γ Λ (.str maximum)),
      stringMinimum source ≤ (eval initial source world env).1.length
  | _, .strLit _ _ => Nat.le_refl _
  | _, .strCat left right => by
    simp only [stringMinimum, eval, strCatW, List.length_append]
    exact Nat.add_le_add (stringMinimum_sound initial world env left)
      (stringMinimum_sound initial world env right)
  | _, .strWeit maximum source => by
    simp only [stringMinimum, eval, strWeitW, List.length_take]
    exact Nat.min_le_min (Nat.le_refl maximum) (stringMinimum_sound initial world env source)
  | _, .wenn _ left right => by
    simp only [stringMinimum, eval]
    split
    · exact (Nat.min_le_left _ _).trans (stringMinimum_sound initial world env left)
    · exact (Nat.min_le_right _ _).trans (stringMinimum_sound initial world env right)
  | _, _ => Nat.zero_le _

theorem stringSlice_bounds {maximum : Nat} (source : Expr D Γ Λ (.str maximum))
    {first last : Nat} (bounds : SliceOk (stringMinimum source) first last)
    (initial world : World D) (env : Env D Γ) :
    SliceOk (eval initial source world env).1.length first last :=
  ⟨bounds.1, bounds.2.trans (stringMinimum_sound initial world env source)⟩

/-- Prefix extraction reuses G's typed string truncation, which the
    ordinary Stage-0 lowering already proves through its string layout. -/
theorem stringPrefix_refines {maximum last : Nat} (source : Expr D Γ Λ (.str maximum))
    (bounds : SliceOk (stringMinimum source) 0 last)
    (initial world : World D) (env : Env D Γ) :
    eval initial (.strWeit last source) world env =
      (strSliceStep (eval initial source world env) 0 last
        (stringSlice_bounds source bounds initial world env) world).value := by
  apply Subtype.ext
  simp only [eval, strWeitW, strSliceStep, valueStep, strSliceValue, sliceValue,
    List.drop_zero, Nat.sub_zero]

theorem stringPrefix_reads {maximum last : Nat} (source : Expr D Γ Λ (.str maximum)) :
    (Expr.strWeit last source).orte = source.orte := rfl

/-- A byte inside a checked slice is the byte at the translated index
    in the original string, for every runtime byte sequence. -/
theorem stringSliceByte_value {maximum first last : Nat} (value : Wert D (.str maximum))
    (bounds : SliceOk value.1.length first last) (index : Int) (low : 0 ≤ index)
    (high : index < ((last - first : Nat) : Int)) :
    strGetW (strSliceValue value first last bounds) index =
      strGetW value ((first : Int) + index) := by
  have shifted : 0 ≤ (first : Int) + index := by omega
  have relative : index.toNat < last - first := by omega
  have absolute : ((first : Int) + index).toNat = first + index.toNat := by omega
  simp only [strGetW, if_pos low, if_pos shifted, strSliceValue, sliceValue,
    List.getElem?_take_of_lt relative, List.getElem?_drop, absolute]

def stringSliceByte {maximum : Nat} {lo hi : Int} (source : Expr D Γ Λ (.str maximum))
    (first : Nat) (index : Expr D Γ Λ (.int lo hi)) : Expr D Γ Λ (.int 0 255) :=
  .strGet source (.add (.lit (first : Int)) index)

theorem stringSliceByte_refines {maximum first last : Nat} {lo hi : Int}
    (source : Expr D Γ Λ (.str maximum)) (index : Expr D Γ Λ (.int lo hi))
    (bounds : SliceOk (stringMinimum source) first last)
    (low : 0 ≤ lo) (high : hi < ((last - first : Nat) : Int))
    (initial world : World D) (env : Env D Γ) :
    eval initial (stringSliceByte source first index) world env =
      strGetW (strSliceValue (eval initial source world env) first last
        (stringSlice_bounds source bounds initial world env)) (eval initial index world env).n := by
  have read := eval initial index world env
  exact (stringSliceByte_value (eval initial source world env)
    (stringSlice_bounds source bounds initial world env) read.n
      (low.trans read.lo_le) (lt_of_le_of_lt read.le_hi high)).symm

theorem stringSliceByte_reads {maximum : Nat} {lo hi : Int} (source : Expr D Γ Λ (.str maximum))
    (first : Nat) (index : Expr D Γ Λ (.int lo hi)) :
    (stringSliceByte source first index).orte = source.orte ++ index.orte := by
  simp only [stringSliceByte, Expr.orte, List.nil_append]

end Gabbro.Grammatik.Parser.UebersetzeAllg
