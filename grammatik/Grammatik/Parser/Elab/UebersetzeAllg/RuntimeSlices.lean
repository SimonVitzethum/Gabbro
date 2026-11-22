module

public import Grammatik.Parser.Elab.UebersetzeAllg.Teil5
public import Grammatik.Niedrig.Konstrukte.Schnitt
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg

open Uebersetze
open LowLevel.Construct

variable {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}

/-- Build a fixed-length subarray at a runtime index using ordinary
    checked array reads. The whole start interval and every offset fit. -/
def arraySpanFrom {τ : Ty} {length : Nat} {lo hi : Int}
    (base : Expr D Γ Λ (.arr τ length)) (start : Expr D Γ Λ (.int lo hi))
    (nonnegative : 0 ≤ lo) : (offset count : Nat) →
    hi + offset + count ≤ length → Expr D Γ Λ (.arr τ count)
  | _, 0, _ => .arrNil
  | offset, count + 1, inside =>
    .arrCons (.arrGet base (.widen (by omega) (by omega) (.add start (.lit offset))))
      (arraySpanFrom base start nonnegative (offset + 1) count (by omega))
termination_by structural _ count _ => count

/-- Expanding local reads neither introduces nor repeats a carrier
    observation. The production source form requires both operands local. -/
theorem arraySpanFrom_reads {τ : Ty} {length : Nat} {lo hi : Int}
    (base : Expr D Γ Λ (.arr τ length)) (start : Expr D Γ Λ (.int lo hi))
    (nonnegative : 0 ≤ lo) (baseLocal : base.orte = []) (startLocal : start.orte = [])
    (offset count : Nat) (bounds : hi + offset + count ≤ length) :
    (arraySpanFrom base start nonnegative offset count bounds).orte = [] := by
  induction count generalizing offset with
  | zero => rfl
  | succ count ih =>
    simp only [arraySpanFrom, Expr.orte, baseLocal, startLocal, List.nil_append,
      ih (offset + 1) (by omega)]

/-- The ordinary core term reads exactly the translated array position
    for every index of the materialized slice and every environment. -/
theorem eval_arraySpanFrom {τ : Ty} {length : Nat} {lo hi : Int}
    (base : Expr D Γ Λ (.arr τ length)) (start : Expr D Γ Λ (.int lo hi))
    (nonnegative : 0 ≤ lo) (initial world : World D) (env : Env D Γ) :
    ∀ (offset count : Nat) (bounds : hi + offset + count ≤ length) (index : Fin count),
      eval initial (arraySpanFrom base start nonnegative offset count bounds) world env index =
        eval initial base world env ⟨((eval initial start world env).n + offset + index.val).toNat,
          by
            have lower := (eval initial start world env).lo_le
            have upper := (eval initial start world env).le_hi
            have valid := index.isLt
            omega⟩
  | _, 0, _, index => index.elim0
  | offset, count + 1, bounds, index => by
    simp only [arraySpanFrom, eval, arrConsW]
    split
    · next first =>
      apply congrArg (eval initial base world env)
      apply Fin.ext
      simp [Zahl.fin, Zahl.weiter, Zahl.add, first]
    · next later =>
      rw [eval_arraySpanFrom base start nonnegative initial world env (offset + 1) count
        (by omega) ⟨index.val - 1, by omega⟩]
      apply congrArg (eval initial base world env)
      apply Fin.ext
      simp only
      omega

/-- The actual source expansion lowers to the same typed core term.
    Each indexed read is performed by the ordinary dependent reader. -/
theorem lowWertE_localArraySpan {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    {fn : UFn} {er : Option Ty} {array index : String} {τ : Ty} {length : Nat} {lo hi : Int}
    {base : Expr (declOf u) Γ Λ (.arr τ length)} {start : Expr (declOf u) Γ Λ (.int lo hi)}
    (readArray : lowWertE u Γ Λ fn er (.param array) = .ok ⟨.arr τ length, base⟩)
    (readIndex : lowWertE u Γ Λ fn er (.param index) = .ok ⟨.int lo hi, start⟩)
    (nonnegative : 0 ≤ lo) (offset count : Nat) (bounds : hi + offset + count ≤ length) :
    lowWertE u Γ Λ fn er (uLocalArraySpan (.param array) (.param index) τ offset count) =
      .ok ⟨.arr τ count, arraySpanFrom base start nonnegative offset count bounds⟩ := by
  induction count generalizing offset with
  | zero => simp only [uLocalArraySpan, lowWertE, lowLit, Except.map, arraySpanFrom]
  | succ count ih =>
    have low : 0 ≤ lo + offset := by omega
    have high : hi + offset ≤ (length : Int) - 1 := by omega
    have head :
        lowWertE u Γ Λ fn er (.idx (.param array) (.add (.param index) (.lit offset))) =
          .ok ⟨τ, .arrGet base (.widen low high (.add start (.lit offset)))⟩ := by
      simp only [lowWertE, readArray, readIndex, LowSide.plus, LowSide.wert, zahlVon, LowWert.zahl,
        idxW, dite_eq_left low, dite_eq_left high]
    simp only [uLocalArraySpan, lowWertE, head, ih (offset + 1) (by omega), consW, fitW,
      dite_true, arraySpanFrom]

/-- The actual core lowering of a runtime slice length is integer
    subtraction in the direction of the half-open range. -/
theorem lowWertE_localArraySliceLength {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    {fn : UFn} {er : Option Ty} {first last : String} {firstLo firstHi lastLo lastHi : Int}
    {begin : Expr (declOf u) Γ Λ (.int firstLo firstHi)}
    {finish : Expr (declOf u) Γ Λ (.int lastLo lastHi)}
    (readFirst : lowWertE u Γ Λ fn er (.param first) = .ok ⟨.int firstLo firstHi, begin⟩)
    (readLast : lowWertE u Γ Λ fn er (.param last) = .ok ⟨.int lastLo lastHi, finish⟩) :
    lowWertE u Γ Λ fn er (.sub (.param last) (.param first)) =
      .ok ⟨.int (lastLo - firstHi) (lastHi - firstLo), .sub finish begin⟩ := by
  simp only [lowWertE, readFirst, readLast, zahlVon, LowWert.zahl, LowSide.minus, LowSide.wert]

/-- Interval checking suffices for all runtime endpoints. The generated
    subtraction returns the exact length of the model slice. -/
theorem eval_localArraySliceLength {τ : Ty} {capacity : Nat} {firstLo firstHi lastLo lastHi : Int}
    (array : Wert D (.arr τ capacity)) (begin : Expr D Γ Λ (.int firstLo firstHi))
    (finish : Expr D Γ Λ (.int lastLo lastHi))
    (ranges : 0 ≤ firstLo ∧ firstHi ≤ lastLo ∧ lastHi ≤ capacity)
    (initial world : World D) (env : Env D Γ) :
    ∃ bounds : SliceOk capacity (eval initial begin world env).n.toNat (eval initial finish world env).n.toNat,
      (eval initial (.sub finish begin) world env).n =
        ((BoundedSlice.ofArray array (eval initial begin world env).n.toNat
          (eval initial finish world env).n.toNat bounds).length : Int) := by
  obtain ⟨nonnegative, ordered, within⟩ := ranges
  have lo := (eval initial begin world env).lo_le
  have hi := (eval initial begin world env).le_hi
  have lo' := (eval initial finish world env).lo_le
  have hi' := (eval initial finish world env).le_hi
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  change (eval initial finish world env).n - (eval initial begin world env).n =
    (((eval initial finish world env).n.toNat - (eval initial begin world env).n.toNat : Nat) : Int)
  omega

/-- The projected source index lowers to one read of the original array. -/
theorem localArraySliceIndex_erfuellbar (ctx : UCtx) (blatt : SExpr → Except String USide)
    (array first last index : String) (τ : Ty) (capacity : Nat)
    (firstLo firstHi lastLo lastHi indexLo indexHi : Int)
    (arrayType : uSliceLocalType ctx array = some (.arr τ capacity))
    (firstType : uSliceLocalType ctx first = some (.int firstLo firstHi))
    (lastType : uSliceLocalType ctx last = some (.int lastLo lastHi))
    (indexType : uSliceLocalType ctx index = some (.int indexLo indexHi))
    (bounds : 0 ≤ firstLo ∧ firstHi ≤ lastLo ∧ lastHi ≤ capacity)
    (locals : blatt (.variable array) = .ok (.param array) ∧
      blatt (.variable first) = .ok (.param first) ∧ blatt (.variable last) = .ok (.param last))
    (indexBounds : 0 ≤ indexLo ∧ indexHi < lastLo - firstHi ∧
      blatt (.variable index) = .ok (.param index)) :
    uRechne ctx blatt (.index (.built "#slice" [.variable array, .variable first, .variable last])
      (.variable index)) = .ok (.idx (.param array) (.add (.param first) (.param index))) := by
  rw [uRechne]
  simp only [uLocalArraySliceObservation, arrayType, firstType, lastType, indexType, bounds,
    locals, indexBounds, and_self, ite_true]

theorem lowWertE_localArraySliceIndex {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    {fn : UFn} {er : Option Ty} {array first index : String} {τ : Ty} {capacity : Nat}
    {firstLo firstHi indexLo indexHi : Int}
    {base : Expr (declOf u) Γ Λ (.arr τ capacity)}
    {begin : Expr (declOf u) Γ Λ (.int firstLo firstHi)}
    {position : Expr (declOf u) Γ Λ (.int indexLo indexHi)}
    (readArray : lowWertE u Γ Λ fn er (.param array) = .ok ⟨.arr τ capacity, base⟩)
    (readFirst : lowWertE u Γ Λ fn er (.param first) = .ok ⟨.int firstLo firstHi, begin⟩)
    (readIndex : lowWertE u Γ Λ fn er (.param index) = .ok ⟨.int indexLo indexHi, position⟩)
    (lower : 0 ≤ firstLo + indexLo) (upper : firstHi + indexHi ≤ (capacity : Int) - 1) :
    lowWertE u Γ Λ fn er (.idx (.param array) (.add (.param first) (.param index))) =
      .ok ⟨τ, .arrGet base (.widen lower upper (.add begin position))⟩ := by
  simp only [lowWertE, readArray, readFirst, readIndex, LowSide.plus, LowSide.wert,
    zahlVon, LowWert.zahl, idxW, dite_eq_left lower, dite_eq_left upper]

/-- For every model run, the original-array read returns the selected
    element of the half-open slice. The endpoint and index ranges prove
    all translated addresses valid without any runtime storage. -/
theorem eval_localArraySliceIndex {τ : Ty} {capacity : Nat}
    {firstLo firstHi lastLo lastHi indexLo indexHi : Int}
    (base : Expr D Γ Λ (.arr τ capacity)) (begin : Expr D Γ Λ (.int firstLo firstHi))
    (finish : Expr D Γ Λ (.int lastLo lastHi)) (position : Expr D Γ Λ (.int indexLo indexHi))
    (bounds : 0 ≤ firstLo ∧ firstHi ≤ lastLo ∧ lastHi ≤ capacity)
    (indexBounds : 0 ≤ indexLo ∧ indexHi < lastLo - firstHi)
    (initial world : World D) (env : Env D Γ) :
    let first := eval initial begin world env
    let last := eval initial finish world env
    let index := eval initial position world env
    ∃ valid : SliceOk capacity first.n.toNat last.n.toNat,
      ∃ inside : index.n.toNat < last.n.toNat - first.n.toNat,
        eval initial (.arrGet base (.widen (by omega)
          (by have low := last.lo_le; have high := last.le_hi; omega) (.add begin position))) world env =
          (BoundedSlice.ofArray (eval initial base world env) first.n.toNat last.n.toNat valid).get
            ⟨index.n.toNat, inside⟩ := by
  dsimp only
  have firstLo := (eval initial begin world env).lo_le
  have firstHi := (eval initial begin world env).le_hi
  have lastLo := (eval initial finish world env).lo_le
  have lastHi := (eval initial finish world env).le_hi
  have indexLo := (eval initial position world env).lo_le
  have indexHi := (eval initial position world env).le_hi
  refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
  simp only [eval, BoundedSlice.ofArray, arrSliceValue]
  apply congrArg (eval initial base world env)
  apply Fin.ext
  simp only [Zahl.fin, Zahl.weiter, Zahl.add]
  omega

end Gabbro.Grammatik.Parser.UebersetzeAllg
