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
  simp only [lowWertE, readFirst, readLast, zahlVon, LowSide.minus, LowSide.wert]

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

end Gabbro.Grammatik.Parser.UebersetzeAllg
