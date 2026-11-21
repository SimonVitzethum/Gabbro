module

public import Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg

open Uebersetze

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
          by have upper := (eval initial start world env).le_hi; have valid := index.isLt; omega⟩
  | _, 0, _, index => index.elim0
  | offset, count + 1, bounds, index => by
    simp only [arraySpanFrom, eval, arrConsW]
    split
    · next first =>
      apply congrArg (eval initial base world env)
      apply Fin.ext
      simp only [Zahl.fin, Zahl.weiter, Zahl.add, first, Nat.cast_zero, Int.add_zero]
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
    {fn : UFn} {er : Option Ty} {array index : USide} {τ : Ty} {length : Nat} {lo hi : Int}
    {base : Expr (declOf u) Γ Λ (.arr τ length)} {start : Expr (declOf u) Γ Λ (.int lo hi)}
    (readArray : lowWertE u Γ Λ fn er array = .ok ⟨.arr τ length, base⟩)
    (readIndex : lowWertE u Γ Λ fn er index = .ok ⟨.int lo hi, start⟩)
    (nonnegative : 0 ≤ lo) (offset count : Nat) (bounds : hi + offset + count ≤ length) :
    lowWertE u Γ Λ fn er (uLocalArraySpan array index τ offset count) =
      .ok ⟨.arr τ count, arraySpanFrom base start nonnegative offset count bounds⟩ := by
  induction count generalizing offset with
  | zero => simp only [uLocalArraySpan, lowWertE, lowLit, Except.map, arraySpanFrom]
  | succ count ih =>
    have low : 0 ≤ lo + offset := by omega
    have high : hi + offset ≤ (length : Int) - 1 := by omega
    have head :
        lowWertE u Γ Λ fn er (.idx array (.add index (.lit offset))) =
          .ok ⟨τ, .arrGet base (.widen low high (.add start (.lit offset)))⟩ := by
      simp only [lowWertE, readArray, readIndex, LowSide.plus, LowSide.wert, zahlVon, LowWert.zahl,
        idxW, dite_eq_left low, dite_eq_left high]
    simp only [uLocalArraySpan, lowWertE, head, ih (offset + 1) (by omega), consW, fitW,
      dite_true, arraySpanFrom]

end Gabbro.Grammatik.Parser.UebersetzeAllg
