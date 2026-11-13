module

public import Bruecke.Kodierung.Glob
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil3Values

@[expose] public section

/-! # The scalar Body reader extended with numeric static reads -/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

/-- `sideExpr` with static reads, including statics nested inside its arithmetic forms.
    The unchanged reader handles every nonrecursive form other than `.glob`. -/
def sideExprG (u : UProg) (fn : UFn) : USide → Option Gabbro.Body.Expr
  | .glob g => some (.global g)
  | .add a b => binE .add (sideExprG u fn a) (sideExprG u fn b)
  | .sub a b => binE .sub (sideExprG u fn a) (sideExprG u fn b)
  | .mul a b => binE .mul (sideExprG u fn a) (sideExprG u fn b)
  | .conv _ _ a => sideExprG u fn a
  | .band a b => binE .band (sideExprG u fn a) (sideExprG u fn b)
  | .bor a b => binE .bor (sideExprG u fn a) (sideExprG u fn b)
  | .bxor a b => binE .bxor (sideExprG u fn a) (sideExprG u fn b)
  | s => sideExpr u fn s

/-- Preserving successful operands preserves their binary expression. -/
theorem binE_preserves_some (op : Gabbro.Body.BinOp)
    (a b a' b' : Option Gabbro.Body.Expr)
    (ha : ∀ e, a = some e → a' = some e) (hb : ∀ e, b = some e → b' = some e)
    (e : Gabbro.Body.Expr) (h : binE op a b = some e) : binE op a' b' = some e := by
  cases a with
  | none => cases b <;> cases h
  | some x =>
    cases b with
    | none => cases h
    | some y =>
      rw [ha x rfl, hb y rfl]
      exact h

/-- Every expression already read by the slot-only bridge keeps exactly its Body form. -/
theorem sideExprG_of_sideExpr (u : UProg) (fn : UFn) (s : USide) (e : Gabbro.Body.Expr)
    (h : sideExpr u fn s = some e) : sideExprG u fn s = some e := by
  match s, h with
  | .add a b, h =>
    exact binE_preserves_some _ _ _ _ _ (fun x hx => sideExprG_of_sideExpr u fn a x hx)
      (fun y hy => sideExprG_of_sideExpr u fn b y hy) e h
  | .sub a b, h =>
    exact binE_preserves_some _ _ _ _ _ (fun x hx => sideExprG_of_sideExpr u fn a x hx)
      (fun y hy => sideExprG_of_sideExpr u fn b y hy) e h
  | .mul a b, h =>
    exact binE_preserves_some _ _ _ _ _ (fun x hx => sideExprG_of_sideExpr u fn a x hx)
      (fun y hy => sideExprG_of_sideExpr u fn b y hy) e h
  | .band a b, h =>
    exact binE_preserves_some _ _ _ _ _ (fun x hx => sideExprG_of_sideExpr u fn a x hx)
      (fun y hy => sideExprG_of_sideExpr u fn b y hy) e h
  | .bor a b, h =>
    exact binE_preserves_some _ _ _ _ _ (fun x hx => sideExprG_of_sideExpr u fn a x hx)
      (fun y hy => sideExprG_of_sideExpr u fn b y hy) e h
  | .bxor a b, h =>
    exact binE_preserves_some _ _ _ _ _ (fun x hx => sideExprG_of_sideExpr u fn a x hx)
      (fun y hy => sideExprG_of_sideExpr u fn b y hy) e h
  | .conv _ _ a, h => exact sideExprG_of_sideExpr u fn a e h
  | .glob _, h => cases h
  | .lit _, h | .param _, h | .slot _ _ _, h | .tab _ _ _, h | .old _ _ _, h | .erg, h
  | .div _ _, h | .rem _ _, h | .shl _ _, h | .shr _ _, h | .neg _, h | .refSlot _ _, h
  | .idx _ _, h | .len _, h | .text _, h | .arrNil, h | .arrCons _ _, h | .upd _ _ _, h
  | .typed _ _, h | .eng _ _ _, h | .ib1 _ _ _, h | .ib2 _ _ _ _, h | .zaehle _ _ _, h
  | .zaehleBaum _ _ _ _ _ _, h | .zaehleFeld _ _ _, h | .product _ _ _, h | .field _ _, h
  | .replace _ _ _, h | .truth _, h | .taggedEmpty _ _, h | .taggedValue _ _ _, h
  | .predicate _, h | .option _ _, h | .absent _, h | .present _ _, h | .reason _ _, h
  | .function _ _, h => exact h
termination_by sizeOf s
decreasing_by all_goals (simp_wf; omega)

/-- The static analogue of `lowTabRead_sim`. There is no index expression or parameter
    lookup, so neither `fn`, `sh` nor `LRel` is needed. Guard possession is already a
    premise of a successful `lowGlobSide`, just as it is for `lowTabRead`. -/
theorem lowGlobRead_sim {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    {g : String} {ls : LowSide u Γ Λ} (h : lowGlobSide u Γ Λ g = .ok ls)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (w : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hG : GRel u σ w) :
    Gabbro.Body.eval ⟨w, β⟩ (.global g) =
      some (valOf (.int ls.range.1 ls.range.2) (eval σ₀ ls.term σ ρ)) := by
  have resolved : ∃ (i : Fin u.globs.length), globIdx u.globs g = .ok i ∧
      (globAt u i).ty = .int ls.range.1 ls.range.2 ∧
      ∃ hd : ∀ guard ∈ (declOf u).gbraucht i, Res.von (declOf u) guard ∈ Λ,
        HEq ls.term (Expr.glob (D := declOf u) (Γ := Γ) i hd) := by
    unfold lowGlobSide at h
    split at h
    · cases h
    · rename_i i hi
      split at h
      · rename_i hd
        split at h
        · rename_i lo hi' ht
          cases h
          refine ⟨i, hi, ht, hd, ?_⟩
          dsimp only
          exact mpr_heq _ _
        · cases h
        · cases h
      · cases h
  obtain ⟨i, hi, ht, hd, he⟩ := resolved
  have hty : (declOf u).gtyp i = .int ls.range.1 ls.range.2 := by
    show (globAt u i).ty.toTy = _
    rw [ht]
    rfl
  change some (w (.global g)) = _
  rw [grel_lies u hG g i hi ls.range.1 ls.range.2 ht]
  exact congrArg some (valOf_eval_heq hty.symm ls.term
    (Expr.glob (D := declOf u) i hd) he σ₀ σ ρ).symm

end Gabbro.Bruecke
