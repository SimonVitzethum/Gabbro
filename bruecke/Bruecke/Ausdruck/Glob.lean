module

public import Bruecke.Kodierung.Glob
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil3Values

@[expose] public section

/-! # The scalar Body reader extended with numeric static reads -/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

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

/-- The scalar extension preserves every successful slot-only read. -/
private theorem numericSideExprG_of_numericSideExpr (u : UProg) (fn : UFn) (s : USide) (e : Gabbro.Body.Expr)
    (h : numericSideExpr u fn s = some e) : numericSideExprG u fn s = some e := by
  match s, h with
  | .add a b, h =>
    exact binE_preserves_some _ _ _ _ _ (fun x hx => numericSideExprG_of_numericSideExpr u fn a x hx)
      (fun y hy => numericSideExprG_of_numericSideExpr u fn b y hy) e h
  | .sub a b, h =>
    exact binE_preserves_some _ _ _ _ _ (fun x hx => numericSideExprG_of_numericSideExpr u fn a x hx)
      (fun y hy => numericSideExprG_of_numericSideExpr u fn b y hy) e h
  | .mul a b, h =>
    exact binE_preserves_some _ _ _ _ _ (fun x hx => numericSideExprG_of_numericSideExpr u fn a x hx)
      (fun y hy => numericSideExprG_of_numericSideExpr u fn b y hy) e h
  | .band a b, h =>
    exact binE_preserves_some _ _ _ _ _ (fun x hx => numericSideExprG_of_numericSideExpr u fn a x hx)
      (fun y hy => numericSideExprG_of_numericSideExpr u fn b y hy) e h
  | .bor a b, h =>
    exact binE_preserves_some _ _ _ _ _ (fun x hx => numericSideExprG_of_numericSideExpr u fn a x hx)
      (fun y hy => numericSideExprG_of_numericSideExpr u fn b y hy) e h
  | .bxor a b, h =>
    exact binE_preserves_some _ _ _ _ _ (fun x hx => numericSideExprG_of_numericSideExpr u fn a x hx)
      (fun y hy => numericSideExprG_of_numericSideExpr u fn b y hy) e h
  | .conv _ _ a, h => exact numericSideExprG_of_numericSideExpr u fn a e h
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

private theorem map_preserves_some {α β : Type} (f : α → β) (a a' : Option α)
    (ha : ∀ x, a = some x → a' = some x) (b : β) (h : a.map f = some b) :
    a'.map f = some b := by
  cases a with
  | none => cases h
  | some x =>
      rw [ha x rfl]
      exact h

mutual
/-- Record structure is independent of the scalar reader's additional successful cases. -/
private theorem recordRead_preserves_some (u : UProg) (fn : UFn)
    (scalar scalar' : USide → Option Gabbro.Body.Expr)
    (hs : ∀ sd e, scalar sd = some e → scalar' sd = some e)
    (sd : USide) (out : Option Ty × Gabbro.Body.Expr)
    (h : recordRead u fn scalar sd = some out) :
    recordRead u fn scalar' sd = some out := by
  -- Keep the source constructor visible to the mutual termination checker.
  match sd, h with
  | .param p, h =>
      cases ht : valueParamTy fn p with
      | none =>
          simp only [recordRead, ht] at h ⊢
          exact map_preserves_some (none, ·) _ _ (hs _) out h
      | some ty => simpa only [recordRead, ht] using h
  | .truth _, h => simpa only [recordRead] using h
  | .product identity _ fields, h =>
      cases ht : (uRecordOf u.records (.prod identity (fields.map (·.1)))).toOption with
      | none => simp [recordRead, ht, bind, Option.bind] at h
      | some schema =>
          cases hr : recordReads u fn scalar fields with
          | none => simp [recordRead, ht, hr, bind, Option.bind] at h
          | some es =>
              have hr' := recordReads_preserves_some u fn scalar scalar' hs fields es hr
              simpa only [recordRead, ht, hr, hr', bind, Option.bind] using h
  | .field base name, h =>
      cases hr : recordRead u fn scalar base with
      | none => simp [recordRead, hr, bind, Option.bind] at h
      | some result =>
          have hr' := recordRead_preserves_some u fn scalar scalar' hs base result hr
          simpa only [recordRead, hr, hr', bind, Option.bind] using h
  | .replace base name value, h =>
      cases hr : recordRead u fn scalar base with
      | none => simp [recordRead, hr, bind, Option.bind] at h
      | some result =>
          have hr' := recordRead_preserves_some u fn scalar scalar' hs base result hr
          rcases result with ⟨tag, e⟩
          cases tag with
          | none => simp [recordRead, hr, bind, Option.bind] at h
          | some ty =>
              cases ht : (uRecordOf u.records ty).toOption with
              | none => simp [recordRead, hr, ht, bind, Option.bind] at h
              | some schema =>
                  cases hp : (uRecordPosition schema.val.fields name).toOption with
                  | none => simp [recordRead, hr, ht, hp, bind, Option.bind] at h
                  | some pos =>
                      cases hv : recordRead u fn scalar value with
                      | none => simp [recordRead, hr, ht, hp, hv, bind, Option.bind] at h
                      | some val =>
                          have hv' := recordRead_preserves_some u fn scalar scalar' hs value val hv
                          simpa only [recordRead, hr, hr', ht, hp, hv, hv', bind, Option.bind] using h
  | .lit _, h | .slot _ _ _, h | .tab _ _ _, h | .old _ _ _, h | .glob _, h | .erg, h
  | .add _ _, h | .sub _ _, h | .mul _ _, h | .conv _ _ _, h
  | .band _ _, h | .bor _ _, h | .bxor _ _, h | .div _ _, h | .rem _ _, h
  | .shl _ _, h | .shr _ _, h | .neg _, h | .refSlot _ _, h | .idx _ _, h | .len _, h
  | .text _, h | .arrNil, h | .arrCons _ _, h | .upd _ _ _, h | .typed _ _, h
  | .eng _ _ _, h | .ib1 _ _ _, h | .ib2 _ _ _ _, h | .zaehle _ _ _, h
  | .zaehleBaum _ _ _ _ _ _, h | .zaehleFeld _ _ _, h | .taggedEmpty _ _, h
  | .taggedValue _ _ _, h | .predicate _, h | .option _ _, h | .absent _, h
  | .present _ _, h | .reason _ _, h | .function _ _, h =>
      simp only [recordRead] at h ⊢
      exact map_preserves_some (none, ·) _ _ (hs _) out h
termination_by 3 * sizeOf sd
decreasing_by all_goals (simp_wf <;> omega)

private theorem recordReads_preserves_some (u : UProg) (fn : UFn)
    (scalar scalar' : USide → Option Gabbro.Body.Expr)
    (hs : ∀ sd e, scalar sd = some e → scalar' sd = some e)
    (fields : List (Ty × USide)) (es : List Gabbro.Body.Expr)
    (h : recordReads u fn scalar fields = some es) :
    recordReads u fn scalar' fields = some es := by
  match fields, h with
  | [], h => simpa only [recordReads] using h
  | (_, sd) :: rest, h =>
      cases hr : recordRead u fn scalar sd with
      | none => simp [recordReads, hr, bind, Option.bind] at h
      | some result =>
          rcases result with ⟨tag, e⟩
          have hr' := recordRead_preserves_some u fn scalar scalar' hs sd (tag, e) hr
          cases ht : recordReads u fn scalar rest with
          | none => simp [recordReads, hr, ht, bind, Option.bind] at h
          | some tail =>
              have ht' := recordReads_preserves_some u fn scalar scalar' hs rest tail ht
              simpa only [recordReads, hr, hr', ht, ht', bind, Option.bind] using h
termination_by 3 * sizeOf fields + 1
decreasing_by all_goals (simp_wf <;> omega)
end

/-- Every expression already read by the slot-only bridge keeps exactly its Body form. -/
theorem sideExprG_of_sideExpr (u : UProg) (fn : UFn) (s : USide) (e : Gabbro.Body.Expr)
    (h : sideExpr u fn s = some e) : sideExprG u fn s = some e := by
  unfold sideExpr at h
  unfold sideExprG
  exact map_preserves_some (·.2) _ _
    (recordRead_preserves_some u fn _ _ (numericSideExprG_of_numericSideExpr u fn) s) e h

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

#print axioms lowGlobRead_sim

end Gabbro.Bruecke
