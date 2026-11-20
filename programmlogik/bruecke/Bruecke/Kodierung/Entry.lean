module
public import Bruecke.Kodierung.Records
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik

theorem nthVal_typed {D : Deklaration} : ∀ {Γ : Ctx} (ρ : Env D Γ) (j : Nat) (ty : Ty),
    Γ[j]? = some ty → ∃ v : Wert D ty, nthVal ρ j = valOf ty v
  | _, .nil, _, _, h => by cases h
  | _, .cons v ρ, 0, ty, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst ty
    exact ⟨v, rfl⟩
  | _, .cons v ρ, j + 1, ty, h => nthVal_typed ρ j ty h

theorem reasonCheck_eval (β : Gabbro.Body.Binding) (w : Gabbro.Body.World) (x : String) :
    ∀ labels, Gabbro.Body.eval ⟨w, β⟩ (reasonCheck x labels) =
      some (.bool (labels.any (fun tag => decide (β x = .reason tag))))
  | [] => rfl
  | tag :: labels => by
    simp only [reasonCheck, Gabbro.Body.eval, reasonCheck_eval β w x labels,
      Gabbro.Body.binop, List.any_cons, Gabbro.Body.orBool_some]

theorem entryCheck_wahr {D : Deklaration} (x : String) (ty : Ty) (v : Wert D ty)
    (β : Gabbro.Body.Binding) (w : Gabbro.Body.World) {e : Gabbro.Body.Expr}
    (hv : β x = valOf ty v) (he : entryCheck x ty = some e) :
    Gabbro.Body.eval ⟨w, β⟩ e = some (.bool true) := by
  cases ty with
  | why n =>
    simp only [entryCheck, Option.some.injEq] at he
    subst e
    rw [reasonCheck_eval]
    have hm : caseLabel v.val ∈ (List.range n).map caseLabel :=
      List.mem_map.mpr ⟨v.val, List.mem_range.mpr v.isLt, rfl⟩
    have hh : ((List.range n).map caseLabel).any (fun tag => decide (β x = .reason tag)) = true := by
      apply List.any_eq_true.mpr
      exact ⟨caseLabel v.val, hm, by rw [decide_eq_true_eq, hv]; rfl⟩
    rw [hh]
  | _ =>
    simp only [entryCheck] at he
    cases hs : entryShapeOfTy _ with
    | none => rw [hs] at he; cases he
    | some sh =>
      rw [hs] at he
      cases he
      simp only [Gabbro.Body.eval, hv, valOf_entryShape _ v sh hs]

end Gabbro.Bruecke
