module
public import Bruecke.Ausdruck.Teil1
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg}

/-- The optional-index encoding commutes with the canonical source lowerer. The bound
    remains in G's `Zahl`; Body retains exactly absence or its checked index. -/
theorem lowOpt_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {sh : Nat}
    {num : Nat} {hn : num < u.tabs.length} {v : UOpt}
    {ev : Expr (declOf u) Γ Λ (.opt ((declOf u).count ⟨num, hn⟩))}
    {e : Gabbro.Body.Expr}
    (h : lowOpt u Γ Λ fn sh num hn v = .ok ev) (hb : optionExpr u fn v = some e)
    (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WRel u σ s.world) (hL : LRel fn sh ρ s.local') :
    Gabbro.Body.eval s e = some (valOf (.opt ((declOf u).count ⟨num, hn⟩)) (eval σ₀ ev σ ρ)) := by
  cases v with
  | nichts => cases h; cases hb; rfl
  | etwas ix =>
    simp only [lowOpt] at h
    cases hi : lowIdx u Γ Λ fn sh ⟨num, hn⟩ ix with
    | error err => rw [hi] at h; cases h
    | ok ei =>
      rw [hi] at h
      cases h
      cases hb
      simp only [Gabbro.Body.eval, lowIdx_sim hi σ₀ σ ρ s.world s.local' hL]
      rfl
  | var x =>
    cases hb
    simp only [lowOpt] at h
    split at h
    · cases h
    · rename_i j hj
      split at h
      · rename_i m hm
        split at h
        · split at h
          · cases h
          · rename_i var hv
            cases h
            simp only [Gabbro.Body.eval]
            rw [hL x j hj, nthVal_lowVar Γ (sh + j) _ var ρ hv]
            rfl
        · cases h
      · cases h
  | tab t fld ix =>
    cases hb
    simp only [lowOpt] at h
    split at h
    · cases h
    · rename_i t' ht
      split at h
      · cases h
      · rename_i oh ho
        split at h
        · rename_i same
          split at h
          · cases h
          · rename_i i hi
            split at h
            · rename_i held
              cases h
              simp only [Gabbro.Body.eval]
              rw [lowIdx_sim hi σ₀ σ ρ s.world s.local' hL]
              simp only
              rw [wrel_lies_index u hW t t' ht fld oh.idx (fieldIndex_opt ho)]
              have hcast : HEq (slotTermO u Γ Λ t' oh i held)
                  (Expr.slot (D := declOf u) t' oh.idx i held) := by
                unfold slotTermO
                exact mpr_heq _ _
              apply congrArg some
              symm
              exact valOf_eval_heq ((congrArg Ty.opt same).symm.trans oh.hopt.symm) _ _
                ((mpr_heq _ _).trans hcast) σ₀ σ ρ
            · cases h
        · cases h
  | slot p fld ix =>
    simp only [lowOpt] at h
    split at h
    · cases h
    · rename_i j hj
      split at h
      · rename_i space wr pnum hp
        split at h
        · rename_i hlt
          split at h
          · cases h
          · rename_i oh ho
            split at h
            · rename_i same
              split at h
              · cases h
              · rename_i pv hpv
                split at h
                · cases h
                · rename_i i hi
                  split at h
                  · rename_i held
                    cases hc : checkedTableCap u space pnum hlt with
                    | error err => simp [hc, bind, Except.bind] at h
                    | ok cap =>
                      cases hparam : checkedPointerParam fn j
                          ⟨space, ⟨true, wr, none⟩, .table pnum⟩ with
                      | error err => simp [hc, hparam, bind, Except.bind] at h
                      | ok parameter =>
                        simp only [hc, hparam, bind, Except.bind, pure, Except.pure] at h
                        cases h
                        have hpt := ptrTab_of_type fn p j pnum true wr hj parameter.down.2 hlt
                        simp only [optionExpr, hpt, Option.map_some, Option.some.injEq] at hb
                        subst e
                        simp only [Gabbro.Body.eval]
                        rw [lowIdx_sim hi σ₀ σ ρ s.world s.local' hL]
                        simp only
                        rw [wrel_lies_index u hW _ ⟨pnum, hlt⟩ (hT.1 _) fld oh.idx
                          (fieldIndex_opt ho)]
                        have hcast : HEq (durchTermO u Γ Λ pnum hlt oh pv cap.down i held)
                            (Expr.thru (D := declOf u) (Expr.var pv) ⟨pnum, hlt⟩
                              cap.down oh.idx i held) := by
                          unfold durchTermO
                          exact mpr_heq _ _
                        apply congrArg some
                        symm
                        exact valOf_eval_heq ((congrArg Ty.opt same).symm.trans oh.hopt.symm)
                          _ _ ((mpr_heq _ _).trans hcast) σ₀ σ ρ
                  · cases h
            · cases h
        · cases h
      · cases h
  | glob => cases hb

/-- `is_some` compares the option constructor, never its numeric payload. -/
theorem eval_option_test {D : Deklaration} {n : Int} (v : Wert D (.opt n))
    (s : Gabbro.Body.State) (e : Gabbro.Body.Expr)
    (h : Gabbro.Body.eval s e = some (valOf (.opt n) v)) :
    Gabbro.Body.eval s (.bin .ne e (.lit .absent)) = some (.bool v.isSome) := by
  cases v <;> simp [Gabbro.Body.eval, h, valOf, Gabbro.Body.binop]

/-- Optional call arguments use the same option value theorem as binders and returns. -/
theorem lowCallOptionArg_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {c : Fin u.fns.length} {kind : UParamArt} {ty : Ty} {v : UOpt}
    {ev : Expr (declOf u) Γ Λ ty} {e : Gabbro.Body.Expr}
    (h : lowCallArgOneL u c Γ fn Λ kind ty (.oval v) = .ok ev)
    (hb : optionExpr u fn v = some e)
    (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : LRel fn 0 ρ s.local') :
    Gabbro.Body.eval s e = some (valOf ty (eval σ₀ ev σ ρ)) := by
  cases kind with
  | opt num =>
    cases ty with
    | opt n =>
      simp only [lowCallArgOneL] at h
      split at h
      · rename_i hn
        split at h
        · rename_i same
          split at h
          · cases h
          · rename_i eo ho
            cases h
            rw [lowOpt_sim ho hb hT σ₀ σ ρ s hW.1 hL]
            exact congrArg some (valOf_eval_heq (congrArg Ty.opt same) eo _
              (mpr_heq _ _).symm σ₀ σ ρ)
        · cases h
      · cases h
    | _ => simp only [lowCallArgOneL] at h; cases h
  | ptr a =>
    cases ty with
    | ptr cap =>
      rcases cap with ⟨sp, ⟨rd, wr, ow⟩, tg⟩
      cases ow <;> cases tg <;> simp only [lowCallArgOneL] at h
      all_goals repeat' split at h
      all_goals first | cases h | simp at h
    | _ =>
      simp only [lowCallArgOneL] at h
      all_goals repeat' split at h
      all_goals first | cases h | simp at h
  | _ =>
    cases ty <;> simp only [lowCallArgOneL] at h
    all_goals repeat' split at h
    all_goals cases h

end Gabbro.Bruecke
