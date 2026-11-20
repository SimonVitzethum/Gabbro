module
public import Bruecke.Anweisung.Match.Basis
public import Bruecke.Anweisung.Lokal.Position
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg}

theorem lowOpt_named_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {ns : BodyNames} {num : Nat} {hn : num < u.tabs.length} {v : UOpt}
    {ev : Expr (declOf u) Γ Λ (.opt ((declOf u).count ⟨num, hn⟩))} {e : Gabbro.Body.Expr}
    (h : lowOpt u Γ Λ fn 0 num hn v = .ok ev) (hb : optionZ fn ns v = some e)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    Gabbro.Body.eval s e = some (valOf (.opt ((declOf u).count ⟨num, hn⟩)) (eval σ₀ ev σ ρ)) := by
  cases v with
  | nichts => cases h; cases hb; rfl
  | etwas ix =>
    simp only [lowOpt] at h
    cases hi : lowIdx u Γ Λ fn 0 ⟨num, hn⟩ ix with
    | error err => rw [hi] at h; cases h
    | ok ei =>
      rw [hi] at h
      cases h
      simp only [optionZ] at hb
      cases hr : renameScalar (ns.lookup fn) (idxExpr ix) with
      | none => rw [hr] at hb; cases hb
      | some raw =>
        rw [hr] at hb
        cases hb
        have hv := lowIdx_sim hi σ₀ σ ρ s.world (ns.visible fn s.local') (hL.visible (ns := ns))
        change Gabbro.Body.eval ⟨s.world, visibleBinding (ns.lookup fn) s.local'⟩ (idxExpr ix) = _ at hv
        have he := eval_renameScalar (ns.lookup fn) s (idxExpr ix) raw hr
        simp only [Gabbro.Body.eval, he, hv, eval, valOf]
  | var x =>
    simp only [optionZ] at hb
    cases hid : ns.lookup fn x with
    | none => rw [hid] at hb; cases hb
    | some id =>
      rw [hid] at hb
      cases hb
      simp only [lowOpt] at h
      cases hj : paramPos fn.params x with
      | error err => rw [hj] at h; cases h
      | ok j =>
        simp only [hj, Nat.zero_add] at h
        cases hk : fn.kinds[j]? with
        | none => rw [hk] at h; cases h
        | some kind =>
          cases kind <;> rw [hk] at h
          case opt m =>
            by_cases hm : (m == num) = true
            · simp only [hm, decide_true, ↓reduceIte, ↓reduceDIte] at h
              cases hv : lowVar Γ j (.opt ((declOf u).count ⟨num, hn⟩)) with
              | error err => rw [hv] at h; cases h
              | ok var =>
                rw [hv] at h
                cases h
                have hi : ns.active[j]? = some id := by
                  simpa only [BodyNames.lookup, hj] using hid
                simp only [Gabbro.Body.eval]
                rw [hL.values j id hi]
                try rw [Nat.zero_add]
                rw [nthVal_lowVar Γ j _ var ρ hv]
                rfl
            · simp only [hm, decide_false, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte] at h
              cases h
          all_goals cases h
  | slot | tab | glob => cases hb

end Gabbro.Bruecke
