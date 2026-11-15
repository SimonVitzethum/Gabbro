module
public import Bruecke.Ausdruck.RecordFit
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg}

/-- Field projection shares the typed schema lookup and runtime list-index law in both
    the numeric and general value simulations. Only the base expression is recursive. -/
theorem lowWertE_field_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {er : Option Ty} {base : USide} {name : String} {wv : LowWert u Γ Λ}
    {tag : Option Ty} {eB : Gabbro.Body.Expr}
    (h : lowWertE u Γ Λ fn er (.field base name) = .ok wv)
    (hb : recordProject u (recordRead u fn base) name = some (tag, eB))
    {σ₀ σ : World (declOf u)} {ρ : Env (declOf u) Γ} {w : Gabbro.Body.World}
    {β : Gabbro.Body.Binding}
    (base_sim : ∀ {v : LowWert u Γ Λ} {t : Option Ty} {e : Gabbro.Body.Expr},
      lowWertE u Γ Λ fn er base = .ok v → recordRead u fn base = some (t, e) →
      Gabbro.Body.eval ⟨w, β⟩ e = some (valOf v.ty (eval σ₀ v.term σ ρ)) ∧
        (∀ ty, t = some ty → v.ty = ty)) :
    Gabbro.Body.eval ⟨w, β⟩ eB = some (valOf wv.ty (eval σ₀ wv.term σ ρ)) ∧
      (∀ ty, tag = some ty → wv.ty = ty) := by
    cases hr : recordRead u fn base with
    | none => simp [recordProject, hr] at hb
    | some out =>
        rcases out with ⟨bt, be⟩
        cases bt with
        | none => simp [recordProject, hr] at hb
        | some ty =>
            cases hg : u.exportGate with
            | error err => simp [lowWertE, hg, bind, Except.bind] at h
            | ok gate =>
                cases hw : lowWertE u Γ Λ fn er base with
                | error err => simp [lowWertE, hg, hw, bind, Except.bind] at h
                | ok baseW =>
                    obtain ⟨hv, hty⟩ := base_sim hw hr
                    have same := hty ty rfl
                    rcases baseW with ⟨actual, term⟩
                    dsimp only at same
                    subst actual
                    cases hs : uRecordOf u.records ty with
                    | error err => simp [recordProject, hr, hs, Except.toOption, bind, Option.bind] at hb
                    | ok schema =>
                        cases hp : uRecordPosition schema.val.fields name with
                        | error err => simp [recordProject, hr, hs, hp, Except.toOption, bind, Option.bind] at hb
                        | ok pos =>
                            rcases pos with ⟨fieldTy, pos⟩
                            simp only [recordProject, hr, hs, hp, Except.toOption,
                              Option.unattach, Option.map_some, bind, Option.bind, pure,
                              Option.some.injEq, Prod.mk.injEq] at hb
                            obtain ⟨rfl, rfl⟩ := hb
                            simp only [lowWertE, hg, hw, hs, hp, bind, Except.bind,
                              pure, Except.pure, Except.ok.injEq] at h
                            cases h
                            let baseE := cast (congrArg (Expr (declOf u) Γ Λ) schema.property.symm) term
                            have he : Gabbro.Body.eval ⟨w, β⟩ be =
                                some (.record (valOfProd _ (eval σ₀ baseE σ ρ))) := by
                              rw [hv, ← valOf_cast_eval schema.property.symm term σ₀ σ ρ]
                              rfl
                            refine ⟨?_, fun _ heq => Option.some.inj heq⟩
                            rw [Gabbro.Body.eval_recGet _ _ _ _ he]
                            exact valOfProd_get (D := declOf u) pos (eval σ₀ baseE σ ρ)

end Gabbro.Bruecke
