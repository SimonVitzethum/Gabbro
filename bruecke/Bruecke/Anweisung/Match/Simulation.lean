module
public import Bruecke.Anweisung.Match.Werte
public import Bruecke.Anweisung.Schleife.Basis
public import Bruecke.Kette.Schritt
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg} {C : Fin u.fns.length → Prop}

/-- An option arm binds the checked table index once. Normal completion removes its
    source entry while every outer positional value, sampled call and return survives. -/
theorem stmtZiel_option_G {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {Γ : Ctx} {fn ft : UFn} {ns : BodyNames} {Λ Λ' : List (Res (declOf u))}
    {num : Nat} {hn : num < u.tabs.length} {v : UOpt} {x : String}
    {ev : Expr (declOf u) Γ Λ (.opt ((declOf u).count ⟨num, hn⟩))}
    {pb : Block (declOf u) (verOf u c) false (.index ((declOf u).count ⟨num, hn⟩) :: Γ) Λ Λ'}
    {ab : Block (declOf u) (verOf u c) false Γ Λ Λ'}
    {e : Gabbro.Body.Expr} {ps as : List Gabbro.Body.Stmt}
    (hU : UmfangB Γ fn ns) (hV : Sicht u ft fn)
    (hv : lowOpt u Γ Λ fn 0 num hn v = .ok ev) (he : optionZ ft ns v = some e)
    (hp : ∀ σ ρ s, WGRel u σ s.world →
      PositionalLRel (fn.mitIndex x num ((declOf u).count ⟨num, hn⟩)) (ns.push x).active 0 ρ s.local' →
      BlockZiel_G u C c O passes R (fn.mitIndex x num ((declOf u).count ⟨num, hn⟩))
        (ns.push x).active pb σ ρ s ps)
    (ha : ∀ σ ρ s, WGRel u σ s.world → PositionalLRel fn ns.active 0 ρ s.local' →
      BlockZiel_G u C c O passes R fn ns.active ab σ ρ s as)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    StmtZiel_G u C c O passes R fn ns.active (.onOption ev pb ab) σ ρ s
      (.onOption e (ns.fresh x) ps as) := by
  let σl := σ.lese Λ ev.orte
  have hWl : WGRel u σl s.world := wgrel_same u rfl rfl hW
  have he' := (optionZ_sicht hV ns v).symm.trans he
  have hval := lowOpt_named_sim hv he' σl σl ρ s hL
  cases hh : eval σl ev σl ρ with
  | none =>
    have hG : execStmt O passes R (.onOption ev pb ab) σ ρ = execBlock O passes R ab σl ρ := by
      first
        | (simp only [execStmt, σl, hh]; done)
        | (simp only [execStmt, σl] at *; simp only [hh])
        | simp [execStmt, σl, hh]
    have hB : ∀ ρB, Gabbro.Body.step ρB (.onOption e (ns.fresh x) ps as) s =
        Gabbro.Body.exec ρB as s := by
      intro ρB
      simp only [hh, valOf] at hval
      simp only [Gabbro.Body.step, hval]
    exact stmtZiel_of_G hG hB (ha σl ρ s hWl hL)
  | some value =>
    let t : Gabbro.Body.State := ⟨s.world, Gabbro.Body.bindLocal s.local' (ns.fresh x) (.int value.n)⟩
    have ht := hL.pushIndex x hU.valid num ((declOf u).count ⟨num, hn⟩) value
    have hArm := hp σl (.cons value ρ) t hWl ht
    have hG : execStmt O passes R (.onOption ev pb ab) σ ρ =
        (execBlock O passes R pb σl (.cons value ρ)).schrumpf := by
      first
        | (simp only [execStmt, σl, hh]; done)
        | (simp only [execStmt, σl] at *; simp only [hh])
        | simp [execStmt, σl, hh]
    have hB : ∀ ρB, Gabbro.Body.step ρB (.onOption e (ns.fresh x) ps as) s =
        Gabbro.Body.exec ρB ps t := by
      intro ρB
      simp only [hh, valOf] at hval
      simp only [Gabbro.Body.step, hval]; rfl
    refine ⟨fun err h => hArm.1 err (schrumpfZ_logik (hG.symm.trans h)),
      fun σ' result h => ?_, fun σ' env h => ?_⟩
    · obtain ⟨A, hg, ho, hk, hr⟩ := hArm.2.1 σ' result (schrumpfZ_zurueck (hG.symm.trans h))
      refine ⟨A, hg, ho, hk, fun ρB hT hF => ?_⟩
      obtain ⟨s', hs, hw⟩ := hr ρB hT hF
      exact ⟨s', by simp only [Gabbro.Body.exec, hB ρB, hs], hw⟩
    · obtain ⟨env', hex, rfl⟩ := schrumpfZ_ok (hG.symm.trans h)
      obtain ⟨A, s', hStretch, hw, hl⟩ := hArm.2.2 σ' env' hex
      refine ⟨A, s', { hStretch with lauf := fun ρB hT hF => ?_ }, hw, hl.tailIndex⟩
      simp only [Gabbro.Body.exec, hB ρB, hStretch.lauf ρB hT hF]

end Gabbro.Bruecke
