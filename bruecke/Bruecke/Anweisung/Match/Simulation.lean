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
theorem stmtZiel_option_G {loopMode : Bool} {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {Γ : Ctx} {fn ft : UFn} {ns : BodyNames} {Λ Λ' : List (Res (declOf u))}
    {num : Nat} {hn : num < u.tabs.length} {v : UOpt} {x : String}
    {ev : Expr (declOf u) Γ Λ (.opt ((declOf u).count ⟨num, hn⟩))}
    {pb : Block (declOf u) (verOf u c) loopMode (.index ((declOf u).count ⟨num, hn⟩) :: Γ) Λ Λ'}
    {ab : Block (declOf u) (verOf u c) loopMode Γ Λ Λ'}
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
        (execBlock O passes R pb σl (.cons value ρ)).schrumpf t ps := by
      first
        | (simp only [execStmt, σl, hh]; done)
        | (simp only [execStmt, σl] at *; simp only [hh])
        | simp [execStmt, σl, hh]
    have hB : ∀ ρB, Gabbro.Body.step ρB (.onOption e (ns.fresh x) ps as) s =
        Gabbro.Body.exec ρB ps t := by
      intro ρB
      simp only [hh, valOf] at hval
      simp only [Gabbro.Body.step, hval]; rfl
    have shrunk := ausgangZiel_schrumpf (Strecke_G.leer t)
      (fun _ _ hl => hl.tailIndex) hArm
    unfold StmtZiel_G
    rw [hG]
    exact ausgangZiel_map_state (by simpa only [List.nil_append] using shrunk) rfl
      (fun ρB => by rw [Gabbro.Body.exec_singleton, hB])

end Gabbro.Bruecke
