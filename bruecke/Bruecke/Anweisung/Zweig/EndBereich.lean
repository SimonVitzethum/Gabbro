module
public import Bruecke.Anweisung.Zweig.EndZiel
public import Bruecke.Kette.Formen.Bereich
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

theorem endZiel_narrow_G {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {ns : BodyNames} {x id : String}
    {a b lo hi : Int} {j : Nat} {v : Var Γ (.int a b)}
    {err : Endblock (declOf u) (verOf u c) false Γ Λ}
    {rest : Endblock (declOf u) (verOf u c) false (.int lo hi :: Γ) Λ}
    {errorBody ys : List Gabbro.Body.Stmt} (hj : paramPos fn.params x = .ok j)
    (hv : lowVar Γ j (.int a b) = .ok v) (hid : ns.lookup fn x = some id)
    (hU : UmfangB Γ fn ns)
    (hErr : ∀ σ ρ s, WGRel u σ s.world → PositionalLRel fn ns.active 0 ρ s.local' →
      EndZiel_G u C c O passes R fn ns.active err σ ρ s errorBody)
    (hRest : ∀ σ ρ s, WGRel u σ s.world →
      PositionalLRel (fn.mitBindung x (lo, hi)) (ns.push x).active 0 ρ s.local' →
      EndZiel_G u C c O passes R (fn.mitBindung x (lo, hi)) (ns.push x).active rest σ ρ s ys)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    EndZiel_G u C c O passes R fn ns.active (.narrow (.var v) lo hi err rest) σ ρ s
      (narrowStep ns x lo hi (.name id) errorBody :: ys) := by
  let σl := σ.lese Λ (Expr.var (Λ := Λ) v).orte
  have hWl : WGRel u σl s.world := wgrel_same u rfl rfl hW
  have hval := narrowName_eval hj hv hid ρ s hL
  have ht := narrowTest_eval (lo := lo) (hi := hi) hval
  by_cases hb : lo ≤ (ρ.get v).n ∧ (ρ.get v).n ≤ hi
  · let value : Wert (declOf u) (.int lo hi) := ⟨(ρ.get v).n, hb.1, hb.2⟩
    let s₁ : Gabbro.Body.State :=
      ⟨s.world, Gabbro.Body.bindLocal s.local' (ns.fresh x) (.int (ρ.get v).n)⟩
    have hs : ∀ ρB, Gabbro.Body.step ρB (narrowStep ns x lo hi (.name id) errorBody) s = .running s₁ := by
      intro ρB
      simp only [narrowStep, Gabbro.Body.step, ht, hb, decide_true, Gabbro.Body.exec, hval]
    have hL₁ := hL.push x (ns.fresh x) (lo, hi) (BodyNames.fresh_not_active hU.valid x) value
    have hr := hRest σl (.cons value ρ) s₁ hWl hL₁
    rw [endZiel_false_iff] at hr ⊢
    refine ⟨fun e he => hr.1 e ?_, fun σ' v' he => ?_, fun σ' r' he => ?_⟩
    · simp only [execEnd, eval, hb, ↓reduceDIte] at he
      exact EndAusgang.schrumpf_logik he
    · simp only [execEnd, eval, hb, ↓reduceDIte] at he
      obtain ⟨A, hr⟩ := hr.2.1 σ' v' (endSchrumpf_zurueck he)
      exact ⟨A, RueckZ_G.vor (fun ρB _ => hs ρB) (fun w => Int.le_refl _) hr⟩
    · simp only [execEnd, eval, hb, ↓reduceDIte] at he
      obtain ⟨A, hr⟩ := hr.2.2 σ' r' (endSchrumpf_why he)
      exact ⟨A, RueckZ_G.vor (fun ρB _ => hs ρB) (fun w => Int.le_refl _) hr⟩
  · apply endZiel_of_G (q := err) (σl := σl) ys
      (by simp only [execEnd, eval, hb, ↓reduceDIte])
      (fun ρB => by simp only [narrowStep, Gabbro.Body.step, ht, hb, decide_false])
      (hErr σl ρ s hWl hL)

end Gabbro.Bruecke
