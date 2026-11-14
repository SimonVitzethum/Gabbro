module
public import Bruecke.Anweisung.Bereich.Ende
public import Bruecke.Anweisung.Zweig.EndKopf
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

/-- Outside a loop, an explicit ending cannot run on or take either control exit.
    This equivalence retains all four channels of the shared outcome relation. -/
theorem endZiel_false_iff {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {ids : List String}
    {b : Endblock (declOf u) (verOf u c) false Γ Λ} {σ : World (declOf u)}
    {ρ : Env (declOf u) Γ} {s : Gabbro.Body.State} {bs : List Gabbro.Body.Stmt} :
    EndZiel_G u C c O passes R fn ids b σ ρ s bs ↔
      (∀ e, execEnd O passes R b σ ρ = .logik e →
        ∃ (g : (declOf u).Fn) (σr : World (declOf u)) (envA : Env (declOf u) ((declOf u).params g)),
          C g ∧ R g σr envA = .logik e) ∧
      (∀ σ' v, execEnd O passes R b σ ρ = .zurueck σ' v →
        ∃ A, RueckZ_G u C A s bs σ' (ergValOf (verOf u c).erg v)) := by
  constructor
  · intro h
    exact ⟨fun e he => h.1 e (congrArg EndAusgang.zuAusgang he),
      fun σ' v he => h.2.1 σ' v (congrArg EndAusgang.zuAusgang he)⟩
  · rintro ⟨hlog, hret⟩
    refine ⟨?_, ?_, ?_, fun leave hl => by cases hl⟩
    · intro e he
      apply hlog e
      cases hx : execEnd O passes R b σ ρ <;>
        simp only [hx, EndAusgang.zuAusgang, reduceCtorEq] at he <;> cases he <;> rfl
    · intro σ' v he
      apply hret σ' v
      cases hx : execEnd O passes R b σ ρ <;>
        simp only [hx, EndAusgang.zuAusgang, reduceCtorEq] at he <;> cases he <;> rfl
    · intro σ' ρ' he
      cases hx : execEnd O passes R b σ ρ <;>
        simp only [hx, EndAusgang.zuAusgang, reduceCtorEq] at he <;> cases he

theorem endZiel_to_lauf {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {ids : List String}
    {b : Endblock (declOf u) (verOf u c) false Γ Λ} {σ : World (declOf u)}
    {ρ : Env (declOf u) Γ} {s : Gabbro.Body.State} {bs : List Gabbro.Body.Stmt}
    (h : EndZiel_G u C c O passes R fn ids b σ ρ s bs) :
    LaufZielTeilB u C c O passes R b σ ρ s bs := by
  rw [endZiel_false_iff] at h
  refine ⟨h.1, fun σ' v hv => ?_⟩
  obtain ⟨A, hg, ho, hk, hr⟩ := h.2 σ' v hv
  refine ⟨A, hg, ho, hk, fun ρB hT hF => ?_⟩
  obtain ⟨s', hs, hw⟩ := hr ρB hT hF
  exact ⟨s', by rw [hs]; rfl, by rw [hs, finalValue_returned], hw⟩

theorem endZiel_bind_G {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {Γ : Ctx} {Λ : List (Res (declOf u))} {τ : Ty} {ev : Expr (declOf u) Γ Λ τ}
    {fn fn' : UFn} {ids ids' : List String}
    {q : Endblock (declOf u) (verOf u c) false (τ :: Γ) Λ}
    {σ : World (declOf u)} {ρ : Env (declOf u) Γ} {s s₁ : Gabbro.Body.State}
    {b : Gabbro.Body.Stmt} {bs : List Gabbro.Body.Stmt}
    (hs : ∀ ρB, Gabbro.Body.step ρB b s = .running s₁)
    (hgz : ∀ w, gz w s.world ≤ gz w s₁.world)
    (h : EndZiel_G u C c O passes R fn' ids' q (σ.lese Λ ev.orte)
      (.cons (eval (σ.lese Λ ev.orte) ev (σ.lese Λ ev.orte) ρ) ρ) s₁ bs) :
    EndZiel_G u C c O passes R fn ids (.bind ev q) σ ρ s (b :: bs) := by
  rw [endZiel_false_iff] at h ⊢
  refine ⟨fun e he => h.1 e ?_, fun σ' v he => ?_⟩
  · simp only [execEnd] at he
    exact EndAusgang.schrumpf_logik he
  · simp only [execEnd] at he
    obtain ⟨A, hr⟩ := h.2 σ' v (endSchrumpf_zurueck he)
    exact ⟨A, RueckZ_G.vor (fun ρB _ => hs ρB) hgz hr⟩

theorem endZiel_strecke_G {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {Γ Γ₁ : Ctx} {Λ Λ₁ : List (Res (declOf u))}
    {fn fn' : UFn} {ids ids' : List String}
    {b : Endblock (declOf u) (verOf u c) false Γ Λ}
    {q : Endblock (declOf u) (verOf u c) false Γ₁ Λ₁}
    {σ σ₁ : World (declOf u)} {ρ : Env (declOf u) Γ} {ρ₁ : Env (declOf u) Γ₁}
    {s s₁ : Gabbro.Body.State} {A : List Eintrag} {xs bs : List Gabbro.Body.Stmt}
    (hG : (∀ e, execEnd O passes R b σ ρ = .logik e → execEnd O passes R q σ₁ ρ₁ = .logik e) ∧
      (∀ σ' v, execEnd O passes R b σ ρ = .zurueck σ' v →
        execEnd O passes R q σ₁ ρ₁ = .zurueck σ' v))
    (hs : Strecke_G u C A s s₁ xs) (h : EndZiel_G u C c O passes R fn' ids' q σ₁ ρ₁ s₁ bs) :
    EndZiel_G u C c O passes R fn ids b σ ρ s (xs ++ bs) := by
  rw [endZiel_false_iff] at h ⊢
  refine ⟨fun e he => h.1 e (hG.1 e he), fun σ' v he => ?_⟩
  obtain ⟨A₂, hr⟩ := h.2 σ' v (hG.2 σ' v he)
  exact ⟨A ++ A₂, RueckZ_G.nach hs hr⟩

theorem endZiel_of_G {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {ids : List String}
    {b q : Endblock (declOf u) (verOf u c) false Γ Λ} {σ σl : World (declOf u)}
    {ρ : Env (declOf u) Γ} {s : Gabbro.Body.State} {x : Gabbro.Body.Stmt}
    {bs : List Gabbro.Body.Stmt} (xs : List Gabbro.Body.Stmt)
    (hG : execEnd O passes R b σ ρ = execEnd O passes R q σl ρ)
    (hB : ∀ ρB, Gabbro.Body.step ρB x s = Gabbro.Body.exec ρB bs s)
    (h : EndZiel_G u C c O passes R fn ids q σl ρ s bs) :
    EndZiel_G u C c O passes R fn ids b σ ρ s (x :: xs) := by
  rw [endZiel_false_iff] at h ⊢
  refine ⟨fun e he => h.1 e (hG.symm.trans he), fun σ' v he => ?_⟩
  obtain ⟨A, hg, ho, hk, hr⟩ := h.2 σ' v (hG.symm.trans he)
  refine ⟨A, hg, ho, hk, fun ρB hT hF => ?_⟩
  obtain ⟨s', hs, hw⟩ := hr ρB hT hF
  exact ⟨s', by simp only [Gabbro.Body.exec, hB ρB, hs], hw⟩

/-- An ending conditional preserves both branches' return values and ordered call tables. -/
theorem endZiel_ite_G (hT : TabEindeutig u) {c : Fin u.fns.length} {O : Orakel (declOf u)}
    {passes : Nat}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {Γ : Ctx} {fn fT : UFn} {ns : BodyNames} {Λ : List (Res (declOf u))} {cnd : UEns}
    {cv : Expr (declOf u) Γ Λ .bool} {tb eb : Endblock (declOf u) (verOf u c) false Γ Λ}
    {ce : Gabbro.Body.Expr} {tt te : List Gabbro.Body.Stmt}
    (hU : UmfangB Γ fn ns) (hS : Sicht u fT fn) (hcv : lowEns u Γ Λ fn none cnd = .ok cv)
    (hce : condZ u fT ns cnd = some ce)
    (hBt : ∀ σ ρ s, WGRel u σ s.world → PositionalLRel fn ns.active 0 ρ s.local' →
      EndZiel_G u C c O passes R fn ns.active tb σ ρ s tt)
    (hBe : ∀ σ ρ s, WGRel u σ s.world → PositionalLRel fn ns.active 0 ρ s.local' →
      EndZiel_G u C c O passes R fn ns.active eb σ ρ s te)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    EndZiel_G u C c O passes R fn ns.active (.ite cv tb eb) σ ρ s [.ite ce tt te] := by
  have hWl : WGRel u (σ.lese Λ cv.orte) s.world := wgrel_same u rfl rfl hW
  have hcond : Gabbro.Body.eval s ce =
      some (.bool (wahr? (eval (σ.lese Λ cv.orte) cv (σ.lese Λ cv.orte) ρ))) :=
    lowEns_named_sim hcv ((condZ_sicht hS ns cnd).symm.trans hce) hU.art hT
      (σ.lese Λ cv.orte) (σ.lese Λ cv.orte) ρ s hWl hWl hL
  cases hb : wahr? (eval (σ.lese Λ cv.orte) cv (σ.lese Λ cv.orte) ρ) with
  | true =>
    rw [hb] at hcond
    apply endZiel_of_G (q := tb) (σl := σ.lese Λ cv.orte) []
      (by simp only [execEnd, hb, ↓reduceIte])
      (fun ρB => step_ite_wahr ρB hcond) (hBt _ ρ s hWl hL)
  | false =>
    rw [hb] at hcond
    apply endZiel_of_G (q := eb) (σl := σ.lese Λ cv.orte) []
      (by simp only [execEnd, hb, Bool.false_eq_true, ↓reduceIte])
      (fun ρB => step_ite_falsch ρB hcond) (hBe _ ρ s hWl hL)

end Gabbro.Bruecke
