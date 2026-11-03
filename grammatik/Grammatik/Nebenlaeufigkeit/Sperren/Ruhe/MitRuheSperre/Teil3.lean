module

public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSperre.Teil3a

public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSperre.Teil2
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSperre.Teil2a

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-- Transport the complete optional answer before extending its continuation environment. -/
private theorem ergTransport_ru {e : Option Ty} {τ : Ty} (he : e = some τ)
    (he' : e.map tyR = some (tyR τ)) (v : ErgVal D e) :
    (he' ▸ ergR e v : ErgVal D.mitRuhe (some (tyR τ))) =
      valR τ (he ▸ v : ErgVal D (some τ)) := by
  cases he
  cases he'
  rfl

section Haupt
variable (S : SperrInv D) (O : Orakel D) (O' : Orakel D.mitRuhe) (hO : OrakelRu O O')
  (U : Umwelt D) (U' : Umwelt D.mitRuhe) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) → RufAusgang f)
  (hU : ∀ L σ, U' L (worldR σ) = worldR (U L σ))
  (hR : RufRel R R')
include hO hU hR

set_option linter.unusedSectionVars false in
theorem execBlockH_ru_regRead {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (r)
    (hk)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.regRead r hk rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.regRead r hk rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH]
  rw [worldR_fragt, hO.regLies, einpassen_ru O.zeiger O'.zeiger hO.zeiger]
  cases einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) with
  | none => exact Or.inl rfl
  | some v =>
      simp only [Option.map]
      erw [rzusage_mitRuhe]
      cases D.rzusage r v with
      | false => exact Or.inl rfl
      | true =>
          simp only [if_true]
          exact AusRelRu.schrumpf (ih_execBlockH_ru_rest (σ.fragt (.inr (.inl r))) (Env.cons v ρ))

set_option linter.unusedSectionVars false in
theorem execBlockH_ru_regReadElse {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (r)
    (hk)
    (zusage)
    (sonst)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    (ih_execEndH_ru_sonst : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd sonst) (worldR σ) (envR ρ)) (execEndH S O U passes R sonst σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.regReadElse r hk zusage sonst rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.regReadElse r hk zusage sonst rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH]
  rw [worldR_fragt, hO.regLies, einpassen_ru O.zeiger O'.zeiger hO.zeiger]
  cases einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) with
  | none => exact Or.inl rfl
  | some v =>
      simp only [Option.map]
      have horte :
          (ruE zusage : Expr D.mitRuhe (tyR (D.rtyp r) :: Γ.map tyR)
            (Λ.map resR) .bool).orte = zusage.orte := ruE_orte zusage
      erw [horte, lese_worldR]
      have ez := eval_ru ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) zusage (Env.cons v ρ)
      change @Eq Bool (eval _ (ruE zusage : Expr D.mitRuhe
        (tyR (D.rtyp r) :: Γ.map tyR) (Λ.map resR) .bool) _ (Env.cons (valR _ v) (envR ρ)))
        (eval ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) zusage
          ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) (Env.cons v ρ)) at ez
      erw [ez]
      cases h : (eval ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) zusage ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) (Env.cons v ρ) : Bool) with
      | false =>
          simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
          exact EndRel.zuAusgang (ih_execEndH_ru_sonst _ ρ)
      | true =>
          simp only [wahr?, valR_bool, h, if_true]
          exact AusRelRu.schrumpf (ih_execBlockH_ru_rest _ (Env.cons v ρ))

set_option linter.unusedSectionVars false in
theorem execBlockH_ru_awaits {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (g)
    (payload)
    (hp)
    (hL)
    (hat)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.awaits g payload hp hL hat rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.awaits g payload hp hL hat rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH]
  rw [worldR_fragt, hO.sichtbar]
  cases O.sichtbar g (σ.fragt (.inr (.inr g))) with
  | false => exact Or.inl rfl
  | true =>
      simp only [if_true]
      rw [show ([Sum.inr g] : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) = [Sum.inr g] from rfl,
        lese_worldR]
      exact AusRelRu.schrumpf (ih_execBlockH_ru_rest ((σ.fragt (.inr (.inr g))).lese Λ [Sum.inr g])
        (Env.cons (((σ.fragt (.inr (.inr g))).lese Λ [Sum.inr g]).globs g) ρ))

set_option linter.unusedSectionVars false in
theorem execBlockH_ru_exchange {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (g)
    (neu)
    (hw)
    (hL)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.exchange g neu hw hL rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.exchange g neu hw hL rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH]
  rw [show (Sum.inr g :: (ruE neu).orte : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) =
    Sum.inr g :: neu.orte from congrArg (Sum.inr g :: ·) (ruE_orte neu), lese_worldR]
  have ez := eval_ru (σ.lese Λ (Sum.inr g :: neu.orte)) (σ.lese Λ (Sum.inr g :: neu.orte)) neu
    (Env.cons ((σ.lese Λ (Sum.inr g :: neu.orte)).globs g) ρ)
  change eval _ (ruE neu) _ (Env.cons (valR _ _) (envR ρ)) = _ at ez
  rw [show ((worldR (σ.lese Λ (Sum.inr g :: neu.orte))).globs g) =
    valR _ ((σ.lese Λ (Sum.inr g :: neu.orte)).globs g) from rfl, ez, schreibGlob_worldR]
  exact AusRelRu.schrumpf (ih_execBlockH_ru_rest
    ((σ.lese Λ (Sum.inr g :: neu.orte)).schreibGlob g Λ (eval (σ.lese Λ (Sum.inr g :: neu.orte)) neu
      (σ.lese Λ (Sum.inr g :: neu.orte)) (Env.cons ((σ.lese Λ (Sum.inr g :: neu.orte)).globs g) ρ)))
    (Env.cons ((σ.lese Λ (Sum.inr g :: neu.orte)).globs g) ρ))

set_option linter.unusedSectionVars false in
theorem execBlockH_ru_narrow {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_lo}
    {zi_hi}
    (e)
    (lo')
    (hi')
    (sonst)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    (ih_execEndH_ru_sonst : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd sonst) (worldR σ) (envR ρ)) (execEndH S O U passes R sonst σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH]
  have hread : (worldR σ).lese (Λ.map resR) (ruE e).orte =
      worldR (σ.lese Λ e.orte) :=
    (lese_worldR σ Λ _).trans
      (congrArg (fun os => worldR (σ.lese Λ os)) (ruE_orte e))
  have hv : @Eq (Zahl zi_lo zi_hi)
      (eval ((worldR σ).lese (Λ.map resR) (ruE e).orte) (ruE e)
        ((worldR σ).lese (Λ.map resR) (ruE e).orte) (envR ρ))
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) :=
    (congrArg (fun W => eval W (ruE e) W (envR ρ)) hread).trans
      (eval_ru (σ.lese Λ e.orte) (σ.lese Λ e.orte) e ρ)
  let branch (W : World D.mitRuhe) (z : Zahl zi_lo zi_hi) :
      Ausgang (vertragR V) l (Γ.map tyR) :=
    if h : lo' ≤ z.n ∧ z.n ≤ hi' then
      (execBlockH S.mitRuhe O' U' passes R' (ruB rest) W
        (Env.cons (τ := .int lo' hi') ⟨z.n, h.1, h.2⟩ (envR ρ))).schrumpf
    else (execEndH S.mitRuhe O' U' passes R' (ruEnd sonst) W (envR ρ)).zuAusgang
  change AusRelRu (branch ((worldR σ).lese (Λ.map resR) (ruE e).orte)
    (eval ((worldR σ).lese (Λ.map resR) (ruE e).orte) (ruE e)
      ((worldR σ).lese (Λ.map resR) (ruE e).orte) (envR ρ))) _
  erw [hv, hread]
  dsimp only [branch]
  by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi'
  · erw [dif_pos hc, dif_pos hc]
    exact AusRelRu.schrumpf (ih_execBlockH_ru_rest _
      (Env.cons (⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, hc.1, hc.2⟩ : Zahl lo' hi') ρ))
  · erw [dif_neg hc, dif_neg hc]
    exact EndRel.zuAusgang (ih_execEndH_ru_sonst _ ρ)

set_option linter.unusedSectionVars false in
theorem execBlockH_ru_narrowRequired {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_lo}
    {zi_hi}
    (e)
    (lo')
    (hi')
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.narrowRequired (lo := zi_lo) (hi := zi_hi) e lo' hi' rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.narrowRequired (lo := zi_lo) (hi := zi_hi) e lo' hi' rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH]
  have hread : (worldR σ).lese (Λ.map resR) (ruE e).orte =
      worldR (σ.lese Λ e.orte) :=
    (lese_worldR σ Λ _).trans
      (congrArg (fun os => worldR (σ.lese Λ os)) (ruE_orte e))
  have hv : @Eq (Zahl zi_lo zi_hi)
      (eval ((worldR σ).lese (Λ.map resR) (ruE e).orte) (ruE e)
        ((worldR σ).lese (Λ.map resR) (ruE e).orte) (envR ρ))
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) :=
    (congrArg (fun W => eval W (ruE e) W (envR ρ)) hread).trans
      (eval_ru (σ.lese Λ e.orte) (σ.lese Λ e.orte) e ρ)
  let branch (W : World D.mitRuhe) (z : Zahl zi_lo zi_hi) :
      Ausgang (vertragR V) l (Γ.map tyR) :=
    if h : lo' ≤ z.n ∧ z.n ≤ hi' then
      (execBlockH S.mitRuhe O' U' passes R' (ruB rest) W
        (Env.cons (τ := .int lo' hi') ⟨z.n, h.1, h.2⟩ (envR ρ))).schrumpf
    else .logik .kapazitaet
  change AusRelRu (branch ((worldR σ).lese (Λ.map resR) (ruE e).orte)
    (eval ((worldR σ).lese (Λ.map resR) (ruE e).orte) (ruE e)
      ((worldR σ).lese (Λ.map resR) (ruE e).orte) (envR ρ))) _
  erw [hv, hread]
  dsimp only [branch]
  by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi'
  · erw [dif_pos hc, dif_pos hc]
    exact AusRelRu.schrumpf (ih_execBlockH_ru_rest _
      (Env.cons (⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, hc.1, hc.2⟩ : Zahl lo' hi') ρ))
  · erw [dif_neg hc, dif_neg hc]
    exact Or.inl rfl

set_option linter.unusedSectionVars false in
theorem execBlockH_ru_check {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (c)
    (sonst)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    (ih_execEndH_ru_sonst : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd sonst) (worldR σ) (envR ρ)) (execEndH S O U passes R sonst σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.check c sonst rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.check c sonst rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH]
  erw [ruE_orte, lese_worldR, eval_ru]
  cases h : (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ : Bool) with
  | false =>
      simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
      exact EndRel.zuAusgang (ih_execEndH_ru_sonst _ ρ)
  | true =>
      simp only [wahr?, valR_bool, h, if_true]
      exact ih_execBlockH_ru_rest _ ρ

set_option linter.unusedSectionVars false in
theorem execBlockH_ru_float {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_l1}
    {zi_h1}
    {zi_l2}
    {zi_h2}
    (op)
    (a)
    (b)
    (lo)
    (hi)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH]
  erw [orte2, lese_worldR, eval_ru, eval_ru]
  have ha := congrArg (fun v : Gleit zi_l1 zi_h1 => v.x)
    (valR_fl (D := D)
      (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ))
  have hb := congrArg (fun v : Gleit zi_l2 zi_h2 => v.x)
    (valR_fl (D := D)
      (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ))
  erw [ha, hb]
  cases gleitPasst lo hi (gleitRechne op
      (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
      (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) with
  | none => exact Or.inl rfl
  | some v => exact AusRelRu.schrumpf (ih_execBlockH_ru_rest _ (Env.cons v ρ))

set_option linter.unusedSectionVars false in
theorem execBlockH_ru_bindAxiomOpt {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_e}
    (a)
    (args)
    (he)
    (hp)
    (hd)
    (hgd)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.bindAxiomOpt (e := zi_e) a args he hp hd hgd rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.bindAxiomOpt (e := zi_e) a args he hp hd hgd rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  cases zi_e with
  | none =>
      simp only [ruB, execBlockH]
      erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwort_ruG hO]
      cases axiomAntwort O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ' w =>
          cases w with
          | none => exact Or.inl rfl
          | some v =>
              simp only [Option.map, Ausgang.weiterOpt, ergEnv]
              erw [execBlockH_vorΛ]
              exact ih_execBlockH_ru_rest σ' ρ
  | some τ =>
      simp only [ruB, execBlockH]
      erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwort_ruG hO]
      cases axiomAntwort O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ' w =>
          cases w with
          | none => exact Or.inl rfl
          | some v =>
              simp only [Option.map, Ausgang.weiterOpt, ergEnv]
              erw [execBlockH_vorΛ]
              have hv := ergTransport_ru he (congrArg (Option.map tyR) he) v
              have henv := congrArg
                (fun w : Wert D.mitRuhe (tyR τ) => Env.cons w (envR ρ)) hv
              erw [henv]
              exact AusRelRu.schrumpf (ih_execBlockH_ru_rest σ'
                (Env.cons (show ErgVal D (some τ) from he ▸ v) ρ))

set_option linter.unusedSectionVars false in
theorem execBlockH_ru_bindAxiomOptElse {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_e}
    (a)
    (args)
    (he)
    (hr)
    (hp)
    (hd)
    (hgd)
    (err)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    (ih_execEndH_ru_err : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd err) (worldR σ) (envR ρ)) (execEndH S O U passes R err σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.bindAxiomOptElse (e := zi_e) a args he hp hd hgd hr err rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.bindAxiomOptElse (e := zi_e) a args he hp hd hgd hr err rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  cases zi_e with
  | none =>
      simp only [ruB, execBlockH]
      erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwortSonst_ruG hO]
      cases axiomAntwortSonst O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ' w =>
          rcases w with _ | v | r
          · exact Or.inl rfl
          · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply, id]
            simp only [Ausgang.weiterOpt, ergEnv]
            erw [execBlockH_vorΛ]
            exact ih_execBlockH_ru_rest σ' ρ
          · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply, id]
            erw [execEndH_umΛ]
            exact EndRel.zuAusgang (EndRel.schrumpf
              (ih_execEndH_ru_err σ' (Env.cons (τ := reasonTy (D.agruende a)) r ρ)))
  | some τ =>
      simp only [ruB, execBlockH]
      erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwortSonst_ruG hO]
      cases axiomAntwortSonst O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ' w =>
          rcases w with _ | v | r
          · exact Or.inl rfl
          · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply, id]
            simp only [Ausgang.weiterOpt, ergEnv]
            erw [execBlockH_vorΛ]
            have hv := ergTransport_ru he (congrArg (Option.map tyR) he) v
            have henv := congrArg
              (fun w : Wert D.mitRuhe (tyR τ) => Env.cons w (envR ρ)) hv
            erw [henv]
            exact AusRelRu.schrumpf (ih_execBlockH_ru_rest σ'
              (Env.cons (show ErgVal D (some τ) from he ▸ v) ρ))
          · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply, id]
            erw [execEndH_umΛ]
            exact EndRel.zuAusgang (EndRel.schrumpf
              (ih_execEndH_ru_err σ' (Env.cons (τ := reasonTy (D.agruende a)) r ρ)))


end Haupt
end Gabbro.Grammatik
