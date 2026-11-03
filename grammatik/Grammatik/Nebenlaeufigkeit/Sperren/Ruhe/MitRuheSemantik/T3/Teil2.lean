module
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik.T3.Teil2a

public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik.T2
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik.T3.Teil1Control
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik.T3.Teil1b

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-- The optional binder transports the complete canonical answer value. -/
private theorem ergTransport_ru {e : Option Ty} {τ : Ty} (he : e = some τ)
    (he' : e.map tyR = some (tyR τ)) (v : ErgVal D e) :
    (he' ▸ ergR e v : ErgVal D.mitRuhe (some (tyR τ))) =
      valR τ (he ▸ v : ErgVal D (some τ)) := by
  cases he
  cases he'
  rfl

section Haupt
variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) → RufAusgang f)

set_option linter.unusedSectionVars false in
theorem execBlock_ru_bindAxiom {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_τ}
    (a)
    (args)
    (he)
    (hw)
    (hg)
    (hd)
    (hgd)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlock_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB rest) (worldR σ) (envR ρ) = ausR (execBlock O passes R rest σ ρ))
    : execBlock O.mitRuhe passes R' (ruB (.bindAxiom (τ := zi_τ) a args he hw hg hd hgd rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ) = ausR (execBlock O passes R (.bindAxiom (τ := zi_τ) a args he hw hg hd hgd rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlock]
  erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwort_ru]
  cases axiomAntwort O a (σ.lese Λ args.orte)
    (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | mk σ' w =>
      cases w with
      | none => rfl
      | some v =>
          simp only [Option.map]
          rw [ergWert_ru he, ← ausR_schrumpf, ← ih_execBlock_ru_rest σ' (Env.cons _ ρ)]
          rfl

set_option linter.unusedSectionVars false in
theorem execBlock_ru_bindAxiomElse {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_τ}
    (a)
    (args)
    (he)
    (hr)
    (hw)
    (hg)
    (hd)
    (hgd)
    (err)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlock_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB rest) (worldR σ) (envR ρ) = ausR (execBlock O passes R rest σ ρ))
    (ih_execEnd_ru_err : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd err) (worldR σ) (envR ρ) = endR (execEnd O passes R err σ ρ))
    : execBlock O.mitRuhe passes R' (ruB (.bindAxiomElse (τ := zi_τ) a args he hr hw hg hd hgd err rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ) = ausR (execBlock O passes R (.bindAxiomElse (τ := zi_τ) a args he hr hw hg hd hgd err rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlock]
  erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwortSonst_ru]
  cases axiomAntwortSonst O a (σ.lese Λ args.orte)
    (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | mk σ' w =>
      rcases w with _ | v | r
      · rfl
      · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply]
        rw [ergWert_ru he, ← ausR_schrumpf, ← ih_execBlock_ru_rest σ' (Env.cons _ ρ)]
        rfl
      · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply, id]
        exact (congrArg (fun a => EndAusgang.zuAusgang (EndAusgang.schrumpf a))
          (ih_execEnd_ru_err σ' (Env.cons (τ := .why (D.agruende a)) r ρ))).trans
          ((congrArg EndAusgang.zuAusgang (endR_schrumpf _)).trans (endR_zuAusgang _))

set_option linter.unusedSectionVars false in
theorem execBlock_ru_regRead {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (r)
    (hk)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlock_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB rest) (worldR σ) (envR ρ) = ausR (execBlock O passes R rest σ ρ))
    : execBlock O.mitRuhe passes R' (ruB (.regRead r hk rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ) = ausR (execBlock O passes R (.regRead r hk rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlock]
  rw [worldR_fragt, regLies_mitRuhe, einpassen_ru O.zeiger O.mitRuhe.zeiger (zeiger_mitRuhe O)]
  cases einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) with
  | none => rfl
  | some v =>
      simp only [Option.map]
      erw [rzusage_mitRuhe]
      cases D.rzusage r v with
      | false => rfl
      | true =>
          simp only [if_true]
          rw [← ausR_schrumpf, ← ih_execBlock_ru_rest (σ.fragt (.inr (.inl r))) (Env.cons v ρ)]
          rfl

set_option linter.unusedSectionVars false in
theorem execBlock_ru_regReadElse {V : Vertrag D}
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
    (ih_execBlock_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB rest) (worldR σ) (envR ρ) = ausR (execBlock O passes R rest σ ρ))
    (ih_execEnd_ru_sonst : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd sonst) (worldR σ) (envR ρ) = endR (execEnd O passes R sonst σ ρ))
    : execBlock O.mitRuhe passes R' (ruB (.regReadElse r hk zusage sonst rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ) = ausR (execBlock O passes R (.regReadElse r hk zusage sonst rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlock]
  rw [worldR_fragt, regLies_mitRuhe, einpassen_ru O.zeiger O.mitRuhe.zeiger (zeiger_mitRuhe O)]
  cases einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) with
  | none => rfl
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
          rw [← endR_zuAusgang, ih_execEnd_ru_sonst _ ρ]
      | true =>
          simp only [wahr?, valR_bool, h, if_true]
          rw [← ausR_schrumpf, ← ih_execBlock_ru_rest _ (Env.cons v ρ)]
          rfl

set_option linter.unusedSectionVars false in
theorem execBlock_ru_awaits {V : Vertrag D}
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
    (ih_execBlock_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB rest) (worldR σ) (envR ρ) = ausR (execBlock O passes R rest σ ρ))
    : execBlock O.mitRuhe passes R' (ruB (.awaits g payload hp hL hat rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ) = ausR (execBlock O passes R (.awaits g payload hp hL hat rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlock]
  rw [worldR_fragt, sichtbar_mitRuhe]
  cases O.sichtbar g (σ.fragt (.inr (.inr g))) with
  | false => rfl
  | true =>
      simp only [if_true]
      rw [show ([Sum.inr g] : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) = [Sum.inr g] from rfl,
        lese_worldR, ← ausR_schrumpf, ← ih_execBlock_ru_rest _ (Env.cons _ ρ)]
      rfl

set_option linter.unusedSectionVars false in
theorem execBlock_ru_exchange {V : Vertrag D}
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
    (ih_execBlock_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB rest) (worldR σ) (envR ρ) = ausR (execBlock O passes R rest σ ρ))
    : execBlock O.mitRuhe passes R' (ruB (.exchange g neu hw hL rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ) = ausR (execBlock O passes R (.exchange g neu hw hL rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlock]
  erw [show (Sum.inr g :: (ruE neu).orte : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) =
    Sum.inr g :: neu.orte from congrArg (Sum.inr g :: ·) (ruE_orte neu), lese_worldR]
  have ez := eval_ru (σ.lese Λ (Sum.inr g :: neu.orte)) (σ.lese Λ (Sum.inr g :: neu.orte)) neu
    (Env.cons ((σ.lese Λ (Sum.inr g :: neu.orte)).globs g) ρ)
  change eval _ (ruE neu) _ (Env.cons (valR _ _) (envR ρ)) = _ at ez
  erw [show ((worldR (σ.lese Λ (Sum.inr g :: neu.orte))).globs g) =
    valR _ ((σ.lese Λ (Sum.inr g :: neu.orte)).globs g) from rfl, ez, schreibGlob_worldR,
    ← ausR_schrumpf, ← ih_execBlock_ru_rest _ (Env.cons _ ρ)]
  rfl

set_option linter.unusedSectionVars false in
theorem execBlock_ru_narrow {V : Vertrag D}
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
    (ih_execBlock_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB rest) (worldR σ) (envR ρ) = ausR (execBlock O passes R rest σ ρ))
    (ih_execEnd_ru_sonst : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd sonst) (worldR σ) (envR ρ) = endR (execEnd O passes R sonst σ ρ))
    : execBlock O.mitRuhe passes R' (ruB (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ) = ausR (execBlock O passes R (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlock]
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
      (execBlock O.mitRuhe passes R' (ruB rest) W
        (Env.cons (τ := .int lo' hi') ⟨z.n, h.1, h.2⟩ (envR ρ))).schrumpf
    else (execEnd O.mitRuhe passes R' (ruEnd sonst) W (envR ρ)).zuAusgang
  change branch ((worldR σ).lese (Λ.map resR) (ruE e).orte)
    (eval ((worldR σ).lese (Λ.map resR) (ruE e).orte) (ruE e)
      ((worldR σ).lese (Λ.map resR) (ruE e).orte) (envR ρ)) = _
  erw [hv, hread]
  dsimp only [branch]
  by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi'
  · erw [dif_pos hc, dif_pos hc]
    exact (congrArg Ausgang.schrumpf (ih_execBlock_ru_rest _
      (Env.cons (⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, hc.1, hc.2⟩ : Zahl lo' hi') ρ))).trans
      (ausR_schrumpf _)
  · erw [dif_neg hc, dif_neg hc, ← endR_zuAusgang, ih_execEnd_ru_sonst _ ρ]

set_option linter.unusedSectionVars false in
theorem execBlock_ru_narrowRequired {V : Vertrag D}
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
    (ih_execBlock_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB rest) (worldR σ) (envR ρ) = ausR (execBlock O passes R rest σ ρ))
    : execBlock O.mitRuhe passes R' (ruB (.narrowRequired (lo := zi_lo) (hi := zi_hi) e lo' hi' rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ) = ausR (execBlock O passes R (.narrowRequired (lo := zi_lo) (hi := zi_hi) e lo' hi' rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlock]
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
      (execBlock O.mitRuhe passes R' (ruB rest) W
        (Env.cons (τ := .int lo' hi') ⟨z.n, h.1, h.2⟩ (envR ρ))).schrumpf
    else .logik .kapazitaet
  change branch ((worldR σ).lese (Λ.map resR) (ruE e).orte)
    (eval ((worldR σ).lese (Λ.map resR) (ruE e).orte) (ruE e)
      ((worldR σ).lese (Λ.map resR) (ruE e).orte) (envR ρ)) = _
  erw [hv, hread]
  dsimp only [branch]
  by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi'
  · erw [dif_pos hc, dif_pos hc]
    exact (congrArg Ausgang.schrumpf (ih_execBlock_ru_rest _
      (Env.cons (⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, hc.1, hc.2⟩ : Zahl lo' hi') ρ))).trans
      (ausR_schrumpf _)
  · erw [dif_neg hc, dif_neg hc]
    rfl

set_option linter.unusedSectionVars false in
theorem execBlock_ru_bindAxiomOpt {V : Vertrag D}
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
    (ih_execBlock_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB rest) (worldR σ) (envR ρ) = ausR (execBlock O passes R rest σ ρ))
    : execBlock O.mitRuhe passes R' (ruB (.bindAxiomOpt (e := zi_e) a args he hp hd hgd rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ) = ausR (execBlock O passes R (.bindAxiomOpt (e := zi_e) a args he hp hd hgd rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  cases zi_e with
  | none =>
      simp only [ruB, execBlock]
      erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwort_ru]
      cases axiomAntwort O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ' w =>
          cases w with
          | none => rfl
          | some v =>
              simp only [Option.map, Ausgang.weiterOpt, ergEnv]
              dsimp only [sigR, Deklaration.asignatur]
              erw [execBlock_vorΛ]
              exact ih_execBlock_ru_rest σ' _
  | some τ =>
      simp only [ruB, execBlock]
      erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwort_ru]
      cases axiomAntwort O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ' w =>
          cases w with
          | none => rfl
          | some v =>
              simp only [Option.map, Ausgang.weiterOpt, ergEnv]
              erw [execBlock_vorΛ]
              have hv := ergTransport_ru he (congrArg (Option.map tyR) he) v
              have henv := congrArg
                (fun w : Wert D.mitRuhe (tyR τ) => Env.cons w (envR ρ)) hv
              exact (congrArg Ausgang.schrumpf
                ((congrArg (fun env => execBlock O.mitRuhe passes R' (ruB rest)
                    (worldR σ') env) henv).trans
                  (ih_execBlock_ru_rest σ'
                    (Env.cons (show ErgVal D (some τ) from he ▸ v) ρ)))).trans (ausR_schrumpf _)

set_option linter.unusedSectionVars false in
theorem execBlock_ru_bindAxiomOptElse {V : Vertrag D}
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
    (ih_execBlock_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB rest) (worldR σ) (envR ρ) = ausR (execBlock O passes R rest σ ρ))
    (ih_execEnd_ru_err : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd err) (worldR σ) (envR ρ) = endR (execEnd O passes R err σ ρ))
    : execBlock O.mitRuhe passes R' (ruB (.bindAxiomOptElse (e := zi_e) a args he hp hd hgd hr err rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ) = ausR (execBlock O passes R (.bindAxiomOptElse (e := zi_e) a args he hp hd hgd hr err rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  cases zi_e with
  | none =>
      simp only [ruB, execBlock]
      erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwortSonst_ru]
      cases axiomAntwortSonst O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ' w =>
          rcases w with _ | v | r
          · rfl
          · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply, id]
            simp only [Ausgang.weiterOpt, ergEnv]
            dsimp only [sigR, Deklaration.asignatur]
            erw [execBlock_vorΛ]
            exact ih_execBlock_ru_rest σ' _
          · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply, id,
              sigR, Deklaration.asignatur]
            erw [execEnd_umΛ]
            exact (congrArg (fun a => (EndAusgang.schrumpf a).zuAusgang)
              (ih_execEnd_ru_err σ' (Env.cons (τ := reasonTy (D.agruende a)) r ρ))).trans
              ((congrArg EndAusgang.zuAusgang (endR_schrumpf _)).trans (endR_zuAusgang _))
  | some τ =>
      simp only [ruB, execBlock]
      erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwortSonst_ru]
      cases axiomAntwortSonst O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ' w =>
          rcases w with _ | v | r
          · rfl
          · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply, id]
            simp only [Ausgang.weiterOpt, ergEnv]
            erw [execBlock_vorΛ]
            have hv := ergTransport_ru he (congrArg (Option.map tyR) he) v
            have henv := congrArg
              (fun w : Wert D.mitRuhe (tyR τ) => Env.cons w (envR ρ)) hv
            exact (congrArg Ausgang.schrumpf
              ((congrArg (fun env => execBlock O.mitRuhe passes R' (ruB rest)
                  (worldR σ') env) henv).trans
                (ih_execBlock_ru_rest σ'
                  (Env.cons (show ErgVal D (some τ) from he ▸ v) ρ)))).trans (ausR_schrumpf _)
          · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply, id,
              sigR, Deklaration.asignatur]
            erw [execEnd_umΛ]
            exact (congrArg (fun a => (EndAusgang.schrumpf a).zuAusgang)
              (ih_execEnd_ru_err σ' (Env.cons (τ := reasonTy (D.agruende a)) r ρ))).trans
              ((congrArg EndAusgang.zuAusgang (endR_schrumpf _)).trans (endR_zuAusgang _))

end Haupt
end Gabbro.Grammatik
