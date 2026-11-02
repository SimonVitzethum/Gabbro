module
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik.T3.Teil2a

public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik.T2
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik.T3.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Haupt
variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
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
      rw [ruE_orte, lese_worldR]
      have ez := eval_ru ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) zusage (Env.cons v ρ)
      change eval _ (ruE zusage) _ (Env.cons (valR _ v) (envR ρ)) = _ at ez
      rw [ez]
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
  rw [show (Sum.inr g :: (ruE neu).orte : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) =
    Sum.inr g :: neu.orte from congrArg (Sum.inr g :: ·) (ruE_orte neu), lese_worldR]
  have ez := eval_ru (σ.lese Λ (Sum.inr g :: neu.orte)) (σ.lese Λ (Sum.inr g :: neu.orte)) neu
    (Env.cons ((σ.lese Λ (Sum.inr g :: neu.orte)).globs g) ρ)
  change eval _ (ruE neu) _ (Env.cons (valR _ _) (envR ρ)) = _ at ez
  rw [show ((worldR (σ.lese Λ (Sum.inr g :: neu.orte))).globs g) =
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
  simp only [ruE_orte, lese_worldR, eval_ru, valR_int]
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
  simp only [ruE_orte, lese_worldR, eval_ru, valR_int]
  by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi'
  · erw [dif_pos hc, dif_pos hc]
    exact (congrArg Ausgang.schrumpf (ih_execBlock_ru_rest _
      (Env.cons (⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, hc.1, hc.2⟩ : Zahl lo' hi') ρ))).trans
      (ausR_schrumpf _)
  · erw [dif_neg hc, dif_neg hc]
    exact Or.inl rfl

end Haupt
end Gabbro.Grammatik
