module

public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik.T3.Teil3Basis
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik.T2
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik.T3.Teil2

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Haupt
variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) → RufAusgang f)
  (hR : RufRu R R')
include hR
set_option linter.unusedSectionVars false in
theorem execEnd_ru_bind {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_τ}
    (e)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEnd_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd rest) (worldR σ) (envR ρ) = endR (execEnd O passes R rest σ ρ))
    : execEnd O.mitRuhe passes R' (ruEnd (.bind (τ := zi_τ) e rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ) = endR (execEnd O passes R (.bind (τ := zi_τ) e rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEnd]
  erw [ruE_orte, lese_worldR, eval_ru, ← endR_schrumpf, ← ih_execEnd_ru_rest _ _]
  rfl

set_option linter.unusedSectionVars false in
theorem execEnd_ru_bindCall {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_τ}
    (g)
    (args)
    (he)
    (hp)
    (hr)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEnd_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd rest) (worldR σ) (envR ρ) = endR (execEnd O passes R rest σ ρ))
    : execEnd O.mitRuhe passes R' (ruEnd (.bindCall (τ := zi_τ) g args he hp hr rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ) = endR (execEnd O passes R (.bindCall (τ := zi_τ) g args he hp hr rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEnd]
  erw [ruA_orte, lese_worldR, evalArgs_ru, hR]
  cases hx : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | ok σ' v =>
      try erw [hx]
      simp only [rufR]
      erw [execEnd_umΛ, ergWert_ru he]
      exact (congrArg EndAusgang.schrumpf (ih_execEnd_ru_rest σ' (Env.cons (ergWert he v) ρ))).trans
        (endR_schrumpf _)
  | why σ' r => exact (Fin.cast hr r).elim0
  | logik e => (try erw [hx]); rfl
  | hardware e => (try erw [hx]); rfl

set_option linter.unusedSectionVars false in
theorem execEnd_ru_bindCallElse {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_τ}
    (g)
    (args)
    (he)
    (hp)
    (hr)
    (err)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEnd_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd rest) (worldR σ) (envR ρ) = endR (execEnd O passes R rest σ ρ))
    (ih_execEnd_ru_err : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd err) (worldR σ) (envR ρ) = endR (execEnd O passes R err σ ρ))
    : execEnd O.mitRuhe passes R' (ruEnd (.bindCallElse (τ := zi_τ) g args he hp hr err rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ) = endR (execEnd O passes R (.bindCallElse (τ := zi_τ) g args he hp hr err rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEnd]
  erw [ruA_orte, lese_worldR, evalArgs_ru, hR]
  cases hx : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | ok σ' v =>
      try erw [hx]
      simp only [rufR]
      erw [execEnd_umΛ, ergWert_ru he]
      exact (congrArg EndAusgang.schrumpf (ih_execEnd_ru_rest σ' (Env.cons (ergWert he v) ρ))).trans
        (endR_schrumpf _)
  | why σ' r =>
      try erw [hx]
      simp only [rufR]
      erw [execEnd_umΛ]
      exact (congrArg EndAusgang.schrumpf (ih_execEnd_ru_err σ' (Env.cons r ρ))).trans
        (endR_schrumpf _)
  | logik e => (try erw [hx]); rfl
  | hardware e => (try erw [hx]); rfl

set_option linter.unusedSectionVars false in
theorem execEnd_ru_bindAxiom {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
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
    (ih_execEnd_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd rest) (worldR σ) (envR ρ) = endR (execEnd O passes R rest σ ρ))
    : execEnd O.mitRuhe passes R' (ruEnd (.bindAxiom (τ := zi_τ) a args he hw hg hd hgd rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ) = endR (execEnd O passes R (.bindAxiom (τ := zi_τ) a args he hw hg hd hgd rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEnd]
  erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwort_ru]
  cases axiomAntwort O a (σ.lese Λ args.orte)
    (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | mk σ' w =>
      cases w with
      | none => rfl
      | some v =>
          simp only [Option.map]
          rw [ergWert_ru he, ← endR_schrumpf, ← ih_execEnd_ru_rest σ' (Env.cons _ ρ)]
          rfl

set_option linter.unusedSectionVars false in
theorem execEnd_ru_bindAxiomElse {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
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
    (ih_execEnd_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd rest) (worldR σ) (envR ρ) = endR (execEnd O passes R rest σ ρ))
    (ih_execEnd_ru_err : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd err) (worldR σ) (envR ρ) = endR (execEnd O passes R err σ ρ))
    : execEnd O.mitRuhe passes R' (ruEnd (.bindAxiomElse (τ := zi_τ) a args he hr hw hg hd hgd err rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ) = endR (execEnd O passes R (.bindAxiomElse (τ := zi_τ) a args he hr hw hg hd hgd err rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEnd]
  erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwortSonst_ru]
  cases axiomAntwortSonst O a (σ.lese Λ args.orte)
    (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | mk σ' w =>
      rcases w with _ | v | r
      · rfl
      · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply]
        rw [ergWert_ru he, ← endR_schrumpf, ← ih_execEnd_ru_rest σ' (Env.cons _ ρ)]
        rfl
      · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply, id]
        rw [← endR_schrumpf, ← ih_execEnd_ru_err σ' (Env.cons (τ := .why (D.agruende a)) r ρ)]
        rfl

set_option linter.unusedSectionVars false in
theorem execEnd_ru_regRead {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (r)
    (hk)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEnd_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd rest) (worldR σ) (envR ρ) = endR (execEnd O passes R rest σ ρ))
    : execEnd O.mitRuhe passes R' (ruEnd (.regRead r hk rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ) = endR (execEnd O passes R (.regRead r hk rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEnd]
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
          rw [← endR_schrumpf, ← ih_execEnd_ru_rest (σ.fragt (.inr (.inl r))) (Env.cons v ρ)]
          rfl

set_option linter.unusedSectionVars false in
theorem execEnd_ru_regReadElse {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (r)
    (hk)
    (zusage)
    (sonst)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEnd_ru_sonst : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd sonst) (worldR σ) (envR ρ) = endR (execEnd O passes R sonst σ ρ))
    (ih_execEnd_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd rest) (worldR σ) (envR ρ) = endR (execEnd O passes R rest σ ρ))
    : execEnd O.mitRuhe passes R' (ruEnd (.regReadElse r hk zusage sonst rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ) = endR (execEnd O passes R (.regReadElse r hk zusage sonst rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEnd]
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
          exact ih_execEnd_ru_sonst _ ρ
      | true =>
          simp only [wahr?, valR_bool, h, if_true]
          rw [← endR_schrumpf, ← ih_execEnd_ru_rest _ (Env.cons v ρ)]
          rfl

set_option linter.unusedSectionVars false in
theorem execEnd_ru_awaits {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (g)
    (payload)
    (hp)
    (hL)
    (hat)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEnd_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd rest) (worldR σ) (envR ρ) = endR (execEnd O passes R rest σ ρ))
    : execEnd O.mitRuhe passes R' (ruEnd (.awaits g payload hp hL hat rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ) = endR (execEnd O passes R (.awaits g payload hp hL hat rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEnd]
  rw [worldR_fragt, sichtbar_mitRuhe]
  cases O.sichtbar g (σ.fragt (.inr (.inr g))) with
  | false => rfl
  | true =>
      simp only [if_true]
      rw [show ([Sum.inr g] : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) = [Sum.inr g] from rfl,
        lese_worldR, ← endR_schrumpf, ← ih_execEnd_ru_rest _ (Env.cons _ ρ)]
      rfl

omit hR in
set_option linter.unusedSectionVars false in
theorem execEnd_ru_bindAxiomOpt {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
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
    (ih_execEnd_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd rest) (worldR σ) (envR ρ) = endR (execEnd O passes R rest σ ρ))
    : execEnd O.mitRuhe passes R' (ruEnd (.bindAxiomOpt (e := zi_e) a args he hp hd hgd rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ) = endR (execEnd O passes R (.bindAxiomOpt (e := zi_e) a args he hp hd hgd rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  cases zi_e with
  | none =>
      simp only [ruEnd, execEnd]
      erw [execEnd_umΛ, ruA_orte, lese_worldR, evalArgs_ru, axiomAntwort_ru]
      cases axiomAntwort O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ' w =>
          cases w with
          | none => rfl
          | some v =>
              simp only [EndAusgang.weiterOpt, ergEnv]
              exact ih_execEnd_ru_rest σ' _
  | some τ =>
      simp only [ruEnd, execEnd]
      erw [execEnd_umΛ, ruA_orte, lese_worldR, evalArgs_ru, axiomAntwort_ru]
      cases axiomAntwort O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ' w =>
          cases w with
          | none => rfl
          | some v =>
              simp only [Option.map, EndAusgang.weiterOpt, ergEnv]
              rw [ergWert_ru he, ← endR_schrumpf, ← ih_execEnd_ru_rest σ' (Env.cons _ ρ)]
              rfl

omit hR in
set_option linter.unusedSectionVars false in
theorem execEnd_ru_bindAxiomOptElse {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
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
    (ih_execEnd_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd rest) (worldR σ) (envR ρ) = endR (execEnd O passes R rest σ ρ))
    (ih_execEnd_ru_err : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd err) (worldR σ) (envR ρ) = endR (execEnd O passes R err σ ρ))
    : execEnd O.mitRuhe passes R' (ruEnd (.bindAxiomOptElse (e := zi_e) a args he hp hd hgd hr err rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ) = endR (execEnd O passes R (.bindAxiomOptElse (e := zi_e) a args he hp hd hgd hr err rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  cases zi_e with
  | none =>
      simp only [ruEnd, execEnd]
      erw [execEnd_umΛ, ruA_orte, lese_worldR, evalArgs_ru, axiomAntwortSonst_ru]
      cases axiomAntwortSonst O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ' w =>
          rcases w with _ | v | r
          · rfl
          · simp only [EndAusgang.weiterOpt, ergEnv]
            exact ih_execEnd_ru_rest σ' _
          · erw [execEnd_umΛ]
            exact (congrArg (fun a => (EndAusgang.schrumpf a)) (ih_execEnd_ru_err σ' _)).trans
              (endR_schrumpf _)
  | some τ =>
      simp only [ruEnd, execEnd]
      erw [execEnd_umΛ, ruA_orte, lese_worldR, evalArgs_ru, axiomAntwortSonst_ru]
      cases axiomAntwortSonst O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ' w =>
          rcases w with _ | v | r
          · rfl
          · simp only [Option.map, EndAusgang.weiterOpt, ergEnv]
            rw [ergWert_ru he, ← endR_schrumpf, ← ih_execEnd_ru_rest σ' (Env.cons _ ρ)]
            rfl
          · erw [execEnd_umΛ]
            exact (congrArg (fun a => (EndAusgang.schrumpf a)) (ih_execEnd_ru_err σ' _)).trans
              (endR_schrumpf _)

end Haupt
end Gabbro.Grammatik
