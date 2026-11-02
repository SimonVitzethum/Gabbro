module

public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSperre.Teil4

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Haupt
variable (S : SperrInv D) (O : Orakel D) (O' : Orakel D.mitRuhe) (hO : OrakelRu O O')
  (U : Umwelt D) (U' : Umwelt D.mitRuhe) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) → RufAusgang f)
  (hU : ∀ L σ, U' L (worldR σ) = worldR (U L σ))
  (hR : RufRel R R')
include hO hU hR

set_option linter.unusedSectionVars false in
theorem execEndH_ru_bindCallElse {V : Vertrag D}
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
    (ih_execEndH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndH S O U passes R rest σ ρ))
    (ih_execEndH_ru_err : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd err) (worldR σ) (envR ρ)) (execEndH S O U passes R err σ ρ))
    : EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd (.bindCallElse (τ := zi_τ) g args he hp hr err rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndH S O U passes R (.bindCallElse (τ := zi_τ) g args he hp hr err rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndH]
  erw [ruA_orte, lese_worldR, evalArgs_ru]
  rcases hR g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
    with hx' | ⟨e', e, h1, h2, ht⟩
  · erw [hx']
    cases hx : R g (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
    | ok σ' v =>
        try erw [hx]
        simp only [rufR]
        erw [execEndH_umΛ, ergWert_ru he]
        exact EndRel.schrumpf (ih_execEndH_ru_rest σ' (Env.cons (ergWert he v) ρ))
    | why σ' r =>
        try erw [hx]
        simp only [rufR]
        erw [execEndH_umΛ]
        exact EndRel.schrumpf (ih_execEndH_ru_err σ' (Env.cons r ρ))
    | logik e => (try erw [hx]); exact Or.inl rfl
    | hardware e => (try erw [hx]); exact Or.inl rfl
  · erw [h1, h2]
    exact Or.inr ⟨e', e, rfl, rfl, ht⟩

set_option linter.unusedSectionVars false in
theorem execEndH_ru_bindAxiom {V : Vertrag D}
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
    (ih_execEndH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndH S O U passes R rest σ ρ))
    : EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd (.bindAxiom (τ := zi_τ) a args he hw hg hd hgd rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndH S O U passes R (.bindAxiom (τ := zi_τ) a args he hw hg hd hgd rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndH]
  erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwort_ruG hO]
  cases axiomAntwort O a (σ.lese Λ args.orte)
    (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | mk σ' w =>
      cases w with
      | none => exact Or.inl rfl
      | some v =>
          simp only [Option.map]
          rw [ergWert_ru he]
          exact EndRel.schrumpf (ih_execEndH_ru_rest σ' (Env.cons (ergWert he v) ρ))

set_option linter.unusedSectionVars false in
theorem execEndH_ru_bindAxiomElse {V : Vertrag D}
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
    (ih_execEndH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndH S O U passes R rest σ ρ))
    (ih_execEndH_ru_err : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd err) (worldR σ) (envR ρ)) (execEndH S O U passes R err σ ρ))
    : EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd (.bindAxiomElse (τ := zi_τ) a args he hr hw hg hd hgd err rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndH S O U passes R (.bindAxiomElse (τ := zi_τ) a args he hr hw hg hd hgd err rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndH]
  erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwortSonst_ruG hO]
  cases axiomAntwortSonst O a (σ.lese Λ args.orte)
    (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | mk σ' w =>
      rcases w with _ | v | r
      · exact Or.inl rfl
      · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply]
        rw [ergWert_ru he]
        exact EndRel.schrumpf (ih_execEndH_ru_rest σ' (Env.cons (ergWert he v) ρ))
      · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply, id]
        exact EndRel.schrumpf (ih_execEndH_ru_err σ' (Env.cons (τ := .why (D.agruende a)) r ρ))

set_option linter.unusedSectionVars false in
theorem execEndH_ru_regRead {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (r)
    (hk)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEndH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndH S O U passes R rest σ ρ))
    : EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd (.regRead r hk rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndH S O U passes R (.regRead r hk rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndH]
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
          exact EndRel.schrumpf (ih_execEndH_ru_rest (σ.fragt (.inr (.inl r))) (Env.cons v ρ))

set_option linter.unusedSectionVars false in
theorem execEndH_ru_regReadElse {V : Vertrag D}
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
    (ih_execEndH_ru_sonst : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd sonst) (worldR σ) (envR ρ)) (execEndH S O U passes R sonst σ ρ))
    (ih_execEndH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndH S O U passes R rest σ ρ))
    : EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd (.regReadElse r hk zusage sonst rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndH S O U passes R (.regReadElse r hk zusage sonst rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndH]
  rw [worldR_fragt, hO.regLies, einpassen_ru O.zeiger O'.zeiger hO.zeiger]
  cases einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) with
  | none => exact Or.inl rfl
  | some v =>
      simp only [Option.map]
      rw [ruE_orte, lese_worldR]
      have ez := eval_ru ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) zusage (Env.cons v ρ)
      change eval _ (ruE zusage) _ (Env.cons (valR _ v) (envR ρ)) = _ at ez
      rw [ez]
      cases h : (eval ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) zusage ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) (Env.cons v ρ) : Bool) with
      | false =>
          simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
          exact ih_execEndH_ru_sonst _ ρ
      | true =>
          simp only [wahr?, valR_bool, h, if_true]
          exact EndRel.schrumpf (ih_execEndH_ru_rest _ (Env.cons v ρ))

set_option linter.unusedSectionVars false in
theorem execEndH_ru_awaits {V : Vertrag D}
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
    (ih_execEndH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndH S O U passes R rest σ ρ))
    : EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd (.awaits g payload hp hL hat rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndH S O U passes R (.awaits g payload hp hL hat rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndH]
  rw [worldR_fragt, hO.sichtbar]
  cases O.sichtbar g (σ.fragt (.inr (.inr g))) with
  | false => exact Or.inl rfl
  | true =>
      simp only [if_true]
      rw [show ([Sum.inr g] : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) = [Sum.inr g] from rfl,
        lese_worldR]
      exact EndRel.schrumpf (ih_execEndH_ru_rest ((σ.fragt (.inr (.inr g))).lese Λ [Sum.inr g])
        (Env.cons (((σ.fragt (.inr (.inr g))).lese Λ [Sum.inr g]).globs g) ρ))

set_option linter.unusedSectionVars false in
theorem execEndH_ru_bindCallInd {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_τ}
    (n)
    (p)
    (args)
    (he)
    (hp)
    (hr)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEndH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndH S O U passes R rest σ ρ))
    : EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd (.bindCallInd (τ := zi_τ) (n := n) p args he hp hr rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndH S O U passes R (.bindCallInd (τ := zi_τ) (n := n) p args he hp hr rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndH]
  erw [show (ruE p).orte ++ (ruA args).orte = p.orte ++ args.orte from
    kongr₂ (· ++ ·) (ruE_orte p) (ruA_orte args)]
  erw [lese_worldR, eval_ru, evalArgs_ru]
  cases h : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ with
  | mk g hg =>
      rw [valR_fnptr]
      dsimp only
      erw [umsig_ru hg]
      rcases hR g (σ.lese Λ (p.orte ++ args.orte)) (umsig hg (evalArgs
          (σ.lese Λ (p.orte ++ args.orte)) args (σ.lese Λ (p.orte ++ args.orte)) ρ))
        with hx' | ⟨e', e, h1, h2, ht⟩
      · erw [hx']
        cases hx : R g (σ.lese Λ (p.orte ++ args.orte)) (umsig hg (evalArgs
            (σ.lese Λ (p.orte ++ args.orte)) args (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
        | ok σ' v =>
            try erw [hx]
            simp only [rufR]
            erw [execEndH_umΛ, ergWert_ru (ergSig hg he)]
            exact EndRel.schrumpf
              (ih_execEndH_ru_rest σ' (Env.cons (ergWert (ergSig hg he) v) ρ))
        | why σ' r => exact keinGrundSig hg hr r
        | logik e => (try erw [hx]); exact Or.inl rfl
        | hardware e => (try erw [hx]); exact Or.inl rfl
      · erw [h1, h2]
        exact Or.inr ⟨e', e, rfl, rfl, ht⟩

set_option linter.unusedSectionVars false in
theorem execEndH_ru_narrow {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_lo}
    {zi_hi}
    (e)
    (lo')
    (hi')
    (sonst)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEndH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndH S O U passes R rest σ ρ))
    (ih_execEndH_ru_sonst : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd sonst) (worldR σ) (envR ρ)) (execEndH S O U passes R sonst σ ρ))
    : EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndH S O U passes R (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndH]
  simp only [ruE_orte, lese_worldR, eval_ru, valR_int]
  by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi'
  · erw [dif_pos hc, dif_pos hc]
    exact EndRel.schrumpf (ih_execEndH_ru_rest _
      (Env.cons (⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, hc.1, hc.2⟩ : Zahl lo' hi') ρ))
  · erw [dif_neg hc, dif_neg hc]
    exact ih_execEndH_ru_sonst _ ρ

set_option linter.unusedSectionVars false in
theorem execEndH_ru_narrowRequired {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_lo}
    {zi_hi}
    (e)
    (lo')
    (hi')
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEndH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndH S O U passes R rest σ ρ))
    : EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd (.narrowRequired (lo := zi_lo) (hi := zi_hi) e lo' hi' rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndH S O U passes R (.narrowRequired (lo := zi_lo) (hi := zi_hi) e lo' hi' rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndH]
  simp only [ruE_orte, lese_worldR, eval_ru, valR_int]
  by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi'
  · erw [dif_pos hc, dif_pos hc]
    exact EndRel.schrumpf (ih_execEndH_ru_rest _
      (Env.cons (⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, hc.1, hc.2⟩ : Zahl lo' hi') ρ))
  · erw [dif_neg hc, dif_neg hc]
    exact Or.inl rfl

end Haupt
end Gabbro.Grammatik
