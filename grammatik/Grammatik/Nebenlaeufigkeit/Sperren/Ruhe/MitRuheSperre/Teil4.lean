module

public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSperre.Teil3

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
theorem execBlockH_ru_floatLit {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (q)
    (lo)
    (hi)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.floatLit q lo hi rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.floatLit q lo hi rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH]
  cases gleitPasst lo hi (bruch q) with
  | none => exact Or.inl rfl
  | some v => exact AusRelRu.schrumpf (ih_execBlockH_ru_rest _ (Env.cons v ρ))

set_option linter.unusedSectionVars false in
theorem execBlockH_ru_floatOf {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_l1}
    {zi_h1}
    (e)
    (lo)
    (hi)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH]
  rw [ruE_orte, lese_worldR, eval_ru]
  try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
  cases gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n) with
  | none => exact Or.inl rfl
  | some v => exact AusRelRu.schrumpf (ih_execBlockH_ru_rest _ (Env.cons v ρ))

set_option linter.unusedSectionVars false in
theorem execBlockH_ru_floatNarrow {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_l1}
    {zi_h1}
    (e)
    (lo)
    (hi)
    (sonst)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    (ih_execEndH_ru_sonst : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd sonst) (worldR σ) (envR ρ)) (execEndH S O U passes R sonst σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH]
  rw [ruE_orte, lese_worldR, eval_ru]
  try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
  cases gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x with
  | none => exact EndRel.zuAusgang (ih_execEndH_ru_sonst _ ρ)
  | some v => exact AusRelRu.schrumpf (ih_execBlockH_ru_rest _ (Env.cons v ρ))

set_option linter.unusedSectionVars false in
theorem execEndH_ru_ret {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (e)
    (hΛ)
    (σ : World D)
    (ρ : Env D Γ)
    : EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd (.ret e hΛ : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndH S O U passes R (.ret e hΛ : Endblock D V l Γ Λ) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruEnd, execEndH]
  erw [ruErg_orte, lese_worldR, evalErg_ru]
  rfl

set_option linter.unusedSectionVars false in
theorem execEndH_ru_retScoped {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (e)
    (R)
    (σ : World D)
    (ρ : Env D Γ)
    : EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd (.retScoped e R : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndH S O U passes R (.retScoped e R : Endblock D V l Γ Λ) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruEnd, execEndH]
  erw [ruErg_orte, lese_worldR, evalErg_ru]
  rw [gibt_foldl_worldR]
  rfl

set_option linter.unusedSectionVars false in
theorem execEndH_ru_retWhyScoped {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (r)
    (R)
    (σ : World D)
    (ρ : Env D Γ)
    : EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd (.retWhyScoped r R : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndH S O U passes R (.retWhyScoped r R : Endblock D V l Γ Λ) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruEnd, execEndH]
  rw [gibt_foldl_worldR]

set_option linter.unusedSectionVars false in
theorem execEndH_ru_cons {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_Λ'}
    (s)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execStmtH_ru_s : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS s) (worldR σ) (envR ρ)) (execStmtH S O U passes R s σ ρ))
    (ih_execEndH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndH S O U passes R rest σ ρ))
    : EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd (.cons (Λ' := zi_Λ') s rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndH S O U passes R (.cons (Λ' := zi_Λ') s rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndH]
  rcases ih_execStmtH_ru_s σ ρ with h | ⟨e', e, h1, h2, ht⟩
  · rw [h]
    cases execStmtH S O U passes R s σ ρ with
    | ok σ' ρ' => exact ih_execEndH_ru_rest σ' ρ'
    | _ => exact Or.inl rfl
  · rw [h1, h2]
    exact Or.inr ⟨e', e, rfl, rfl, ht⟩

set_option linter.unusedSectionVars false in
theorem execEndH_ru_bind {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_τ}
    (e)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEndH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndH S O U passes R rest σ ρ))
    : EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd (.bind (τ := zi_τ) e rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndH S O U passes R (.bind (τ := zi_τ) e rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndH]
  rw [ruE_orte, lese_worldR, eval_ru]
  exact EndRel.schrumpf (ih_execEndH_ru_rest (σ.lese Λ e.orte)
    (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ))

set_option linter.unusedSectionVars false in
theorem execEndH_ru_bindCall {V : Vertrag D}
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
    (ih_execEndH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndH S O U passes R rest σ ρ))
    : EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd (.bindCall (τ := zi_τ) g args he hp hr rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndH S O U passes R (.bindCall (τ := zi_τ) g args he hp hr rest : Endblock D V l Γ Λ) σ ρ) :=
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
    | why σ' r => exact (Fin.cast hr r).elim0
    | logik e => (try erw [hx]); exact Or.inl rfl
    | hardware e => (try erw [hx]); exact Or.inl rfl
  · erw [h1, h2]
    exact Or.inr ⟨e', e, rfl, rfl, ht⟩

set_option linter.unusedSectionVars false in
theorem execEndH_ru_bindAxiomOpt {V : Vertrag D}
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
    (ih_execEndH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndH S O U passes R rest σ ρ))
    : EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd (.bindAxiomOpt (e := zi_e) a args he hp hd hgd rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndH S O U passes R (.bindAxiomOpt (e := zi_e) a args he hp hd hgd rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  cases zi_e with
  | none =>
      simp only [ruEnd, execEndH]
      erw [execEndH_umΛ, ruA_orte, lese_worldR, evalArgs_ru, axiomAntwort_ruG hO]
      cases axiomAntwort O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ' w =>
          cases w with
          | none => exact Or.inl rfl
          | some v =>
              simp only [EndAusgang.weiterOpt, ergEnv]
              exact ih_execEndH_ru_rest σ' _
  | some τ =>
      simp only [ruEnd, execEndH]
      erw [execEndH_umΛ, ruA_orte, lese_worldR, evalArgs_ru, axiomAntwort_ruG hO]
      cases axiomAntwort O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ' w =>
          cases w with
          | none => exact Or.inl rfl
          | some v =>
              simp only [Option.map, EndAusgang.weiterOpt, ergEnv]
              rw [ergWert_ru he]
              exact EndRel.schrumpf (ih_execEndH_ru_rest σ' (Env.cons _ ρ))

set_option linter.unusedSectionVars false in
theorem execEndH_ru_bindAxiomOptElse {V : Vertrag D}
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
    (ih_execEndH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndH S O U passes R rest σ ρ))
    (ih_execEndH_ru_err : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd err) (worldR σ) (envR ρ)) (execEndH S O U passes R err σ ρ))
    : EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd (.bindAxiomOptElse (e := zi_e) a args he hp hd hgd hr err rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndH S O U passes R (.bindAxiomOptElse (e := zi_e) a args he hp hd hgd hr err rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  cases zi_e with
  | none =>
      simp only [ruEnd, execEndH]
      erw [execEndH_umΛ, ruA_orte, lese_worldR, evalArgs_ru, axiomAntwortSonst_ruG hO]
      cases axiomAntwortSonst O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ' w =>
          rcases w with _ | v | r
          · exact Or.inl rfl
          · simp only [EndAusgang.weiterOpt, ergEnv]
            exact ih_execEndH_ru_rest σ' _
          · simp only [EndAusgang.weiterOpt, ergEnv]
            erw [execEndH_umΛ]
            exact EndRel.schrumpf (ih_execEndH_ru_err σ' _)
  | some τ =>
      simp only [ruEnd, execEndH]
      erw [execEndH_umΛ, ruA_orte, lese_worldR, evalArgs_ru, axiomAntwortSonst_ruG hO]
      cases axiomAntwortSonst O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ' w =>
          rcases w with _ | v | r
          · exact Or.inl rfl
          · simp only [Option.map, EndAusgang.weiterOpt, ergEnv]
            rw [ergWert_ru he]
            exact EndRel.schrumpf (ih_execEndH_ru_rest σ' (Env.cons _ ρ))
          · simp only [Option.map, EndAusgang.weiterOpt, ergEnv]
            erw [execEndH_umΛ]
            exact EndRel.schrumpf (ih_execEndH_ru_err σ' _)


end Haupt
end Gabbro.Grammatik
