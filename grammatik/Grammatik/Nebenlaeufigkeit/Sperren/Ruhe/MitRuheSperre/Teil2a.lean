module

public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSperre.Teil2

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
theorem execStmtH_ru_callInd {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (n)
    (p)
    (args)
    (hp)
    (hr)
    (σ : World D)
    (ρ : Env D Γ)
    : AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS (.callInd (n := n) p args hp hr : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtH S O U passes R (.callInd (n := n) p args hp hr : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS]
  erw [execStmtH_nachΛ]
  simp only [execStmtH]
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
        | ok σ' v => (try erw [hx]); exact Or.inl rfl
        | why σ' r => exact keinGrundSig hg hr r
        | logik e => (try erw [hx]); exact Or.inl rfl
        | hardware e => (try erw [hx]); exact Or.inl rfl
      · erw [h1, h2]
        exact Or.inr ⟨e', e, rfl, rfl, ht⟩

set_option linter.unusedSectionVars false in
theorem execStmtH_ru_callIndElse {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (n)
    (p)
    (args)
    (he)
    (hp)
    (hr)
    (err)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEndH_ru_err : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd err) (worldR σ) (envR ρ)) (execEndH S O U passes R err σ ρ))
    : AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS (.callIndElse (n := n) p args he hp hr err : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtH S O U passes R (.callIndElse (n := n) p args he hp hr err : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS]
  erw [execStmtH_nachΛ]
  simp only [execStmtH, indSonst]
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
        | ok σ' v => (try erw [hx]); exact Or.inl rfl
        | why σ' r =>
            try erw [hx]
            exact EndRel.zuAusgang (EndRel.schrumpf (ih_execEndH_ru_err σ' (Env.cons (grundSig hg r) ρ)))
        | logik e => (try erw [hx]); exact Or.inl rfl
        | hardware e => (try erw [hx]); exact Or.inl rfl
      · erw [h1, h2]
        exact Or.inr ⟨e', e, rfl, rfl, ht⟩

set_option linter.unusedSectionVars false in
theorem execStmtH_ru_locks {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (hr)
    (body)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockH_ru_body : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB body) (worldR σ) (envR ρ)) (execBlockH S O U passes R body σ ρ))
    : AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS (.locks L hr body : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtH S O U passes R (.locks L hr body : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmtH]
  rw [hU, nimmt_worldR]
  exact AusRelRu.frei S L (ih_execBlockH_ru_body ((U L σ).nimmt L) ρ)

set_option linter.unusedSectionVars false in
theorem execStmtH_ru_traverse {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (t)
    (inv)
    (body)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockH_ru_body : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB body) (worldR σ) (envR ρ)) (execBlockH S O U passes R body σ ρ))
    : AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS (.traverse t inv body : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtH S O U passes R (.traverse t inv body : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmtH]
  have hL := traverseLauf_rel (l := l) (fun σ ρ => execBlockH S O U passes R body σ ρ)
    (fun σ ρ => execBlockH S.mitRuhe O' U' passes R' (ruB body) σ ρ)
    (fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ)))
    (fun σ ρ => (σ.lese (Λ.map resR) (ruE inv).orte,
      wahr? (eval (σ.lese (Λ.map resR) (ruE inv).orte) (ruE inv)
        (σ.lese (Λ.map resR) (ruE inv).orte) ρ)))
    (fun σ ρ => ih_execBlockH_ru_body σ ρ)
    (fun σ ρ => by simp only [ruE_orte, lese_worldR, eval_ru, valR_bool, wahr?])
    (alleIndizes (D.count t)) σ ρ
  rw [map_valR_int] at hL
  exact hL

set_option linter.unusedSectionVars false in
theorem execStmtH_ru_consumeTraverse {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (t)
    (member)
    (edge)
    (inv)
    (bound)
    (mass)
    (body)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockH_ru_body : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB body) (worldR σ) (envR ρ)) (execBlockH S O U passes R body σ ρ))
    : AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS (.consumeTraverse t member edge inv bound mass body : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtH S O U passes R (.consumeTraverse t member edge inv bound mass body : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmtH]
  have hL := traverseLauf_rel (l := l) (fun σ ρ => execBlockH S O U passes R body σ ρ)
    (fun σ ρ => execBlockH S.mitRuhe O' U' passes R' (ruB body) σ ρ)
    (fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ)))
    (fun σ ρ => (σ.lese (Λ.map resR) (ruE inv).orte,
      wahr? (eval (σ.lese (Λ.map resR) (ruE inv).orte) (ruE inv)
        (σ.lese (Λ.map resR) (ruE inv).orte) ρ)))
    (fun σ ρ => ih_execBlockH_ru_body σ ρ)
    (fun σ ρ => by simp only [ruE_orte, lese_worldR, eval_ru, valR_bool, wahr?])
    (alleIndizes (D.count t)) σ ρ
  rw [map_valR_int] at hL
  exact hL

set_option linter.unusedSectionVars false in
theorem execStmtH_ru_retry {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (n)
    (bis)
    (body)
    (ueber)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockH_ru_body : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB body) (worldR σ) (envR ρ)) (execBlockH S O U passes R body σ ρ))
    (ih_execBlockH_ru_ueber : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB ueber) (worldR σ) (envR ρ)) (execBlockH S O U passes R ueber σ ρ))
    : AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS (.retry n bis body ueber : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtH S O U passes R (.retry n bis body ueber : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmtH]
  exact retryLauf_rel (fun σ ρ => execBlockH S O U passes R body σ ρ)
    (fun σ ρ => execBlockH S.mitRuhe O' U' passes R' (ruB body) σ ρ)
    (fun σ ρ => (σ.lese Λ bis.orte, wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ)))
    (fun σ ρ => (σ.lese (Λ.map resR) (ruE bis).orte,
      wahr? (eval (σ.lese (Λ.map resR) (ruE bis).orte) (ruE bis)
        (σ.lese (Λ.map resR) (ruE bis).orte) ρ)))
    (fun σ ρ => execBlockH S O U passes R ueber σ ρ)
    (fun σ ρ => execBlockH S.mitRuhe O' U' passes R' (ruB ueber) σ ρ)
    (fun σ ρ => ih_execBlockH_ru_body σ ρ)
    (fun σ ρ => by simp only [ruE_orte, lese_worldR, eval_ru, valR_bool, wahr?])
    (fun σ ρ => ih_execBlockH_ru_ueber σ ρ) n σ ρ

set_option linter.unusedSectionVars false in
theorem execStmtH_ru_forever {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (a)
    (inv)
    (body)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockH_ru_body : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB body) (worldR σ) (envR ρ)) (execBlockH S O U passes R body σ ρ))
    : AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS (.forever a inv body : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtH S O U passes R (.forever a inv body : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmtH]
  exact foreverLauf_rel a (fun σ ρ => execBlockH S O U passes R body σ ρ)
    (fun σ ρ => execBlockH S.mitRuhe O' U' passes R' (ruB body) σ ρ)
    (fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ)))
    (fun σ ρ => (σ.lese (Λ.map resR) (ruE inv).orte,
      wahr? (eval (σ.lese (Λ.map resR) (ruE inv).orte) (ruE inv)
        (σ.lese (Λ.map resR) (ruE inv).orte) ρ)))
    (fun σ ρ => ih_execBlockH_ru_body σ ρ)
    (fun σ ρ => by simp only [ruE_orte, lese_worldR, eval_ru, valR_bool, wahr?]) passes σ ρ

set_option linter.unusedSectionVars false in
theorem execStmtH_ru_axiomCall {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (a)
    (args)
    (h)
    (hw)
    (hg)
    (hd)
    (hgd)
    (σ : World D)
    (ρ : Env D Γ)
    : AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS (.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtH S O U passes R (.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ _) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruS, execStmtH]
  erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwort_ruG hO]
  cases axiomAntwort O a (σ.lese Λ args.orte)
    (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | mk σ' w =>
      cases w with
      | none => rfl
      | some _ => rfl

set_option linter.unusedSectionVars false in
theorem execStmtH_ru_axiomCallElse {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (e)
    (a)
    (args)
    (he)
    (hp)
    (hd)
    (hgd)
    (hr)
    (err)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEndH_ru_err : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd err) (worldR σ) (envR ρ)) (execEndH S O U passes R err σ ρ))
    : AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS (.axiomCallElse e a args he hp hd hgd hr err : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtH S O U passes R (.axiomCallElse e a args he hp hd hgd hr err : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS]
  erw [execStmtH_nachΛ]
  simp only [execStmtH]
  erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwortSonst_ruG hO]
  cases axiomAntwortSonst O a (σ.lese Λ args.orte)
    (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | mk σ' w =>
      rcases w with _ | v | r
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact EndRel.zuAusgang (EndRel.schrumpf
          (ih_execEndH_ru_err σ' (Env.cons (τ := reasonTy (D.agruende a)) r ρ)))

set_option linter.unusedSectionVars false in
theorem execStmtH_ru_regWrite {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (r)
    (hk)
    (e)
    (σ : World D)
    (ρ : Env D Γ)
    : AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS (.regWrite r hk e : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtH S O U passes R (.regWrite r hk e : Stmt D V l Γ Λ _) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruS, execStmtH]
  rw [ruE_orte, lese_worldR]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmtH_ru_publish {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (g)
    (e)
    (payload)
    (hp)
    (hw)
    (hL)
    (σ : World D)
    (ρ : Env D Γ)
    : AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS (.publish g e payload hp hw hL : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtH S O U passes R (.publish g e payload hp hw hL : Stmt D V l Γ Λ _) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruS, execStmtH]
  rw [ruE_orte, lese_worldR, eval_ru, schreibGlob_worldR]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmtH_ru_ret {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (e)
    (hΛ)
    (σ : World D)
    (ρ : Env D Γ)
    : AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS (.ret e hΛ : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtH S O U passes R (.ret e hΛ : Stmt D V l Γ Λ _) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruS, execStmtH]
  erw [ruErg_orte, lese_worldR, evalErg_ru]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmtH_ru_retScoped {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (e)
    (R)
    (σ : World D)
    (ρ : Env D Γ)
    : AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS (.retScoped e R : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtH S O U passes R (.retScoped e R : Stmt D V l Γ Λ _) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruS, execStmtH]
  erw [ruErg_orte, lese_worldR, evalErg_ru]
  rfl

set_option linter.unusedSectionVars false in
theorem execBlockH_ru_cons {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_Λ'}
    (s)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execStmtH_ru_s : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS s) (worldR σ) (envR ρ)) (execStmtH S O U passes R s σ ρ))
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.cons (Λ' := zi_Λ') s rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.cons (Λ' := zi_Λ') s rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH]
  rcases ih_execStmtH_ru_s σ ρ with h | ⟨e', e, h1, h2, ht⟩
  · rw [h]
    cases execStmtH S O U passes R s σ ρ with
    | ok σ' ρ' => exact ih_execBlockH_ru_rest σ' ρ'
    | _ => exact Or.inl rfl
  · rw [h1, h2]
    exact Or.inr ⟨e', e, rfl, rfl, ht⟩

end Haupt
end Gabbro.Grammatik
