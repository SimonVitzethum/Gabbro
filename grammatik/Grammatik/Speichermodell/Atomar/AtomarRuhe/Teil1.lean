/-
  File:      Grammatik/Speichermodell/AtomarRuhe.lean
  Subject:   The idle root (MitRuhe.lean) and the semantics with the atomic rely: a body of
             `P.mitRuhe` under `execStmtHA` runs as the body of `P`, the atomic environment
             translated like the lock move (`hA`). The copy of MitRuheSperre.lean §4/§5 over
             `execStmtHA`. Opus lane O25b, 2026-09-26. Standalone.
-/
module
public import Grammatik.Speichermodell.Atomar.AtomarRuhe.Teil1a
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSperre
public import Grammatik.Speichermodell.Maschine.SperreSemA
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

section HauptA

variable (S : SperrInv D) (O : Orakel D) (O' : Orakel D.mitRuhe) (hO : OrakelRu O O')
  (U : Umwelt D) (U' : Umwelt D.mitRuhe) (A : AUmwelt D) (A' : AUmwelt D.mitRuhe) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) → RufAusgang f)
  (hU : ∀ L σ, U' L (worldR σ) = worldR (U L σ))
  (hA : ∀ X σ, A' X (worldR σ) = worldR (A X σ))
  (hR : RufRel R R')

include hO hU hA hR

set_option linter.unusedSectionVars false in
theorem execStmtHA_ru_ite {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (c)
    (t)
    (e)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockHA_ru_e : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB e) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R e σ ρ))
    (ih_execBlockHA_ru_t : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB t) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R t σ ρ))
    : AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS (.ite c t e : Stmt D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R (.ite c t e : Stmt D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruS, execStmtHA]
  rw [ruE_orte, leseA_worldR hA, eval_ru]
  cases h : (eval (leseA A σ Λ c.orte) c (leseA A σ Λ c.orte) ρ : Bool)
  · simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
    exact ih_execBlockHA_ru_e _ ρ
  · simp only [wahr?, valR_bool, h, if_true]
    exact ih_execBlockHA_ru_t _ ρ

set_option linter.unusedSectionVars false in
theorem execStmtHA_ru_onOption {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_n}
    (o)
    (p)
    (a)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockHA_ru_a : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB a) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R a σ ρ))
    (ih_execBlockHA_ru_p : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB p) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R p σ ρ))
    : AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS (.onOption (n := zi_n) o p a : Stmt D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R (.onOption (n := zi_n) o p a : Stmt D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruS, execStmtHA]
  rw [ruE_orte, leseA_worldR hA, eval_ru]
  try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
  cases h : eval (leseA A σ Λ o.orte) o (leseA A σ Λ o.orte) ρ with
  | none => exact ih_execBlockHA_ru_a _ ρ
  | some k =>
      simp only
      exact AusRelRu.schrumpf (ih_execBlockHA_ru_p _ (Env.cons k ρ))

set_option linter.unusedSectionVars false in
theorem execStmtHA_ru_onTag {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_cs}
    (v)
    (arms)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execArmsHA_ru_arms : ∀ (v : Wert D (.sum _)), ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execArmsHA S.mitRuhe O' U' A' passes R' (ruArms arms) (valR (.sum _) v) (worldR σ) (envR ρ)) (execArmsHA S O U A passes R arms v σ ρ))
    : AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS (.onTag (cs := zi_cs) v arms : Stmt D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R (.onTag (cs := zi_cs) v arms : Stmt D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruS, execStmtHA]
  rw [ruE_orte, leseA_worldR hA, eval_ru]
  exact ih_execArmsHA_ru_arms _ _ ρ

set_option linter.unusedSectionVars false in
theorem execStmtHA_ru_onWhy {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_n}
    (r)
    (arms)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execGrundHA_ru_arms : ∀ (r : Fin _), ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execGrundHA S.mitRuhe O' U' A' passes R' (ruGArms arms) r (worldR σ) (envR ρ)) (execGrundHA S O U A passes R arms r σ ρ))
    : AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS (.onWhy (n := zi_n) r arms : Stmt D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R (.onWhy (n := zi_n) r arms : Stmt D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruS, execStmtHA]
  rw [ruE_orte, leseA_worldR hA, eval_ru]
  exact ih_execGrundHA_ru_arms _ _ ρ

set_option linter.unusedSectionVars false in
theorem execStmtHA_ru_call {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (g)
    (args)
    (hp)
    (hr)
    (σ : World D)
    (ρ : Env D Γ)
    : AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS (.call g args hp hr : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R (.call g args hp hr : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS]
  erw [execStmtHA_nachΛ]
  simp only [execStmtHA]
  erw [ruA_orte, leseA_worldR hA, evalArgs_ru]
  rcases hR g (leseA A σ Λ args.orte) (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ)
    with hx' | ⟨e', e, h1, h2, ht⟩
  · erw [hx']
    cases hx : R g (leseA A σ Λ args.orte)
        (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ) with
    | ok σ' v => (try erw [hx]); exact Or.inl rfl
    | why σ' r => exact (Fin.cast hr r).elim0
    | logik e => (try erw [hx]); exact Or.inl rfl
    | hardware e => (try erw [hx]); exact Or.inl rfl
  · erw [h1, h2]
    exact Or.inr ⟨e', e, rfl, rfl, ht⟩

set_option linter.unusedSectionVars false in
theorem execStmtHA_ru_callInd {V : Vertrag D}
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
    : AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS (.callInd (n := n) p args hp hr : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R (.callInd (n := n) p args hp hr : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS]
  erw [execStmtHA_nachΛ]
  simp only [execStmtHA]
  erw [show (ruE p).orte ++ (ruA args).orte = p.orte ++ args.orte from
    kongr₂ (· ++ ·) (ruE_orte p) (ruA_orte args)]
  erw [leseA_worldR hA, eval_ru, evalArgs_ru]
  cases h : eval (leseA A σ Λ (p.orte ++ args.orte)) p (leseA A σ Λ (p.orte ++ args.orte)) ρ with
  | mk g hg =>
      rw [valR_fnptr]
      dsimp only
      erw [umsig_ru hg]
      rcases hR g (leseA A σ Λ (p.orte ++ args.orte)) (umsig hg (evalArgs
          (leseA A σ Λ (p.orte ++ args.orte)) args (leseA A σ Λ (p.orte ++ args.orte)) ρ))
        with hx' | ⟨e', e, h1, h2, ht⟩
      · erw [hx']
        cases hx : R g (leseA A σ Λ (p.orte ++ args.orte)) (umsig hg (evalArgs
            (leseA A σ Λ (p.orte ++ args.orte)) args (leseA A σ Λ (p.orte ++ args.orte)) ρ)) with
        | ok σ' v => (try erw [hx]); exact Or.inl rfl
        | why σ' r => exact keinGrundSig hg hr r
        | logik e => (try erw [hx]); exact Or.inl rfl
        | hardware e => (try erw [hx]); exact Or.inl rfl
      · erw [h1, h2]
        exact Or.inr ⟨e', e, rfl, rfl, ht⟩

set_option linter.unusedSectionVars false in
theorem execStmtHA_ru_callIndElse {V : Vertrag D}
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
    (ih_execEndHA_ru_err : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd err) (worldR σ) (envR ρ)) (execEndHA S O U A passes R err σ ρ))
    : AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS (.callIndElse (n := n) p args he hp hr err : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R (.callIndElse (n := n) p args he hp hr err : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS]
  erw [execStmtHA_nachΛ]
  simp only [execStmtHA, indSonst]
  erw [show (ruE p).orte ++ (ruA args).orte = p.orte ++ args.orte from
    kongr₂ (· ++ ·) (ruE_orte p) (ruA_orte args)]
  erw [leseA_worldR hA, eval_ru, evalArgs_ru]
  cases h : eval (leseA A σ Λ (p.orte ++ args.orte)) p (leseA A σ Λ (p.orte ++ args.orte)) ρ with
  | mk g hg =>
      rw [valR_fnptr]
      dsimp only
      erw [umsig_ru hg]
      rcases hR g (leseA A σ Λ (p.orte ++ args.orte)) (umsig hg (evalArgs
          (leseA A σ Λ (p.orte ++ args.orte)) args (leseA A σ Λ (p.orte ++ args.orte)) ρ))
        with hx' | ⟨e', e, h1, h2, ht⟩
      · erw [hx']
        cases hx : R g (leseA A σ Λ (p.orte ++ args.orte)) (umsig hg (evalArgs
            (leseA A σ Λ (p.orte ++ args.orte)) args (leseA A σ Λ (p.orte ++ args.orte)) ρ)) with
        | ok σ' v => (try erw [hx]); exact Or.inl rfl
        | why σ' r =>
            try erw [hx]
            exact EndRel.zuAusgang (EndRel.schrumpf (ih_execEndHA_ru_err σ' (Env.cons (grundSig hg r) ρ)))
        | logik e => (try erw [hx]); exact Or.inl rfl
        | hardware e => (try erw [hx]); exact Or.inl rfl
      · erw [h1, h2]
        exact Or.inr ⟨e', e, rfl, rfl, ht⟩

set_option linter.unusedSectionVars false in
theorem execStmtHA_ru_locks {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (hr)
    (body)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockHA_ru_body : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB body) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R body σ ρ))
    : AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS (.locks L hr body : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R (.locks L hr body : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmtHA]
  rw [hU, nimmt_worldR]
  exact AusRelRu.frei S L (ih_execBlockHA_ru_body ((U L σ).nimmt L) ρ)

set_option linter.unusedSectionVars false in
theorem execStmtHA_ru_traverse {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (t)
    (inv)
    (body)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockHA_ru_body : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB body) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R body σ ρ))
    : AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS (.traverse t inv body : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R (.traverse t inv body : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmtHA]
  have hL := traverseLauf_rel (l := l) (fun σ ρ => execBlockHA S O U A passes R body σ ρ)
    (fun σ ρ => execBlockHA S.mitRuhe O' U' A' passes R' (ruB body) σ ρ)
    (fun σ ρ => (leseA A σ Λ inv.orte, wahr? (eval (leseA A σ Λ inv.orte) inv (leseA A σ Λ inv.orte) ρ)))
    (fun σ ρ => (leseA A' σ (Λ.map resR) (ruE inv).orte,
      wahr? (eval (leseA A' σ (Λ.map resR) (ruE inv).orte) (ruE inv)
        (leseA A' σ (Λ.map resR) (ruE inv).orte) ρ)))
    (fun σ ρ => ih_execBlockHA_ru_body σ ρ)
    (fun σ ρ => by simp only [ruE_orte, leseA_worldR hA, eval_ru, valR_bool, wahr?])
    (alleIndizes (D.count t)) σ ρ
  rw [map_valR_int] at hL
  exact hL

set_option linter.unusedSectionVars false in
theorem execStmtHA_ru_consumeTraverse {V : Vertrag D}
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
    (ih_execBlockHA_ru_body : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB body) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R body σ ρ))
    : AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS (.consumeTraverse t member edge inv bound mass body : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R (.consumeTraverse t member edge inv bound mass body : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmtHA]
  have hL := traverseLauf_rel (l := l) (fun σ ρ => execBlockHA S O U A passes R body σ ρ)
    (fun σ ρ => execBlockHA S.mitRuhe O' U' A' passes R' (ruB body) σ ρ)
    (fun σ ρ => (leseA A σ Λ inv.orte, wahr? (eval (leseA A σ Λ inv.orte) inv (leseA A σ Λ inv.orte) ρ)))
    (fun σ ρ => (leseA A' σ (Λ.map resR) (ruE inv).orte,
      wahr? (eval (leseA A' σ (Λ.map resR) (ruE inv).orte) (ruE inv)
        (leseA A' σ (Λ.map resR) (ruE inv).orte) ρ)))
    (fun σ ρ => ih_execBlockHA_ru_body σ ρ)
    (fun σ ρ => by simp only [ruE_orte, leseA_worldR hA, eval_ru, valR_bool, wahr?])
    (alleIndizes (D.count t)) σ ρ
  rw [map_valR_int] at hL
  exact hL

end HauptA
end Gabbro.Grammatik
