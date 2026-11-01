module

public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSperre
public import Grammatik.Speichermodell.Maschine.SperreSemA
public import Grammatik.Speichermodell.Atomar.AtomarRuhe.Teil1

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
theorem execStmtHA_ru_retry {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (n)
    (bis)
    (body)
    (ueber)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockHA_ru_body : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB body) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R body σ ρ))
    (ih_execBlockHA_ru_ueber : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB ueber) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R ueber σ ρ))
    : AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS (.retry n bis body ueber : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R (.retry n bis body ueber : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmtHA]
  exact retryLauf_rel (fun σ ρ => execBlockHA S O U A passes R body σ ρ)
    (fun σ ρ => execBlockHA S.mitRuhe O' U' A' passes R' (ruB body) σ ρ)
    (fun σ ρ => (leseA A σ Λ bis.orte, wahr? (eval (leseA A σ Λ bis.orte) bis (leseA A σ Λ bis.orte) ρ)))
    (fun σ ρ => (leseA A' σ (Λ.map resR) (ruE bis).orte,
      wahr? (eval (leseA A' σ (Λ.map resR) (ruE bis).orte) (ruE bis)
        (leseA A' σ (Λ.map resR) (ruE bis).orte) ρ)))
    (fun σ ρ => execBlockHA S O U A passes R ueber σ ρ)
    (fun σ ρ => execBlockHA S.mitRuhe O' U' A' passes R' (ruB ueber) σ ρ)
    (fun σ ρ => ih_execBlockHA_ru_body σ ρ)
    (fun σ ρ => by simp only [ruE_orte, leseA_worldR hA, eval_ru, valR_bool, wahr?])
    (fun σ ρ => ih_execBlockHA_ru_ueber σ ρ) n σ ρ

set_option linter.unusedSectionVars false in
theorem execStmtHA_ru_forever {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (a)
    (inv)
    (body)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockHA_ru_body : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB body) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R body σ ρ))
    : AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS (.forever a inv body : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R (.forever a inv body : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmtHA]
  exact foreverLauf_rel a (fun σ ρ => execBlockHA S O U A passes R body σ ρ)
    (fun σ ρ => execBlockHA S.mitRuhe O' U' A' passes R' (ruB body) σ ρ)
    (fun σ ρ => (leseA A σ Λ inv.orte, wahr? (eval (leseA A σ Λ inv.orte) inv (leseA A σ Λ inv.orte) ρ)))
    (fun σ ρ => (leseA A' σ (Λ.map resR) (ruE inv).orte,
      wahr? (eval (leseA A' σ (Λ.map resR) (ruE inv).orte) (ruE inv)
        (leseA A' σ (Λ.map resR) (ruE inv).orte) ρ)))
    (fun σ ρ => ih_execBlockHA_ru_body σ ρ)
    (fun σ ρ => by simp only [ruE_orte, leseA_worldR hA, eval_ru, valR_bool, wahr?]) passes σ ρ

set_option linter.unusedSectionVars false in
theorem execStmtHA_ru_axiomCall {V : Vertrag D}
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
    : AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS (.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R (.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ _) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruS, execStmtHA]
  erw [ruA_orte, leseA_worldR hA, evalArgs_ru, axiomAntwort_ruG hO]
  cases axiomAntwort O a (leseA A σ Λ args.orte)
    (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ) with
  | mk σ' w =>
      cases w with
      | none => rfl
      | some _ => rfl

set_option linter.unusedSectionVars false in
theorem execStmtHA_ru_regWrite {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (r)
    (hk)
    (e)
    (σ : World D)
    (ρ : Env D Γ)
    : AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS (.regWrite r hk e : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R (.regWrite r hk e : Stmt D V l Γ Λ _) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruS, execStmtHA]
  rw [ruE_orte, leseA_worldR hA]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmtHA_ru_publish {V : Vertrag D}
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
    : AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS (.publish g e payload hp hw hL : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R (.publish g e payload hp hw hL : Stmt D V l Γ Λ _) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruS, execStmtHA]
  rw [ruE_orte, leseA_worldR hA, eval_ru, schreibGlob_worldR]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmtHA_ru_ret {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (e)
    (hΛ)
    (σ : World D)
    (ρ : Env D Γ)
    : AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS (.ret e hΛ : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R (.ret e hΛ : Stmt D V l Γ Λ _) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruS, execStmtHA]
  erw [ruErg_orte, leseA_worldR hA, evalErg_ru]
  rfl

set_option linter.unusedSectionVars false in
theorem execBlockHA_ru_cons {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_Λ'}
    (s)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execStmtHA_ru_s : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS s) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R s σ ρ))
    (ih_execBlockHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R rest σ ρ))
    : AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB (.cons (Λ' := zi_Λ') s rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R (.cons (Λ' := zi_Λ') s rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockHA]
  rcases ih_execStmtHA_ru_s σ ρ with h | ⟨e', e, h1, h2, ht⟩
  · rw [h]
    cases execStmtHA S O U A passes R s σ ρ with
    | ok σ' ρ' => exact ih_execBlockHA_ru_rest σ' ρ'
    | _ => exact Or.inl rfl
  · rw [h1, h2]
    exact Or.inr ⟨e', e, rfl, rfl, ht⟩

set_option linter.unusedSectionVars false in
theorem execBlockHA_ru_bind {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_τ}
    (e)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R rest σ ρ))
    : AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB (.bind (τ := zi_τ) e rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R (.bind (τ := zi_τ) e rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockHA]
  rw [ruE_orte, leseA_worldR hA, eval_ru]
  exact AusRelRu.schrumpf (ih_execBlockHA_ru_rest (leseA A σ Λ e.orte)
    (Env.cons (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ) ρ))

set_option linter.unusedSectionVars false in
theorem execBlockHA_ru_bindCall {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_τ}
    (g)
    (args)
    (he)
    (hp)
    (hr)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R rest σ ρ))
    : AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB (.bindCall (τ := zi_τ) g args he hp hr rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R (.bindCall (τ := zi_τ) g args he hp hr rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockHA]
  erw [ruA_orte, leseA_worldR hA, evalArgs_ru]
  rcases hR g (leseA A σ Λ args.orte) (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ)
    with hx' | ⟨e', e, h1, h2, ht⟩
  · erw [hx']
    cases hx : R g (leseA A σ Λ args.orte)
        (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ) with
    | ok σ' v =>
        try erw [hx]
        simp only [rufR]
        erw [execBlockHA_vorΛ, ergWert_ru he]
        exact AusRelRu.schrumpf (ih_execBlockHA_ru_rest σ' (Env.cons (ergWert he v) ρ))
    | why σ' r => exact (Fin.cast hr r).elim0
    | logik e => (try erw [hx]); exact Or.inl rfl
    | hardware e => (try erw [hx]); exact Or.inl rfl
  · erw [h1, h2]
    exact Or.inr ⟨e', e, rfl, rfl, ht⟩

set_option linter.unusedSectionVars false in
theorem execBlockHA_ru_bindCallInd {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
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
    (ih_execBlockHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R rest σ ρ))
    : AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB (.bindCallInd (τ := zi_τ) (n := n) p args he hp hr rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R (.bindCallInd (τ := zi_τ) (n := n) p args he hp hr rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockHA]
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
        | ok σ' v =>
            try erw [hx]
            simp only [rufR]
            erw [execBlockHA_vorΛ, ergWert_ru (ergSig hg he)]
            exact AusRelRu.schrumpf
              (ih_execBlockHA_ru_rest σ' (Env.cons (ergWert (ergSig hg he) v) ρ))
        | why σ' r => exact keinGrundSig hg hr r
        | logik e => (try erw [hx]); exact Or.inl rfl
        | hardware e => (try erw [hx]); exact Or.inl rfl
      · erw [h1, h2]
        exact Or.inr ⟨e', e, rfl, rfl, ht⟩

set_option linter.unusedSectionVars false in
theorem execBlockHA_ru_bindCallElse {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
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
    (ih_execBlockHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R rest σ ρ))
    (ih_execEndHA_ru_err : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd err) (worldR σ) (envR ρ)) (execEndHA S O U A passes R err σ ρ))
    : AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB (.bindCallElse (τ := zi_τ) g args he hp hr err rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R (.bindCallElse (τ := zi_τ) g args he hp hr err rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockHA]
  erw [ruA_orte, leseA_worldR hA, evalArgs_ru]
  rcases hR g (leseA A σ Λ args.orte) (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ)
    with hx' | ⟨e', e, h1, h2, ht⟩
  · erw [hx']
    cases hx : R g (leseA A σ Λ args.orte)
        (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ) with
    | ok σ' v =>
        try erw [hx]
        simp only [rufR]
        erw [execBlockHA_vorΛ, ergWert_ru he]
        exact AusRelRu.schrumpf (ih_execBlockHA_ru_rest σ' (Env.cons (ergWert he v) ρ))
    | why σ' r =>
        try erw [hx]
        simp only [rufR]
        erw [execEndHA_umΛ]
        exact EndRel.zuAusgang (EndRel.schrumpf (ih_execEndHA_ru_err σ' (Env.cons r ρ)))
    | logik e => (try erw [hx]); exact Or.inl rfl
    | hardware e => (try erw [hx]); exact Or.inl rfl
  · erw [h1, h2]
    exact Or.inr ⟨e', e, rfl, rfl, ht⟩

set_option linter.unusedSectionVars false in
theorem execBlockHA_ru_bindAxiom {V : Vertrag D}
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
    (ih_execBlockHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R rest σ ρ))
    : AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB (.bindAxiom (τ := zi_τ) a args he hw hg hd hgd rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R (.bindAxiom (τ := zi_τ) a args he hw hg hd hgd rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockHA]
  erw [ruA_orte, leseA_worldR hA, evalArgs_ru, axiomAntwort_ruG hO]
  cases axiomAntwort O a (leseA A σ Λ args.orte)
    (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ) with
  | mk σ' w =>
      cases w with
      | none => exact Or.inl rfl
      | some v =>
          simp only [Option.map]
          rw [ergWert_ru he]
          exact AusRelRu.schrumpf (ih_execBlockHA_ru_rest σ' (Env.cons (ergWert he v) ρ))

set_option linter.unusedSectionVars false in
theorem execBlockHA_ru_bindAxiomElse {V : Vertrag D}
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
    (ih_execBlockHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R rest σ ρ))
    (ih_execEndHA_ru_err : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd err) (worldR σ) (envR ρ)) (execEndHA S O U A passes R err σ ρ))
    : AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB (.bindAxiomElse (τ := zi_τ) a args he hr hw hg hd hgd err rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R (.bindAxiomElse (τ := zi_τ) a args he hr hw hg hd hgd err rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockHA]
  erw [ruA_orte, leseA_worldR hA, evalArgs_ru, axiomAntwortSonst_ruG hO]
  cases axiomAntwortSonst O a (leseA A σ Λ args.orte)
    (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ) with
  | mk σ' w =>
      rcases w with _ | v | r
      · exact Or.inl rfl
      · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply]
        rw [ergWert_ru he]
        exact AusRelRu.schrumpf (ih_execBlockHA_ru_rest σ' (Env.cons (ergWert he v) ρ))
      · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply, id]
        exact EndRel.zuAusgang (EndRel.schrumpf
          (ih_execEndHA_ru_err σ' (Env.cons (τ := .why (D.agruende a)) r ρ)))

set_option linter.unusedSectionVars false in
theorem execBlockHA_ru_regRead {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (r)
    (hk)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R rest σ ρ))
    : AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB (.regRead r hk rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R (.regRead r hk rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockHA]
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
          exact AusRelRu.schrumpf (ih_execBlockHA_ru_rest (σ.fragt (.inr (.inl r))) (Env.cons v ρ))

set_option linter.unusedSectionVars false in
theorem execBlockHA_ru_regReadElse {V : Vertrag D}
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
    (ih_execBlockHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R rest σ ρ))
    (ih_execEndHA_ru_sonst : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd sonst) (worldR σ) (envR ρ)) (execEndHA S O U A passes R sonst σ ρ))
    : AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB (.regReadElse r hk zusage sonst rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R (.regReadElse r hk zusage sonst rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockHA]
  rw [worldR_fragt, hO.regLies, einpassen_ru O.zeiger O'.zeiger hO.zeiger]
  cases einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) with
  | none => exact Or.inl rfl
  | some v =>
      simp only [Option.map]
      rw [ruE_orte, leseA_worldR hA]
      have ez := eval_ru (leseA A (σ.fragt (.inr (.inl r))) Λ zusage.orte) (leseA A (σ.fragt (.inr (.inl r))) Λ zusage.orte) zusage (Env.cons v ρ)
      change eval _ (ruE zusage) _ (Env.cons (valR _ v) (envR ρ)) = _ at ez
      rw [ez]
      cases h : (eval (leseA A (σ.fragt (.inr (.inl r))) Λ zusage.orte) zusage (leseA A (σ.fragt (.inr (.inl r))) Λ zusage.orte) (Env.cons v ρ) : Bool) with
      | false =>
          simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
          exact EndRel.zuAusgang (ih_execEndHA_ru_sonst _ ρ)
      | true =>
          simp only [wahr?, valR_bool, h, if_true]
          exact AusRelRu.schrumpf (ih_execBlockHA_ru_rest _ (Env.cons v ρ))

end HauptA
end Gabbro.Grammatik
