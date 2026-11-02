module

public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSperre.Teil2
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSperre.Teil2a

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
theorem execBlockH_ru_bind {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_τ}
    (e)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.bind (τ := zi_τ) e rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.bind (τ := zi_τ) e rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH]
  rw [ruE_orte, lese_worldR, eval_ru]
  exact AusRelRu.schrumpf (ih_execBlockH_ru_rest (σ.lese Λ e.orte)
    (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ))

set_option linter.unusedSectionVars false in
theorem execBlockH_ru_bindCall {V : Vertrag D}
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
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.bindCall (τ := zi_τ) g args he hp hr rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.bindCall (τ := zi_τ) g args he hp hr rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH]
  erw [ruA_orte, lese_worldR, evalArgs_ru]
  rcases hR g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
    with hx' | ⟨e', e, h1, h2, ht⟩
  · erw [hx']
    cases hx : R g (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
    | ok σ' v =>
        try erw [hx]
        simp only [rufR]
        erw [execBlockH_vorΛ, ergWert_ru he]
        exact AusRelRu.schrumpf (ih_execBlockH_ru_rest σ' (Env.cons (ergWert he v) ρ))
    | why σ' r => exact (Fin.cast hr r).elim0
    | logik e => (try erw [hx]); exact Or.inl rfl
    | hardware e => (try erw [hx]); exact Or.inl rfl
  · erw [h1, h2]
    exact Or.inr ⟨e', e, rfl, rfl, ht⟩

set_option linter.unusedSectionVars false in
theorem execBlockH_ru_bindCallInd {V : Vertrag D}
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
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.bindCallInd (τ := zi_τ) (n := n) p args he hp hr rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.bindCallInd (τ := zi_τ) (n := n) p args he hp hr rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH]
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
            erw [execBlockH_vorΛ, ergWert_ru (ergSig hg he)]
            exact AusRelRu.schrumpf
              (ih_execBlockH_ru_rest σ' (Env.cons (ergWert (ergSig hg he) v) ρ))
        | why σ' r => exact keinGrundSig hg hr r
        | logik e => (try erw [hx]); exact Or.inl rfl
        | hardware e => (try erw [hx]); exact Or.inl rfl
      · erw [h1, h2]
        exact Or.inr ⟨e', e, rfl, rfl, ht⟩

set_option linter.unusedSectionVars false in
theorem execBlockH_ru_bindCallIndElse {V : Vertrag D}
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
    (err)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    (ih_execEndH_ru_err : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd err) (worldR σ) (envR ρ)) (execEndH S O U passes R err σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.bindCallIndElse (τ := zi_τ) (n := n) p args he hp hr err rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.bindCallIndElse (τ := zi_τ) (n := n) p args he hp hr err rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH, indSonst]
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
            erw [execBlockH_vorΛ, ergWert_ru (ergSig hg he)]
            exact AusRelRu.schrumpf
              (ih_execBlockH_ru_rest σ' (Env.cons (ergWert (ergSig hg he) v) ρ))
        | why σ' r =>
            try erw [hx]
            simp only [rufR]
            erw [execEndH_umΛ]
            exact EndRel.zuAusgang (EndRel.schrumpf (ih_execEndH_ru_err σ' (Env.cons (grundSig hg r) ρ)))
        | logik e => (try erw [hx]); exact Or.inl rfl
        | hardware e => (try erw [hx]); exact Or.inl rfl
      · erw [h1, h2]
        exact Or.inr ⟨e', e, rfl, rfl, ht⟩

set_option linter.unusedSectionVars false in
theorem execBlockH_ru_bindCallElse {V : Vertrag D}
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
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    (ih_execEndH_ru_err : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd err) (worldR σ) (envR ρ)) (execEndH S O U passes R err σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.bindCallElse (τ := zi_τ) g args he hp hr err rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.bindCallElse (τ := zi_τ) g args he hp hr err rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH]
  erw [ruA_orte, lese_worldR, evalArgs_ru]
  rcases hR g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
    with hx' | ⟨e', e, h1, h2, ht⟩
  · erw [hx']
    cases hx : R g (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
    | ok σ' v =>
        try erw [hx]
        simp only [rufR]
        erw [execBlockH_vorΛ, ergWert_ru he]
        exact AusRelRu.schrumpf (ih_execBlockH_ru_rest σ' (Env.cons (ergWert he v) ρ))
    | why σ' r =>
        try erw [hx]
        simp only [rufR]
        erw [execEndH_umΛ]
        exact EndRel.zuAusgang (EndRel.schrumpf (ih_execEndH_ru_err σ' (Env.cons r ρ)))
    | logik e => (try erw [hx]); exact Or.inl rfl
    | hardware e => (try erw [hx]); exact Or.inl rfl
  · erw [h1, h2]
    exact Or.inr ⟨e', e, rfl, rfl, ht⟩

set_option linter.unusedSectionVars false in
theorem execBlockH_ru_bindAxiom {V : Vertrag D}
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
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.bindAxiom (τ := zi_τ) a args he hw hg hd hgd rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.bindAxiom (τ := zi_τ) a args he hw hg hd hgd rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH]
  erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwort_ruG hO]
  cases axiomAntwort O a (σ.lese Λ args.orte)
    (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | mk σ' w =>
      cases w with
      | none => exact Or.inl rfl
      | some v =>
          simp only [Option.map]
          rw [ergWert_ru he]
          exact AusRelRu.schrumpf (ih_execBlockH_ru_rest σ' (Env.cons (ergWert he v) ρ))

set_option linter.unusedSectionVars false in
theorem execBlockH_ru_bindAxiomElse {V : Vertrag D}
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
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    (ih_execEndH_ru_err : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd err) (worldR σ) (envR ρ)) (execEndH S O U passes R err σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.bindAxiomElse (τ := zi_τ) a args he hr hw hg hd hgd err rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.bindAxiomElse (τ := zi_τ) a args he hr hw hg hd hgd err rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH]
  erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwortSonst_ruG hO]
  cases axiomAntwortSonst O a (σ.lese Λ args.orte)
    (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | mk σ' w =>
      rcases w with _ | v | r
      · exact Or.inl rfl
      · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply]
        rw [ergWert_ru he]
        exact AusRelRu.schrumpf (ih_execBlockH_ru_rest σ' (Env.cons (ergWert he v) ρ))
      · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply, id]
        exact EndRel.zuAusgang (EndRel.schrumpf
          (ih_execEndH_ru_err σ' (Env.cons (τ := .why (D.agruende a)) r ρ)))


end Haupt

end Gabbro.Grammatik
