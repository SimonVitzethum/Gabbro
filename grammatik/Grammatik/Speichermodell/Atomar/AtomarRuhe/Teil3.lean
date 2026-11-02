module

public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSperre
public import Grammatik.Speichermodell.Maschine.SperreSemA
public import Grammatik.Speichermodell.Atomar.AtomarRuhe.Teil3a

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
theorem execEndHA_ru_ret {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (e)
    (hΛ)
    (σ : World D)
    (ρ : Env D Γ)
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.ret e hΛ : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.ret e hΛ : Endblock D V l Γ Λ) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruEnd, execEndHA]
  erw [ruErg_orte, leseA_worldR hA, evalErg_ru]
  rfl

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_retScoped {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (e)
    (R)
    (σ : World D)
    (ρ : Env D Γ)
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.retScoped e R : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.retScoped e R : Endblock D V l Γ Λ) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruEnd, execEndHA]
  erw [ruErg_orte, leseA_worldR hA, evalErg_ru]
  rfl

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_cons {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_Λ'}
    (s)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execStmtHA_ru_s : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS s) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R s σ ρ))
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.cons (Λ' := zi_Λ') s rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.cons (Λ' := zi_Λ') s rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  rcases ih_execStmtHA_ru_s σ ρ with h | ⟨e', e, h1, h2, ht⟩
  · rw [h]
    cases execStmtHA S O U A passes R s σ ρ with
    | ok σ' ρ' => exact ih_execEndHA_ru_rest σ' ρ'
    | _ => exact Or.inl rfl
  · rw [h1, h2]
    exact Or.inr ⟨e', e, rfl, rfl, ht⟩

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_bind {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_τ}
    (e)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.bind (τ := zi_τ) e rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.bind (τ := zi_τ) e rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  rw [ruE_orte, leseA_worldR hA, eval_ru]
  exact EndRel.schrumpf (ih_execEndHA_ru_rest (leseA A σ Λ e.orte)
    (Env.cons (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ) ρ))

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_bindCall {V : Vertrag D}
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
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.bindCall (τ := zi_τ) g args he hp hr rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.bindCall (τ := zi_τ) g args he hp hr rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  erw [ruA_orte, leseA_worldR hA, evalArgs_ru]
  rcases hR g (leseA A σ Λ args.orte) (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ)
    with hx' | ⟨e', e, h1, h2, ht⟩
  · erw [hx']
    cases hx : R g (leseA A σ Λ args.orte)
        (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ) with
    | ok σ' v =>
        try erw [hx]
        simp only [rufR]
        erw [execEndHA_umΛ, ergWert_ru he]
        exact EndRel.schrumpf (ih_execEndHA_ru_rest σ' (Env.cons (ergWert he v) ρ))
    | why σ' r => exact (Fin.cast hr r).elim0
    | logik e => (try erw [hx]); exact Or.inl rfl
    | hardware e => (try erw [hx]); exact Or.inl rfl
  · erw [h1, h2]
    exact Or.inr ⟨e', e, rfl, rfl, ht⟩

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_bindCallElse {V : Vertrag D}
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
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    (ih_execEndHA_ru_err : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd err) (worldR σ) (envR ρ)) (execEndHA S O U A passes R err σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.bindCallElse (τ := zi_τ) g args he hp hr err rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.bindCallElse (τ := zi_τ) g args he hp hr err rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  erw [ruA_orte, leseA_worldR hA, evalArgs_ru]
  rcases hR g (leseA A σ Λ args.orte) (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ)
    with hx' | ⟨e', e, h1, h2, ht⟩
  · erw [hx']
    cases hx : R g (leseA A σ Λ args.orte)
        (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ) with
    | ok σ' v =>
        try erw [hx]
        simp only [rufR]
        erw [execEndHA_umΛ, ergWert_ru he]
        exact EndRel.schrumpf (ih_execEndHA_ru_rest σ' (Env.cons (ergWert he v) ρ))
    | why σ' r =>
        try erw [hx]
        simp only [rufR]
        erw [execEndHA_umΛ]
        exact EndRel.schrumpf (ih_execEndHA_ru_err σ' (Env.cons r ρ))
    | logik e => (try erw [hx]); exact Or.inl rfl
    | hardware e => (try erw [hx]); exact Or.inl rfl
  · erw [h1, h2]
    exact Or.inr ⟨e', e, rfl, rfl, ht⟩

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_bindAxiom {V : Vertrag D}
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
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.bindAxiom (τ := zi_τ) a args he hw hg hd hgd rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.bindAxiom (τ := zi_τ) a args he hw hg hd hgd rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  erw [ruA_orte, leseA_worldR hA, evalArgs_ru, axiomAntwort_ruG hO]
  cases axiomAntwort O a (leseA A σ Λ args.orte)
    (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ) with
  | mk σ' w =>
      cases w with
      | none => exact Or.inl rfl
      | some v =>
          simp only [Option.map]
          rw [ergWert_ru he]
          exact EndRel.schrumpf (ih_execEndHA_ru_rest σ' (Env.cons (ergWert he v) ρ))

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_bindAxiomElse {V : Vertrag D}
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
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    (ih_execEndHA_ru_err : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd err) (worldR σ) (envR ρ)) (execEndHA S O U A passes R err σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.bindAxiomElse (τ := zi_τ) a args he hr hw hg hd hgd err rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.bindAxiomElse (τ := zi_τ) a args he hr hw hg hd hgd err rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  erw [ruA_orte, leseA_worldR hA, evalArgs_ru, axiomAntwortSonst_ruG hO]
  cases axiomAntwortSonst O a (leseA A σ Λ args.orte)
    (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ) with
  | mk σ' w =>
      rcases w with _ | v | r
      · exact Or.inl rfl
      · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply]
        rw [ergWert_ru he]
        exact EndRel.schrumpf (ih_execEndHA_ru_rest σ' (Env.cons (ergWert he v) ρ))
      · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply, id]
        exact EndRel.schrumpf (ih_execEndHA_ru_err σ' (Env.cons (τ := .why (D.agruende a)) r ρ))

end HauptA
end Gabbro.Grammatik
