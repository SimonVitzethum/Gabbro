module

public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSperre
public import Grammatik.Speichermodell.Maschine.SperreSemA
public import Grammatik.Speichermodell.Atomar.AtomarRuhe.Teil3

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
theorem execEndHA_ru_regRead {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (r)
    (hk)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.regRead r hk rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.regRead r hk rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
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
          exact EndRel.schrumpf (ih_execEndHA_ru_rest (σ.fragt (.inr (.inl r))) (Env.cons v ρ))

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_regReadElse {V : Vertrag D}
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
    (ih_execEndHA_ru_sonst : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd sonst) (worldR σ) (envR ρ)) (execEndHA S O U A passes R sonst σ ρ))
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.regReadElse r hk zusage sonst rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.regReadElse r hk zusage sonst rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
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
          exact ih_execEndHA_ru_sonst _ ρ
      | true =>
          simp only [wahr?, valR_bool, h, if_true]
          exact EndRel.schrumpf (ih_execEndHA_ru_rest _ (Env.cons v ρ))

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_awaits {V : Vertrag D}
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
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.awaits g payload hp hL hat rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.awaits g payload hp hL hat rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  rw [show ([Sum.inr g] : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) = [Sum.inr g] from rfl,
    worldR_fragt, leseA_worldR hA, hO.sichtbar]
  cases O.sichtbar g (leseA A (σ.fragt (.inr (.inr g))) Λ [Sum.inr g]) with
  | false => exact Or.inl rfl
  | true =>
      simp only [if_true]
      exact EndRel.schrumpf (ih_execEndHA_ru_rest (leseA A (σ.fragt (.inr (.inr g))) Λ [Sum.inr g])
        (Env.cons ((leseA A (σ.fragt (.inr (.inr g))) Λ [Sum.inr g]).globs g) ρ))

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_bindCallInd {V : Vertrag D}
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
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.bindCallInd (τ := zi_τ) (n := n) p args he hp hr rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.bindCallInd (τ := zi_τ) (n := n) p args he hp hr rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
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
            erw [execEndHA_umΛ, ergWert_ru (ergSig hg he)]
            exact EndRel.schrumpf
              (ih_execEndHA_ru_rest σ' (Env.cons (ergWert (ergSig hg he) v) ρ))
        | why σ' r => exact keinGrundSig hg hr r
        | logik e => (try erw [hx]); exact Or.inl rfl
        | hardware e => (try erw [hx]); exact Or.inl rfl
      · erw [h1, h2]
        exact Or.inr ⟨e', e, rfl, rfl, ht⟩

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_narrow {V : Vertrag D}
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
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    (ih_execEndHA_ru_sonst : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd sonst) (worldR σ) (envR ρ)) (execEndHA S O U A passes R sonst σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  simp only [ruE_orte, leseA_worldR hA, eval_ru, valR_int]
  by_cases hc : lo' ≤ (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ∧
      (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ≤ hi'
  · erw [dif_pos hc, dif_pos hc]
    exact EndRel.schrumpf (ih_execEndHA_ru_rest _
      (Env.cons (⟨(eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n, hc.1, hc.2⟩ : Zahl lo' hi') ρ))
  · erw [dif_neg hc, dif_neg hc]
    exact ih_execEndHA_ru_sonst _ ρ

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_narrowRequired {V : Vertrag D}
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
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.narrowRequired (lo := zi_lo) (hi := zi_hi) e lo' hi' rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.narrowRequired (lo := zi_lo) (hi := zi_hi) e lo' hi' rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  simp only [ruE_orte, leseA_worldR hA, eval_ru, valR_int]
  by_cases hc : lo' ≤ (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ∧
      (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ≤ hi'
  · erw [dif_pos hc, dif_pos hc]
    exact EndRel.schrumpf (ih_execEndHA_ru_rest _
      (Env.cons (⟨(eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n, hc.1, hc.2⟩ : Zahl lo' hi') ρ))
  · erw [dif_neg hc, dif_neg hc]
    exact Or.inl rfl

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_exchange {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (g)
    (neu)
    (hw)
    (hL)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.exchange g neu hw hL rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.exchange g neu hw hL rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  rw [show (Sum.inr g :: (ruE neu).orte : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) =
    Sum.inr g :: neu.orte from congrArg (Sum.inr g :: ·) (ruE_orte neu), leseA_worldR hA]
  have ez := eval_ru (leseA A σ Λ (Sum.inr g :: neu.orte)) (leseA A σ Λ (Sum.inr g :: neu.orte)) neu
    (Env.cons ((leseA A σ Λ (Sum.inr g :: neu.orte)).globs g) ρ)
  change eval _ (ruE neu) _ (Env.cons (valR _ _) (envR ρ)) = _ at ez
  rw [show ((worldR (leseA A σ Λ (Sum.inr g :: neu.orte))).globs g) =
    valR _ ((leseA A σ Λ (Sum.inr g :: neu.orte)).globs g) from rfl, ez, schreibGlob_worldR]
  exact EndRel.schrumpf (ih_execEndHA_ru_rest
    ((leseA A σ Λ (Sum.inr g :: neu.orte)).schreibGlob g Λ (eval (leseA A σ Λ (Sum.inr g :: neu.orte)) neu
      (leseA A σ Λ (Sum.inr g :: neu.orte)) (Env.cons ((leseA A σ Λ (Sum.inr g :: neu.orte)).globs g) ρ)))
    (Env.cons ((leseA A σ Λ (Sum.inr g :: neu.orte)).globs g) ρ))

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_ite {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (c)
    (t)
    (e)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEndHA_ru_e : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd e) (worldR σ) (envR ρ)) (execEndHA S O U A passes R e σ ρ))
    (ih_execEndHA_ru_t : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd t) (worldR σ) (envR ρ)) (execEndHA S O U A passes R t σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.ite c t e : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.ite c t e : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  rw [ruE_orte, leseA_worldR hA, eval_ru]
  cases h : (eval (leseA A σ Λ c.orte) c (leseA A σ Λ c.orte) ρ : Bool)
  · simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
    exact ih_execEndHA_ru_e _ ρ
  · simp only [wahr?, valR_bool, h, if_true]
    exact ih_execEndHA_ru_t _ ρ


end HauptA
end Gabbro.Grammatik
