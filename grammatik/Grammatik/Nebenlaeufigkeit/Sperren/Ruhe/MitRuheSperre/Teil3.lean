module

public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSperre.Teil3a

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
theorem execBlockH_ru_regRead {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (r)
    (hk)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.regRead r hk rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.regRead r hk rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH]
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
          exact AusRelRu.schrumpf (ih_execBlockH_ru_rest (σ.fragt (.inr (.inl r))) (Env.cons v ρ))

set_option linter.unusedSectionVars false in
theorem execBlockH_ru_regReadElse {V : Vertrag D}
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
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    (ih_execEndH_ru_sonst : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd sonst) (worldR σ) (envR ρ)) (execEndH S O U passes R sonst σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.regReadElse r hk zusage sonst rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.regReadElse r hk zusage sonst rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH]
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
          exact EndRel.zuAusgang (ih_execEndH_ru_sonst _ ρ)
      | true =>
          simp only [wahr?, valR_bool, h, if_true]
          exact AusRelRu.schrumpf (ih_execBlockH_ru_rest _ (Env.cons v ρ))

set_option linter.unusedSectionVars false in
theorem execBlockH_ru_awaits {V : Vertrag D}
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
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.awaits g payload hp hL hat rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.awaits g payload hp hL hat rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH]
  rw [worldR_fragt, hO.sichtbar]
  cases O.sichtbar g (σ.fragt (.inr (.inr g))) with
  | false => exact Or.inl rfl
  | true =>
      simp only [if_true]
      rw [show ([Sum.inr g] : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) = [Sum.inr g] from rfl,
        lese_worldR]
      exact AusRelRu.schrumpf (ih_execBlockH_ru_rest ((σ.fragt (.inr (.inr g))).lese Λ [Sum.inr g])
        (Env.cons (((σ.fragt (.inr (.inr g))).lese Λ [Sum.inr g]).globs g) ρ))

set_option linter.unusedSectionVars false in
theorem execBlockH_ru_exchange {V : Vertrag D}
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
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.exchange g neu hw hL rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.exchange g neu hw hL rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH]
  rw [show (Sum.inr g :: (ruE neu).orte : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) =
    Sum.inr g :: neu.orte from congrArg (Sum.inr g :: ·) (ruE_orte neu), lese_worldR]
  have ez := eval_ru (σ.lese Λ (Sum.inr g :: neu.orte)) (σ.lese Λ (Sum.inr g :: neu.orte)) neu
    (Env.cons ((σ.lese Λ (Sum.inr g :: neu.orte)).globs g) ρ)
  change eval _ (ruE neu) _ (Env.cons (valR _ _) (envR ρ)) = _ at ez
  rw [show ((worldR (σ.lese Λ (Sum.inr g :: neu.orte))).globs g) =
    valR _ ((σ.lese Λ (Sum.inr g :: neu.orte)).globs g) from rfl, ez, schreibGlob_worldR]
  exact AusRelRu.schrumpf (ih_execBlockH_ru_rest
    ((σ.lese Λ (Sum.inr g :: neu.orte)).schreibGlob g Λ (eval (σ.lese Λ (Sum.inr g :: neu.orte)) neu
      (σ.lese Λ (Sum.inr g :: neu.orte)) (Env.cons ((σ.lese Λ (Sum.inr g :: neu.orte)).globs g) ρ)))
    (Env.cons ((σ.lese Λ (Sum.inr g :: neu.orte)).globs g) ρ))

set_option linter.unusedSectionVars false in
theorem execBlockH_ru_narrow {V : Vertrag D}
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
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    (ih_execEndH_ru_sonst : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd sonst) (worldR σ) (envR ρ)) (execEndH S O U passes R sonst σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH]
  simp only [ruE_orte, lese_worldR, eval_ru, valR_int]
  by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi'
  · erw [dif_pos hc, dif_pos hc]
    exact AusRelRu.schrumpf (ih_execBlockH_ru_rest _
      (Env.cons (⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, hc.1, hc.2⟩ : Zahl lo' hi') ρ))
  · erw [dif_neg hc, dif_neg hc]
    exact EndRel.zuAusgang (ih_execEndH_ru_sonst _ ρ)

set_option linter.unusedSectionVars false in
theorem execBlockH_ru_narrowRequired {V : Vertrag D}
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
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.narrowRequired (lo := zi_lo) (hi := zi_hi) e lo' hi' rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.narrowRequired (lo := zi_lo) (hi := zi_hi) e lo' hi' rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH]
  simp only [ruE_orte, lese_worldR, eval_ru, valR_int]
  by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi'
  · erw [dif_pos hc, dif_pos hc]
    exact AusRelRu.schrumpf (ih_execBlockH_ru_rest _
      (Env.cons (⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, hc.1, hc.2⟩ : Zahl lo' hi') ρ))
  · erw [dif_neg hc, dif_neg hc]
    exact Or.inl rfl

set_option linter.unusedSectionVars false in
theorem execBlockH_ru_check {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (c)
    (sonst)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    (ih_execEndH_ru_sonst : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd sonst) (worldR σ) (envR ρ)) (execEndH S O U passes R sonst σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.check c sonst rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.check c sonst rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH]
  rw [ruE_orte, lese_worldR, eval_ru]
  cases h : (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ : Bool) with
  | false =>
      simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
      exact EndRel.zuAusgang (ih_execEndH_ru_sonst _ ρ)
  | true =>
      simp only [wahr?, valR_bool, h, if_true]
      exact ih_execBlockH_ru_rest _ ρ

set_option linter.unusedSectionVars false in
theorem execBlockH_ru_float {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_l1}
    {zi_h1}
    {zi_l2}
    {zi_h2}
    (op)
    (a)
    (b)
    (lo)
    (hi)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockH S O U passes R rest σ ρ))
    : AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockH S O U passes R (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockH]
  rw [orte2, lese_worldR, eval_ru, eval_ru]
  try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
  cases gleitPasst lo hi (gleitRechne op
      (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
      (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) with
  | none => exact Or.inl rfl
  | some v => exact AusRelRu.schrumpf (ih_execBlockH_ru_rest _ (Env.cons v ρ))

end Haupt
end Gabbro.Grammatik
