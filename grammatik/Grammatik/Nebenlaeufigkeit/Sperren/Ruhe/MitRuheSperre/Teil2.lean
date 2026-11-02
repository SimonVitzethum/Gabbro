module

public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSperre.Teil1

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
theorem execStmtH_ru_putBytes {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_lo}
    {zi_hi}
    (t)
    (f)
    (hf)
    (n)
    (i)
    (hlo)
    (hhi)
    (e)
    (hw)
    (hL)
    (σ : World D)
    (ρ : Env D Γ)
    : AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS (.putBytes (lo := zi_lo) (hi := zi_hi) t f hf n i hlo hhi e hw hL : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtH S O U passes R (.putBytes (lo := zi_lo) (hi := zi_hi) t f hf n i hlo hhi e hw hL : Stmt D V l Γ Λ _) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruS, execStmtH]
  rw [orte2, lese_worldR, eval_ru, eval_ru, schreibBytes_worldR t f hf]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmtH_ru_assignVar {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_τ}
    (x)
    (e)
    (σ : World D)
    (ρ : Env D Γ)
    : AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS (.assignVar (τ := zi_τ) x e : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtH S O U passes R (.assignVar (τ := zi_τ) x e : Stmt D V l Γ Λ _) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruS, execStmtH]
  rw [ruE_orte, lese_worldR, eval_ru, envR_set]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmtH_ru_shift {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (lo)
    (hi)
    (t)
    (f)
    (hτ)
    (i)
    (von)
    (nach)
    (hn)
    (he)
    (hw)
    (hL)
    (σ : World D)
    (ρ : Env D Γ)
    : AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS (.shift (lo := lo) (hi := hi) t f hτ i von nach hn he hw hL : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtH S O U passes R (.shift (lo := lo) (hi := hi) t f hτ i von nach hn he hw hL : Stmt D V l Γ Λ _) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruS, execStmtH]
  erw [show (Sum.inl t :: (ruE i).orte : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) =
    Sum.inl t :: i.orte from congrArg (Sum.inl t :: ·) (ruE_orte i)]
  erw [lese_worldR, eval_ru]
  erw [slotInt_cast_worldR _ t f hτ (congrArg tyR hτ)]
  by_cases hc : (hτ ▸ (σ.lese Λ (Sum.inl t :: i.orte)).slots t
      (eval (σ.lese Λ (Sum.inl t :: i.orte)) i (σ.lese Λ (Sum.inl t :: i.orte)) ρ).n f :
      Wert D (.int lo hi)).n = von
  · erw [if_pos hc, if_pos hc, int_cast_gen' (D.typ t f) lo hi hτ (congrArg tyR hτ) _,
      schreibSlot_worldR]
    rfl
  · erw [if_neg hc, if_neg hc]
    rfl

set_option linter.unusedSectionVars false in
theorem execStmtH_ru_ite {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (c)
    (t)
    (e)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockH_ru_e : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB e) (worldR σ) (envR ρ)) (execBlockH S O U passes R e σ ρ))
    (ih_execBlockH_ru_t : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB t) (worldR σ) (envR ρ)) (execBlockH S O U passes R t σ ρ))
    : AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS (.ite c t e : Stmt D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execStmtH S O U passes R (.ite c t e : Stmt D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruS, execStmtH]
  rw [ruE_orte, lese_worldR, eval_ru]
  cases h : (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ : Bool)
  · simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
    exact ih_execBlockH_ru_e _ ρ
  · simp only [wahr?, valR_bool, h, if_true]
    exact ih_execBlockH_ru_t _ ρ

set_option linter.unusedSectionVars false in
theorem execStmtH_ru_onOption {V : Vertrag D}
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
    (ih_execBlockH_ru_a : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB a) (worldR σ) (envR ρ)) (execBlockH S O U passes R a σ ρ))
    (ih_execBlockH_ru_p : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB p) (worldR σ) (envR ρ)) (execBlockH S O U passes R p σ ρ))
    : AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS (.onOption (n := zi_n) o p a : Stmt D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execStmtH S O U passes R (.onOption (n := zi_n) o p a : Stmt D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruS, execStmtH]
  rw [ruE_orte, lese_worldR, eval_ru]
  try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
  cases h : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ with
  | none => exact ih_execBlockH_ru_a _ ρ
  | some k =>
      simp only
      exact AusRelRu.schrumpf (ih_execBlockH_ru_p _ (Env.cons k ρ))

set_option linter.unusedSectionVars false in
theorem execStmtH_ru_onTag {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_cs}
    (v)
    (arms)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execArmsH_ru_arms : ∀ (v : Wert D (.sum _)), ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execArmsH S.mitRuhe O' U' passes R' (ruArms arms) (valR (.sum _) v) (worldR σ) (envR ρ)) (execArmsH S O U passes R arms v σ ρ))
    : AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS (.onTag (cs := zi_cs) v arms : Stmt D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execStmtH S O U passes R (.onTag (cs := zi_cs) v arms : Stmt D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruS, execStmtH]
  rw [ruE_orte, lese_worldR, eval_ru]
  exact ih_execArmsH_ru_arms _ _ ρ

set_option linter.unusedSectionVars false in
theorem execStmtH_ru_onWhy {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_n}
    (r)
    (arms)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execGrundH_ru_arms : ∀ (r : Fin _), ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execGrundH S.mitRuhe O' U' passes R' (ruGArms arms) r (worldR σ) (envR ρ)) (execGrundH S O U passes R arms r σ ρ))
    : AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS (.onWhy (n := zi_n) r arms : Stmt D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execStmtH S O U passes R (.onWhy (n := zi_n) r arms : Stmt D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruS, execStmtH]
  rw [ruE_orte, lese_worldR, eval_ru]
  exact ih_execGrundH_ru_arms _ _ ρ

set_option linter.unusedSectionVars false in
theorem execStmtH_ru_call {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (g)
    (args)
    (hp)
    (hr)
    (σ : World D)
    (ρ : Env D Γ)
    : AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS (.call g args hp hr : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ)) (execStmtH S O U passes R (.call g args hp hr : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS]
  erw [execStmtH_nachΛ]
  simp only [execStmtH]
  erw [ruA_orte, lese_worldR, evalArgs_ru]
  rcases hR g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
    with hx' | ⟨e', e, h1, h2, ht⟩
  · erw [hx']
    cases hx : R g (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
    | ok σ' v => (try erw [hx]); exact Or.inl rfl
    | why σ' r => exact (Fin.cast hr r).elim0
    | logik e => (try erw [hx]); exact Or.inl rfl
    | hardware e => (try erw [hx]); exact Or.inl rfl
  · erw [h1, h2]
    exact Or.inr ⟨e', e, rfl, rfl, ht⟩


end Haupt
end Gabbro.Grammatik
