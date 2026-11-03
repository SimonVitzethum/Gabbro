/- Part 3 of 4 of `MitRuheSemantik` (split by instrumente/teile/lean-teilen.py; the umbrella `MitRuheSemantik.lean` imports all parts). -/
module
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik.T2
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

section Haupt

variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) → RufAusgang f)
  (hR : RufRu R R')

include hR

set_option linter.unusedSectionVars false in
theorem execStmt_ru_assignSlot {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (t)
    (f)
    (i)
    (e)
    (hw)
    (hL)
    (σ : World D)
    (ρ : Env D Γ)
    : execStmt O.mitRuhe passes R' (ruS (.assignSlot t f i e hw hL : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.assignSlot t f i e hw hL : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmt]
  rw [orte2, lese_worldR, eval_ru, eval_ru, schreibSlot_worldR]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmt_ru_assignThru {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_n}
    (p)
    (t)
    (ht)
    (f)
    (i)
    (e)
    (hw)
    (hL)
    (σ : World D)
    (ρ : Env D Γ)
    : execStmt O.mitRuhe passes R' (ruS (.assignThru (n := zi_n) (read := zi_read) (space := zi_space) p t ht f i e hw hL : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.assignThru (n := zi_n) (read := zi_read) (space := zi_space) p t ht f i e hw hL : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmt]
  rw [show (ruE p).orte ++ (ruE i).orte ++ (ruE e).orte = p.orte ++ i.orte ++ e.orte from
    kongr₂ (· ++ ·) (orte2 p i) (ruE_orte e), lese_worldR, eval_ru, eval_ru, schreibSlot_worldR]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmt_ru_assignThruOwn {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_n}
    (p)
    (t)
    (ht)
    (f)
    (i)
    (e)
    (m)
    (s)
    (ho)
    (he)
    (hg)
    (hw)
    (hL)
    (σ : World D)
    (ρ : Env D Γ)
    : execStmt O.mitRuhe passes R' (ruS (.assignThruOwn (n := zi_n) (read := zi_read) (space := zi_space) (o := zi_eig) p t ht f i e m s ho he hg hw hL : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.assignThruOwn (n := zi_n) (read := zi_read) (space := zi_space) (o := zi_eig) p t ht f i e m s ho he hg hw hL : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmt]
  rw [show (ruE p).orte ++ (ruE i).orte ++ (ruE e).orte = p.orte ++ i.orte ++ e.orte from
    kongr₂ (· ++ ·) (orte2 p i) (ruE_orte e), lese_worldR, eval_ru, eval_ru, schreibSlot_worldR]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmt_ru_assignSlotRef {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_n}
    (r)
    (t)
    (ht)
    (ho)
    (f)
    (e)
    (hw)
    (hL)
    (σ : World D)
    (ρ : Env D Γ)
    : execStmt O.mitRuhe passes R' (ruS (.assignSlotRef (n := zi_n) r t ht ho f e hw hL : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.assignSlotRef (n := zi_n) r t ht ho f e hw hL : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmt]
  rw [show (ruE r).orte ++ (ruE e).orte = r.orte ++ e.orte from
    kongr₂ (· ++ ·) (ruE_orte r) (ruE_orte e), lese_worldR, eval_ru, eval_ru, schreibSlot_worldR]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmt_ru_assignGlob {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (g)
    (e)
    (hw)
    (hL)
    (σ : World D)
    (ρ : Env D Γ)
    : execStmt O.mitRuhe passes R' (ruS (.assignGlob g e hw hL : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.assignGlob g e hw hL : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmt]
  rw [ruE_orte, lese_worldR, eval_ru, schreibGlob_worldR]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmt_ru_putBytes {V : Vertrag D}
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
    : execStmt O.mitRuhe passes R' (ruS (.putBytes (lo := zi_lo) (hi := zi_hi) t f hf n i hlo hhi e hw hL : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.putBytes (lo := zi_lo) (hi := zi_hi) t f hf n i hlo hhi e hw hL : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmt]
  rw [orte2, lese_worldR, eval_ru, eval_ru, schreibBytes_worldR t f hf]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmt_ru_assignVar {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_τ}
    (x)
    (e)
    (σ : World D)
    (ρ : Env D Γ)
    : execStmt O.mitRuhe passes R' (ruS (.assignVar (τ := zi_τ) x e : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.assignVar (τ := zi_τ) x e : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmt]
  rw [ruE_orte, lese_worldR, eval_ru, envR_set]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmt_ru_shift {V : Vertrag D}
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
    : execStmt O.mitRuhe passes R' (ruS (.shift (lo := lo) (hi := hi) t f hτ i von nach hn he hw hL : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.shift (lo := lo) (hi := hi) t f hτ i von nach hn he hw hL : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmt]
  erw [show (Sum.inl t :: (ruE i).orte : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) =
    Sum.inl t :: i.orte from congrArg (Sum.inl t :: ·) (ruE_orte i)]
  erw [lese_worldR, eval_ru]
  erw [slotInt_cast_worldR _ t f hτ (congrArg tyR hτ)]
  by_cases hc : (hτ ▸ (σ.lese Λ (Sum.inl t :: i.orte)).slots t
      (eval (σ.lese Λ (Sum.inl t :: i.orte)) i (σ.lese Λ (Sum.inl t :: i.orte)) ρ).n f :
      Wert D (.int lo hi)).n = von
  · erw [if_pos hc, if_pos hc, int_cast_gen' (D.typ t f) lo hi hτ (congrArg tyR hτ) _, schreibSlot_worldR]
    rfl
  · erw [if_neg hc, if_neg hc]
    rfl

set_option linter.unusedSectionVars false in
theorem execStmt_ru_ite {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (c)
    (t)
    (e)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlock_ru_e : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB e) (worldR σ) (envR ρ) = ausR (execBlock O passes R e σ ρ))
    (ih_execBlock_ru_t : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB t) (worldR σ) (envR ρ) = ausR (execBlock O passes R t σ ρ))
    : execStmt O.mitRuhe passes R' (ruS (.ite c t e : Stmt D V l Γ Λ Λ')) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.ite c t e : Stmt D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruS, execStmt]
  rw [ruE_orte, lese_worldR, eval_ru]
  cases h : (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ : Bool)
  · simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
    exact ih_execBlock_ru_e _ ρ
  · simp only [wahr?, valR_bool, h, if_true]
    exact ih_execBlock_ru_t _ ρ

set_option linter.unusedSectionVars false in
theorem execStmt_ru_onOption {V : Vertrag D}
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
    (ih_execBlock_ru_a : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB a) (worldR σ) (envR ρ) = ausR (execBlock O passes R a σ ρ))
    (ih_execBlock_ru_p : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB p) (worldR σ) (envR ρ) = ausR (execBlock O passes R p σ ρ))
    : execStmt O.mitRuhe passes R' (ruS (.onOption (n := zi_n) o p a : Stmt D V l Γ Λ Λ')) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.onOption (n := zi_n) o p a : Stmt D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruS, execStmt]
  rw [ruE_orte, lese_worldR, eval_ru]
  try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
  cases h : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ with
  | none => exact ih_execBlock_ru_a _ ρ
  | some k =>
      simp only
      rw [← ausR_schrumpf, ← ih_execBlock_ru_p _ (Env.cons k ρ)]
      rfl

set_option linter.unusedSectionVars false in
theorem execStmt_ru_onTag {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_cs}
    (v)
    (arms)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execArms_ru_arms : ∀ (v : Wert D (.sum _)), ∀ (σ : World D), ∀ (ρ : Env D _), execArms O.mitRuhe passes R' (ruArms arms) (valR (.sum _) v) (worldR σ) (envR ρ) = ausR (execArms O passes R arms v σ ρ))
    : execStmt O.mitRuhe passes R' (ruS (.onTag (cs := zi_cs) v arms : Stmt D V l Γ Λ Λ')) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.onTag (cs := zi_cs) v arms : Stmt D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruS, execStmt]
  rw [ruE_orte, lese_worldR, eval_ru]
  exact ih_execArms_ru_arms _ _ ρ

set_option linter.unusedSectionVars false in
theorem execStmt_ru_onWhy {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_n}
    (r)
    (arms)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execGrund_ru_arms : ∀ (r : Fin _), ∀ (σ : World D), ∀ (ρ : Env D _), execGrund O.mitRuhe passes R' (ruGArms arms) r (worldR σ) (envR ρ) = ausR (execGrund O passes R arms r σ ρ))
    : execStmt O.mitRuhe passes R' (ruS (.onWhy (n := zi_n) r arms : Stmt D V l Γ Λ Λ')) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.onWhy (n := zi_n) r arms : Stmt D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruS, execStmt]
  rw [ruE_orte, lese_worldR, eval_ru]
  exact ih_execGrund_ru_arms _ _ ρ

end Haupt
end Gabbro.Grammatik
