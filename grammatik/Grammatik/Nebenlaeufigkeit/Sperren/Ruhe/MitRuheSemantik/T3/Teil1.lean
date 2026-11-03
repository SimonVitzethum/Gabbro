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

set_option linter.unusedSectionVars false in
theorem execStmt_ru_call {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (g)
    (args)
    (hp)
    (hr)
    (σ : World D)
    (ρ : Env D Γ)
    : execStmt O.mitRuhe passes R' (ruS (.call g args hp hr : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.call g args hp hr : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS]
  erw [execStmt_nachΛ]
  simp only [execStmt]
  erw [ruA_orte, lese_worldR, evalArgs_ru, hR]
  cases hx : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | ok σ' v => (try erw [hx]); rfl
  | why σ' r => exact (Fin.cast hr r).elim0
  | logik e => (try erw [hx]); rfl
  | hardware e => (try erw [hx]); rfl

set_option linter.unusedSectionVars false in
theorem execStmt_ru_callInd {V : Vertrag D}
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
    : execStmt O.mitRuhe passes R' (ruS (.callInd (n := n) p args hp hr : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.callInd (n := n) p args hp hr : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS]
  erw [execStmt_nachΛ]
  simp only [execStmt]
  erw [show (ruE p).orte ++ (ruA args).orte = p.orte ++ args.orte from
    kongr₂ (· ++ ·) (ruE_orte p) (ruA_orte args)]
  erw [lese_worldR, eval_ru, evalArgs_ru]
  cases h : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ with
  | mk g hg =>
      rw [valR_fnptr]
      dsimp only
      erw [umsig_ru hg, hR]
      cases hx : R g (σ.lese Λ (p.orte ++ args.orte)) (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
      | ok σ' v => (try erw [hx]); rfl
      | why σ' r => exact keinGrundSig hg hr r
      | logik e => (try erw [hx]); rfl
      | hardware e => (try erw [hx]); rfl

set_option linter.unusedSectionVars false in
theorem execStmt_ru_callIndElse {V : Vertrag D}
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
    (ih_execEnd_ru_err : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd err) (worldR σ) (envR ρ) = endR (execEnd O passes R err σ ρ))
    : execStmt O.mitRuhe passes R' (ruS (.callIndElse (n := n) p args he hp hr err : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.callIndElse (n := n) p args he hp hr err : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS]
  erw [execStmt_nachΛ]
  simp only [execStmt, indSonst]
  erw [show (ruE p).orte ++ (ruA args).orte = p.orte ++ args.orte from
    kongr₂ (· ++ ·) (ruE_orte p) (ruA_orte args)]
  erw [lese_worldR, eval_ru, evalArgs_ru]
  cases h : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ with
  | mk g hg =>
      rw [valR_fnptr]
      dsimp only
      erw [umsig_ru hg, hR]
      cases hx : R g (σ.lese Λ (p.orte ++ args.orte)) (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
      | ok σ' v => (try erw [hx]); rfl
      | why σ' r =>
          try erw [hx]
          simp only [rufR]
          erw [execEnd_umΛ]
          exact (congrArg (fun a => EndAusgang.zuAusgang (EndAusgang.schrumpf a))
            (ih_execEnd_ru_err σ' (Env.cons (grundSig hg r) ρ))).trans
            ((congrArg EndAusgang.zuAusgang (endR_schrumpf _)).trans (endR_zuAusgang _))
      | logik e => (try erw [hx]); rfl
      | hardware e => (try erw [hx]); rfl

set_option linter.unusedSectionVars false in
theorem execStmt_ru_locks {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (hr)
    (body)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlock_ru_body : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB body) (worldR σ) (envR ρ) = ausR (execBlock O passes R body σ ρ))
    : execStmt O.mitRuhe passes R' (ruS (.locks L hr body : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.locks L hr body : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmt]
  rw [nimmt_worldR]
  exact (congrArg _ (ih_execBlock_ru_body (σ.nimmt L) ρ)).trans (ausR_gibt L _)

set_option linter.unusedSectionVars false in
theorem execStmt_ru_traverse {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (t)
    (inv)
    (body)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlock_ru_body : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB body) (worldR σ) (envR ρ) = ausR (execBlock O passes R body σ ρ))
    : execStmt O.mitRuhe passes R' (ruS (.traverse t inv body : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.traverse t inv body : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmt]
  conv => lhs; rw [← map_valR_int (D := D) 0 (D.count t - 1) (alleIndizes (D.count t))]
  refine traverseLauf_ru (execBlock O passes R body) (execBlock O.mitRuhe passes R' (ruB body))
    (fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ)))
    (fun σ ρ => (σ.lese (Λ.map resR) (ruE inv).orte,
      wahr? (eval (σ.lese (Λ.map resR) (ruE inv).orte) (ruE inv) (σ.lese (Λ.map resR) (ruE inv).orte) ρ)))
    (fun σ ρ => ih_execBlock_ru_body σ ρ) (fun σ ρ => ?_) (alleIndizes (D.count t)) σ ρ
  simp only [ruE_orte, lese_worldR, eval_ru, valR_bool, wahr?]

set_option linter.unusedSectionVars false in
theorem execStmt_ru_consumeTraverse {V : Vertrag D}
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
    (ih_execBlock_ru_body : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB body) (worldR σ) (envR ρ) = ausR (execBlock O passes R body σ ρ))
    : execStmt O.mitRuhe passes R' (ruS (.consumeTraverse t member edge inv bound mass body : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.consumeTraverse t member edge inv bound mass body : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmt]
  rw [show (D.mitRuhe.count t).toNat + bound.toNat + 1 =
    (D.count t).toNat + bound.toNat + 1 from by rfl]
  refine verbrauchLauf_ru (D := D) t
    (execBlock O passes R body) (execBlock O.mitRuhe passes R' (ruB body))
    (fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ)))
    (fun σ ρ => (σ.lese (Λ.map resR) (ruE inv).orte,
      wahr? (eval (σ.lese (Λ.map resR) (ruE inv).orte) (ruE inv) (σ.lese (Λ.map resR) (ruE inv).orte) ρ)))
    (verbrauchSel t member edge) (verbrauchSel t (ruE member) (ruE edge))
    (fun σ ρ => let σ := σ.lese Λ mass.orte; (σ, (eval σ mass σ ρ).n))
    (fun σ ρ => let σ := σ.lese (Λ.map resR) (ruE mass).orte; (σ, (eval σ (ruE mass) σ ρ).n))
    bound (fun σ ρ => ih_execBlock_ru_body σ ρ) (fun σ ρ => ?_) ?_ ?_
    ((D.count t).toNat + bound.toNat + 1) σ ρ
  · simp only [ruE_orte, lese_worldR, eval_ru, valR_bool, wahr?]
  · intro σ' ρ'
    simp only [verbrauchSel, ruE_orte, lese_worldR, Prod.mk.injEq]
    refine ⟨rfl, ?_, ?_⟩
    · change verbrauchWahl (alleIndizes (D.count t)) _ _ _ = _
      conv => lhs; rw [← map_valR_int (D := D) 0 (D.count t - 1) (alleIndizes (D.count t))]
      refine verbrauchWahl_map _ _ _ _ _ _ _ _ ?_ ?_ ?_
      · intro k _
        have henv : Env.cons (valR _ k) (envR ρ') = envR (Env.cons k ρ') := rfl
        simp only [henv, eval_ru, valR_bool]
      · intro j _ k _
        have henv : Env.cons (valR _ j) (Env.cons (valR _ k) (envR ρ')) =
            envR (Env.cons j (Env.cons k ρ')) := rfl
        simp only [henv, eval_ru, valR_bool]
      · intro j _ k _
        simp only [show (valR _ j).n = j.n from congrArg Zahl.n (valR_int j),
          show (valR _ k).n = k.n from congrArg Zahl.n (valR_int k)]
    · conv => lhs; rw [show D.mitRuhe.count t = D.count t from rfl]
      conv => lhs; rw [← map_valR_int (D := D) 0 (D.count t - 1) (alleIndizes (D.count t))]
      exact map_all_beibehalt _ _ _ _ (fun k _ => by
        have henv : Env.cons (valR _ k) (envR ρ') = envR (Env.cons k ρ') := rfl
        simp only [henv, eval_ru, valR_bool])
  · intro σ' ρ'
    simp only [ruE_orte, lese_worldR, Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    simp only [eval_ru]
    exact congrArg Zahl.n (valR_int _)

set_option linter.unusedSectionVars false in
theorem execStmt_ru_retry {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (n)
    (bis)
    (body)
    (ueber)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlock_ru_body : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB body) (worldR σ) (envR ρ) = ausR (execBlock O passes R body σ ρ))
    (ih_execBlock_ru_ueber : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB ueber) (worldR σ) (envR ρ) = ausR (execBlock O passes R ueber σ ρ))
    : execStmt O.mitRuhe passes R' (ruS (.retry n bis body ueber : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.retry n bis body ueber : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmt]
  refine retryLauf_ru (execBlock O passes R body) (execBlock O.mitRuhe passes R' (ruB body))
    (fun σ ρ => (σ.lese Λ bis.orte, wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ)))
    (fun σ ρ => (σ.lese (Λ.map resR) (ruE bis).orte,
      wahr? (eval (σ.lese (Λ.map resR) (ruE bis).orte) (ruE bis) (σ.lese (Λ.map resR) (ruE bis).orte) ρ)))
    (execBlock O passes R ueber) (execBlock O.mitRuhe passes R' (ruB ueber))
    (fun σ ρ => ih_execBlock_ru_body σ ρ) (fun σ ρ => ?_) (fun σ ρ => ih_execBlock_ru_ueber σ ρ) n σ ρ
  simp only [ruE_orte, lese_worldR, eval_ru, valR_bool, wahr?]

set_option linter.unusedSectionVars false in
theorem execStmt_ru_forever {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (a)
    (inv)
    (body)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlock_ru_body : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB body) (worldR σ) (envR ρ) = ausR (execBlock O passes R body σ ρ))
    : execStmt O.mitRuhe passes R' (ruS (.forever a inv body : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.forever a inv body : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmt]
  refine foreverLauf_ru a (execBlock O passes R body) (execBlock O.mitRuhe passes R' (ruB body))
    (fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ)))
    (fun σ ρ => (σ.lese (Λ.map resR) (ruE inv).orte,
      wahr? (eval (σ.lese (Λ.map resR) (ruE inv).orte) (ruE inv) (σ.lese (Λ.map resR) (ruE inv).orte) ρ)))
    (fun σ ρ => ih_execBlock_ru_body σ ρ) (fun σ ρ => ?_) passes σ ρ
  simp only [ruE_orte, lese_worldR, eval_ru, valR_bool, wahr?]

set_option linter.unusedSectionVars false in
theorem execStmt_ru_axiomCall {V : Vertrag D}
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
    : execStmt O.mitRuhe passes R' (ruS (.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmt]
  erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwort_ru]
  cases axiomAntwort O a (σ.lese Λ args.orte)
    (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | mk σ' w =>
      cases w with
      | none => rfl
      | some _ => rfl

set_option linter.unusedSectionVars false in
theorem execStmt_ru_axiomCallElse {V : Vertrag D}
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
    (ih_execEnd_ru_err : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd err) (worldR σ) (envR ρ) = endR (execEnd O passes R err σ ρ))
    : execStmt O.mitRuhe passes R' (ruS (.axiomCallElse e a args he hp hd hgd hr err : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.axiomCallElse e a args he hp hd hgd hr err : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS]
  erw [execStmt_nachΛ]
  simp only [execStmt]
  erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwortSonst_ru]
  cases axiomAntwortSonst O a (σ.lese Λ args.orte)
    (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | mk σ' w =>
      rcases w with _ | v | r
      · rfl
      · rfl
      · erw [execEnd_umΛ]
        exact (congrArg (fun a => (EndAusgang.schrumpf a).zuAusgang) (ih_execEnd_ru_err σ' _)).trans
          ((congrArg EndAusgang.zuAusgang (endR_schrumpf _)).trans (endR_zuAusgang _))

end Haupt
end Gabbro.Grammatik
