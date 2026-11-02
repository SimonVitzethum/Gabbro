module

public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik.T2
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik.T3.Teil2

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
theorem execBlock_ru_check {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (c)
    (sonst)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlock_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB rest) (worldR σ) (envR ρ) = ausR (execBlock O passes R rest σ ρ))
    (ih_execEnd_ru_sonst : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd sonst) (worldR σ) (envR ρ) = endR (execEnd O passes R sonst σ ρ))
    : execBlock O.mitRuhe passes R' (ruB (.check c sonst rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ) = ausR (execBlock O passes R (.check c sonst rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlock]
  rw [ruE_orte, lese_worldR, eval_ru]
  cases h : (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ : Bool) with
  | false =>
      simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
      rw [← endR_zuAusgang, ih_execEnd_ru_sonst _ ρ]
  | true =>
      simp only [wahr?, valR_bool, h, if_true]
      exact ih_execBlock_ru_rest _ ρ

set_option linter.unusedSectionVars false in
theorem execBlock_ru_float {V : Vertrag D}
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
    (ih_execBlock_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB rest) (worldR σ) (envR ρ) = ausR (execBlock O passes R rest σ ρ))
    : execBlock O.mitRuhe passes R' (ruB (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ) = ausR (execBlock O passes R (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlock]
  rw [orte2, lese_worldR, eval_ru, eval_ru]
  try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
  cases gleitPasst lo hi (gleitRechne op
      (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
      (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) with
  | none => rfl
  | some v =>
      rw [← ausR_schrumpf, ← ih_execBlock_ru_rest _ (Env.cons v ρ)]
      rfl

set_option linter.unusedSectionVars false in
theorem execBlock_ru_floatLit {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (q)
    (lo)
    (hi)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlock_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB rest) (worldR σ) (envR ρ) = ausR (execBlock O passes R rest σ ρ))
    : execBlock O.mitRuhe passes R' (ruB (.floatLit q lo hi rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ) = ausR (execBlock O passes R (.floatLit q lo hi rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlock]
  cases gleitPasst lo hi (bruch q) with
  | none => rfl
  | some v =>
      rw [← ausR_schrumpf, ← ih_execBlock_ru_rest _ (Env.cons v ρ)]
      rfl

set_option linter.unusedSectionVars false in
theorem execBlock_ru_floatOf {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_l1}
    {zi_h1}
    (e)
    (lo)
    (hi)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlock_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB rest) (worldR σ) (envR ρ) = ausR (execBlock O passes R rest σ ρ))
    : execBlock O.mitRuhe passes R' (ruB (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ) = ausR (execBlock O passes R (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlock]
  rw [ruE_orte, lese_worldR, eval_ru]
  try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
  cases gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n) with
  | none => rfl
  | some v =>
      rw [← ausR_schrumpf, ← ih_execBlock_ru_rest _ (Env.cons v ρ)]
      rfl

set_option linter.unusedSectionVars false in
theorem execBlock_ru_floatNarrow {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_l1}
    {zi_h1}
    (e)
    (lo)
    (hi)
    (sonst)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlock_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB rest) (worldR σ) (envR ρ) = ausR (execBlock O passes R rest σ ρ))
    (ih_execEnd_ru_sonst : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd sonst) (worldR σ) (envR ρ) = endR (execEnd O passes R sonst σ ρ))
    : execBlock O.mitRuhe passes R' (ruB (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ) = ausR (execBlock O passes R (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlock]
  rw [ruE_orte, lese_worldR, eval_ru]
  try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
  cases gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x with
  | none => rw [← endR_zuAusgang, ih_execEnd_ru_sonst _ ρ]
  | some v =>
      rw [← ausR_schrumpf, ← ih_execBlock_ru_rest _ (Env.cons v ρ)]
      rfl

set_option linter.unusedSectionVars false in
theorem execEnd_ru_ret {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (e)
    (hΛ)
    (σ : World D)
    (ρ : Env D Γ)
    : execEnd O.mitRuhe passes R' (ruEnd (.ret e hΛ : Endblock D V l Γ Λ)) (worldR σ) (envR ρ) = endR (execEnd O passes R (.ret e hΛ : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEnd]
  erw [ruErg_orte, lese_worldR, evalErg_ru]
  rfl

set_option linter.unusedSectionVars false in
theorem execEnd_ru_retScoped {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (e)
    (R)
    (σ : World D)
    (ρ : Env D Γ)
    : execEnd O.mitRuhe passes R' (ruEnd (.retScoped e R : Endblock D V l Γ Λ)) (worldR σ) (envR ρ) = endR (execEnd O passes R (.retScoped e R : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEnd]
  erw [ruErg_orte, lese_worldR, evalErg_ru]
  rw [gibt_foldl_worldR]

set_option linter.unusedSectionVars false in
theorem execEnd_ru_retWhyScoped {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (r)
    (R)
    (σ : World D)
    (ρ : Env D Γ)
    : execEnd O.mitRuhe passes R' (ruEnd (.retWhyScoped r R : Endblock D V l Γ Λ)) (worldR σ) (envR ρ) = endR (execEnd O passes R (.retWhyScoped r R : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEnd]
  rw [gibt_foldl_worldR]

set_option linter.unusedSectionVars false in
theorem execEnd_ru_cons {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_Λ'}
    (s)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execStmt_ru_s : ∀ (σ : World D), ∀ (ρ : Env D _), execStmt O.mitRuhe passes R' (ruS s) (worldR σ) (envR ρ) = ausR (execStmt O passes R s σ ρ))
    (ih_execEnd_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd rest) (worldR σ) (envR ρ) = endR (execEnd O passes R rest σ ρ))
    : execEnd O.mitRuhe passes R' (ruEnd (.cons (Λ' := zi_Λ') s rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ) = endR (execEnd O passes R (.cons (Λ' := zi_Λ') s rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEnd]
  rw [ih_execStmt_ru_s σ ρ]
  cases execStmt O passes R s σ ρ with
  | ok σ' ρ' => exact ih_execEnd_ru_rest σ' ρ'
  | _ => rfl

end Haupt
end Gabbro.Grammatik
