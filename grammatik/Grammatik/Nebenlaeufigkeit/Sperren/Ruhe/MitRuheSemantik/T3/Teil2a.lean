module

public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik.T2
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik.T3.Teil1Control
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik.T3.Teil1b

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
theorem execStmt_ru_regWrite {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (r)
    (hk)
    (e)
    (σ : World D)
    (ρ : Env D Γ)
    : execStmt O.mitRuhe passes R' (ruS (.regWrite r hk e : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.regWrite r hk e : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmt]
  rw [ruE_orte, lese_worldR]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmt_ru_publish {V : Vertrag D}
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
    : execStmt O.mitRuhe passes R' (ruS (.publish g e payload hp hw hL : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.publish g e payload hp hw hL : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmt]
  rw [ruE_orte, lese_worldR, eval_ru, schreibGlob_worldR]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmt_ru_ret {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (e)
    (hΛ)
    (σ : World D)
    (ρ : Env D Γ)
    : execStmt O.mitRuhe passes R' (ruS (.ret e hΛ : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.ret e hΛ : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmt]
  erw [ruErg_orte, lese_worldR, evalErg_ru]
  rfl

set_option linter.unusedSectionVars false in
theorem execStmt_ru_retScoped {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (e)
    (cleanup)
    (σ : World D)
    (ρ : Env D Γ)
    : execStmt O.mitRuhe passes R' (ruS (.retScoped e cleanup : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.retScoped e cleanup : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmt]
  erw [ruErg_orte, lese_worldR, evalErg_ru]
  rw [gibt_foldl_worldR]

set_option linter.unusedSectionVars false in
theorem execStmt_ru_retWhyScoped {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (r)
    (cleanup)
    (σ : World D)
    (ρ : Env D Γ)
    : execStmt O.mitRuhe passes R' (ruS (.retWhyScoped r cleanup : Stmt D V l Γ Λ _)) (worldR σ) (envR ρ) = ausR (execStmt O passes R (.retWhyScoped r cleanup : Stmt D V l Γ Λ _) σ ρ) :=
  by
  simp only [ruS, execStmt]
  rw [gibt_foldl_worldR]

set_option linter.unusedSectionVars false in
theorem execBlock_ru_cons {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_Λ'}
    (s)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execStmt_ru_s : ∀ (σ : World D), ∀ (ρ : Env D _), execStmt O.mitRuhe passes R' (ruS s) (worldR σ) (envR ρ) = ausR (execStmt O passes R s σ ρ))
    (ih_execBlock_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB rest) (worldR σ) (envR ρ) = ausR (execBlock O passes R rest σ ρ))
    : execBlock O.mitRuhe passes R' (ruB (.cons (Λ' := zi_Λ') s rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ) = ausR (execBlock O passes R (.cons (Λ' := zi_Λ') s rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlock]
  rw [ih_execStmt_ru_s σ ρ]
  cases execStmt O passes R s σ ρ with
  | ok σ' ρ' => exact ih_execBlock_ru_rest σ' ρ'
  | _ => rfl

set_option linter.unusedSectionVars false in
theorem execBlock_ru_bind {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_τ}
    (e)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlock_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB rest) (worldR σ) (envR ρ) = ausR (execBlock O passes R rest σ ρ))
    : execBlock O.mitRuhe passes R' (ruB (.bind (τ := zi_τ) e rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ) = ausR (execBlock O passes R (.bind (τ := zi_τ) e rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlock]
  rw [ruE_orte, lese_worldR, eval_ru, ← ausR_schrumpf, ← ih_execBlock_ru_rest _ _]
  rfl

set_option linter.unusedSectionVars false in
theorem execBlock_ru_bindCall {V : Vertrag D}
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
    (ih_execBlock_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB rest) (worldR σ) (envR ρ) = ausR (execBlock O passes R rest σ ρ))
    : execBlock O.mitRuhe passes R' (ruB (.bindCall (τ := zi_τ) g args he hp hr rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ) = ausR (execBlock O passes R (.bindCall (τ := zi_τ) g args he hp hr rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlock]
  erw [ruA_orte, lese_worldR, evalArgs_ru, hR]
  cases hx : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | ok σ' v =>
      try erw [hx]
      simp only [rufR]
      erw [execBlock_vorΛ, ergWert_ru he]
      exact (congrArg Ausgang.schrumpf (ih_execBlock_ru_rest σ' (Env.cons (ergWert he v) ρ))).trans
        (ausR_schrumpf _)
  | why σ' r => exact (Fin.cast hr r).elim0
  | logik e => (try erw [hx]); rfl
  | hardware e => (try erw [hx]); rfl

set_option linter.unusedSectionVars false in
theorem execBlock_ru_bindCallInd {V : Vertrag D}
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
    (ih_execBlock_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB rest) (worldR σ) (envR ρ) = ausR (execBlock O passes R rest σ ρ))
    : execBlock O.mitRuhe passes R' (ruB (.bindCallInd (τ := zi_τ) (n := n) p args he hp hr rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ) = ausR (execBlock O passes R (.bindCallInd (τ := zi_τ) (n := n) p args he hp hr rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlock]
  erw [show (ruE p).orte ++ (ruA args).orte = p.orte ++ args.orte from
    kongr₂ (· ++ ·) (ruE_orte p) (ruA_orte args)]
  erw [lese_worldR, eval_ru, evalArgs_ru]
  cases h : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ with
  | mk g hg =>
      rw [valR_fnptr]
      dsimp only
      erw [umsig_ru hg, hR]
      cases hx : R g (σ.lese Λ (p.orte ++ args.orte)) (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
      | ok σ' v =>
          try erw [hx]
          simp only [rufR]
          erw [execBlock_vorΛ, ergWert_ru (ergSig hg he)]
          exact (congrArg Ausgang.schrumpf
            (ih_execBlock_ru_rest σ' (Env.cons (ergWert (ergSig hg he) v) ρ))).trans (ausR_schrumpf _)
      | why σ' r => exact keinGrundSig hg hr r
      | logik e => (try erw [hx]); rfl
      | hardware e => (try erw [hx]); rfl

set_option linter.unusedSectionVars false in
theorem execBlock_ru_bindCallIndElse {V : Vertrag D}
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
    (ih_execBlock_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB rest) (worldR σ) (envR ρ) = ausR (execBlock O passes R rest σ ρ))
    (ih_execEnd_ru_err : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd err) (worldR σ) (envR ρ) = endR (execEnd O passes R err σ ρ))
    : execBlock O.mitRuhe passes R' (ruB (.bindCallIndElse (τ := zi_τ) (n := n) p args he hp hr err rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ) = ausR (execBlock O passes R (.bindCallIndElse (τ := zi_τ) (n := n) p args he hp hr err rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlock, indSonst]
  erw [show (ruE p).orte ++ (ruA args).orte = p.orte ++ args.orte from
    kongr₂ (· ++ ·) (ruE_orte p) (ruA_orte args)]
  erw [lese_worldR, eval_ru, evalArgs_ru]
  cases h : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ with
  | mk g hg =>
      rw [valR_fnptr]
      dsimp only
      erw [umsig_ru hg, hR]
      cases hx : R g (σ.lese Λ (p.orte ++ args.orte)) (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
      | ok σ' v =>
          try erw [hx]
          simp only [rufR]
          erw [execBlock_vorΛ, ergWert_ru (ergSig hg he)]
          exact (congrArg Ausgang.schrumpf
            (ih_execBlock_ru_rest σ' (Env.cons (ergWert (ergSig hg he) v) ρ))).trans (ausR_schrumpf _)
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
theorem execBlock_ru_bindCallElse {V : Vertrag D}
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
    (ih_execBlock_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execBlock O.mitRuhe passes R' (ruB rest) (worldR σ) (envR ρ) = ausR (execBlock O passes R rest σ ρ))
    (ih_execEnd_ru_err : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd err) (worldR σ) (envR ρ) = endR (execEnd O passes R err σ ρ))
    : execBlock O.mitRuhe passes R' (ruB (.bindCallElse (τ := zi_τ) g args he hp hr err rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ) = ausR (execBlock O passes R (.bindCallElse (τ := zi_τ) g args he hp hr err rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlock]
  erw [ruA_orte, lese_worldR, evalArgs_ru, hR]
  cases hx : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | ok σ' v =>
      try erw [hx]
      simp only [rufR]
      erw [execBlock_vorΛ, ergWert_ru he]
      exact (congrArg Ausgang.schrumpf (ih_execBlock_ru_rest σ' (Env.cons (ergWert he v) ρ))).trans
        (ausR_schrumpf _)
  | why σ' r =>
      try erw [hx]
      simp only [rufR]
      erw [execEnd_umΛ]
      exact (congrArg (fun a => EndAusgang.zuAusgang (EndAusgang.schrumpf a))
        (ih_execEnd_ru_err σ' (Env.cons r ρ))).trans
        ((congrArg EndAusgang.zuAusgang (endR_schrumpf _)).trans (endR_zuAusgang _))
  | logik e => (try erw [hx]); rfl
  | hardware e => (try erw [hx]); rfl


end Haupt

end Gabbro.Grammatik
