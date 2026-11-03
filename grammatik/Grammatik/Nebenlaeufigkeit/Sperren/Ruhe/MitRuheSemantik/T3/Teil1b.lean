/- Part 3 of 4 of `MitRuheSemantik` (split by instrumente/teile/lean-teilen.py; the umbrella `MitRuheSemantik.lean` imports all parts). -/
module
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik.T3.Teil1Control
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
      · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply, id]
        erw [execEnd_umΛ]
        exact (congrArg (fun a => (EndAusgang.schrumpf a).zuAusgang) (ih_execEnd_ru_err σ' (Env.cons r ρ))).trans
          ((congrArg EndAusgang.zuAusgang (endR_schrumpf _)).trans (endR_zuAusgang _))

end Haupt
end Gabbro.Grammatik
