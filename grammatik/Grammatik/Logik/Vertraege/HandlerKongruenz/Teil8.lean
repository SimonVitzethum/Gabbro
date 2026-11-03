/-
  File:      Grammatik/HandlerKongruenz/Teil8.lean
  Subject:   **CONGRUENCE UNDER AN ERROR SET: REMAINING ARMS** -- the three
              fused arms that fit neither the Block nor the Endblock helper
              files (`bindAxiomOptElse`/`regReadElse` for blocks, `narrow`
              for terminal blocks).
-/
module

public import Grammatik.Kern.Syntax.Satz
public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.Logik.Vertraege.RahmenTreu.Tactics
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil1
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil2
public import Grammatik.Logik.Vertraege.HandlerKongruenz.Teil1
@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}
section KongruenzDiszRest
variable (O : Orakel D) (passes : Nat)
  (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  {Er : Fehlermarke D → Prop}
  (hR : ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)),
    HeldB (D.signatur g).boden (Signatur.anfang D (D.signatur g)) σ.haelt →
    RufUnter Er (R₁ g σ ρ) (R₂ g σ ρ))
  (hT₁ : TreuR R₁) (hO : TreuO O)
include hR hT₁ hO
set_option linter.unusedSectionVars false

theorem block_bindAxiomOptElse_unter (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (e : Option Ty) (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
    (he : D.aerg a = e) (hp : RufPasst D V (D.asignatur a) Λ)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ) (hr : 0 < D.agruende a)
    (err : Endblock D V l (reasonTy (D.agruende a) :: Γ) (nachSig D (D.asignatur a) Λ))
    (rest : Block D V l (ErgCtx Γ e) (nachSig D (D.asignatur a) Λ) Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (ErgCtx Γ e)), rest.ScopesOk →
      HeldB bo (nachSig D (D.asignatur a) Λ) σ.haelt →
      AusgangUnter Er (execBlock O passes R₁ rest σ ρ) (execBlock O passes R₂ rest σ ρ))
    (ih_err : ∀ (σ : World D) (ρ : Env D (reasonTy (D.agruende a) :: Γ)), err.ScopesOk →
      HeldB bo (nachSig D (D.asignatur a) Λ) σ.haelt →
      EndUnter Er (execEnd O passes R₁ err σ ρ) (execEnd O passes R₂ err σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.bindAxiomOptElse e a args he hp hd hgd hr err rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    AusgangUnter Er
      (execBlock O passes R₁ (Block.bindAxiomOptElse e a args he hp hd hgd hr err rest) σ ρ)
      (execBlock O passes R₂ (Block.bindAxiomOptElse e a args he hp hd hgd hr err rest) σ ρ) := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hscope_err : err.ScopesOk := by scopes_treu
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
  have ihr := fun σ ρ => ih_rest σ ρ hscope_rest
  have ihe := fun σ ρ => ih_err σ ρ hscope_err
  cases e with
  | none =>
      simp only [execBlock, Ausgang.weiterOpt]
      cases hx : axiomAntwortSonst O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ1 ov =>
          rcases ov with _ | v | r
          · exact AusgangUnter.refl _
          · have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
              (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
            rw [hx] at h1
            simp only [hx] at ⊢
            have g1 := hl.trans (Treu.weiter hp.hw hp.hg h1)
            have heq := ihr σ1 _
              (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
            exact heq
          · have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
              (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
            rw [hx] at h1
            simp only [hx] at ⊢
            have g1 := hl.trans (Treu.weiter hp.hw hp.hg h1)
            have heq := (ihe σ1 _
              (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))).schrumpf
            simp only [hx] at ⊢
            exact heq.zuAusgang
  | some τ =>
      simp only [execBlock, Ausgang.weiterOpt]
      cases hx : axiomAntwortSonst O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ1 ov =>
          rcases ov with _ | v | r
          · exact AusgangUnter.refl _
          · have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
              (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
            rw [hx] at h1
            simp only [hx] at ⊢
            have g1 := hl.trans (Treu.weiter hp.hw hp.hg h1)
            have heq := (ihr σ1 _
              (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))).schrumpf
            simp only [hx] at ⊢
            exact heq
          · have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
              (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
            rw [hx] at h1
            simp only [hx] at ⊢
            have g1 := hl.trans (Treu.weiter hp.hw hp.hg h1)
            have heq := (ihe σ1 _
              (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))).schrumpf
            simp only [hx] at ⊢
            exact heq

theorem block_regReadElse_unter (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
    (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (D.rtyp r :: Γ) Λ Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (D.rtyp r :: Γ)), rest.ScopesOk →
      HeldB bo Λ σ.haelt →
      AusgangUnter Er (execBlock O passes R₁ rest σ ρ) (execBlock O passes R₂ rest σ ρ))
    (ih_sonst : ∀ (σ : World D) (ρ : Env D Γ), sonst.ScopesOk →
      HeldB bo Λ σ.haelt →
      EndUnter Er (execEnd O passes R₁ sonst σ ρ) (execEnd O passes R₂ sonst σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.regReadElse r hk zusage sonst rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    AusgangUnter Er (execBlock O passes R₁ (Block.regReadElse r hk zusage sonst rest) σ ρ)
      (execBlock O passes R₂ (Block.regReadElse r hk zusage sonst rest) σ ρ) := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hscope_sonst : sonst.ScopesOk := by scopes_treu
  simp only [execBlock]
  have hl0 := treu_fragt σ (.inr (.inl r))
  rw [← fragt_haelt σ (.inr (.inl r))] at hh
  generalize hg : σ.fragt (.inr (.inl r)) = σq at hh ⊢
  cases hx : einpassen O.zeiger (D.rtyp r) (O.regLies r σq) with
  | none => exact AusgangUnter.refl _
  | some v =>
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σq Λ zusage.orte
      by_cases hc : wahr? (eval (σq.lese Λ zusage.orte) zusage
          (σq.lese Λ zusage.orte) (.cons v ρ)) = true <;>
        simp only [hx, hc, ite_true, ite_false] at ⊢
      · have heq := ih_rest _ _ hscope_rest (hl.heldB hh)
        simp only [hx] at ⊢
        exact heq.schrumpf
      · have heq := ih_sonst _ _ hscope_sonst (hl.heldB hh)
        simp only [hx] at ⊢
        exact heq.zuAusgang

theorem end_narrow_unter (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {lo hi lo' hi' : Int}
    (e : Expr D Γ Λ (.int lo hi)) (sonst : Endblock D V l Γ Λ)
    (rest : Endblock D V l (.int lo' hi' :: Γ) Λ)
    (ih_rest : ∀ (σ : World D) (ρ : Env D (.int lo' hi' :: Γ)), rest.ScopesOk →
      HeldB bo Λ σ.haelt →
      EndUnter Er (execEnd O passes R₁ rest σ ρ) (execEnd O passes R₂ rest σ ρ))
    (ih_sonst : ∀ (σ : World D) (ρ : Env D Γ), sonst.ScopesOk →
      HeldB bo Λ σ.haelt →
      EndUnter Er (execEnd O passes R₁ sonst σ ρ) (execEnd O passes R₂ sonst σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Endblock.narrow e lo' hi' sonst rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    EndUnter Er (execEnd O passes R₁ (Endblock.narrow e lo' hi' sonst rest) σ ρ)
      (execEnd O passes R₂ (Endblock.narrow e lo' hi' sonst rest) σ ρ) := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hscope_sonst : sonst.ScopesOk := by scopes_treu
  simp only [execEnd]
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
  by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
    (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi' <;>
    simp only [hc, dif_pos, dif_neg] at ⊢
  · exact (ih_rest _ _ hscope_rest (hl.heldB hh)).schrumpf
  · exact ih_sonst _ _ hscope_sonst (hl.heldB hh)

theorem end_regReadElse_unter (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
    (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock D V l Γ Λ)
    (rest : Endblock D V l (D.rtyp r :: Γ) Λ)
    (ih_rest : ∀ (σ : World D) (ρ : Env D (D.rtyp r :: Γ)), rest.ScopesOk →
      HeldB bo Λ σ.haelt →
      EndUnter Er (execEnd O passes R₁ rest σ ρ) (execEnd O passes R₂ rest σ ρ))
    (ih_sonst : ∀ (σ : World D) (ρ : Env D Γ), sonst.ScopesOk →
      HeldB bo Λ σ.haelt →
      EndUnter Er (execEnd O passes R₁ sonst σ ρ) (execEnd O passes R₂ sonst σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Endblock.regReadElse r hk zusage sonst rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    EndUnter Er (execEnd O passes R₁ (Endblock.regReadElse r hk zusage sonst rest) σ ρ)
      (execEnd O passes R₂ (Endblock.regReadElse r hk zusage sonst rest) σ ρ) := by
  have hscope_rest : rest.ScopesOk := by scopes_treu
  have hscope_sonst : sonst.ScopesOk := by scopes_treu
  simp only [execEnd]
  have hl0 := treu_fragt σ (.inr (.inl r))
  rw [← fragt_haelt σ (.inr (.inl r))] at hh
  generalize hg : σ.fragt (.inr (.inl r)) = σq at hh ⊢
  cases hx : einpassen O.zeiger (D.rtyp r) (O.regLies r σq) with
  | none => exact EndUnter.refl _
  | some v =>
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σq Λ zusage.orte
      by_cases hc : wahr? (eval (σq.lese Λ zusage.orte) zusage
          (σq.lese Λ zusage.orte) (.cons v ρ)) = true <;>
        simp only [hx, hc, ite_true, ite_false] at ⊢
      · have heq := ih_rest _ _ hscope_rest (hl.heldB hh)
        simp only [hx] at ⊢
        exact heq.schrumpf
      · have heq := ih_sonst _ _ hscope_sonst (hl.heldB hh)
        simp only [hx] at ⊢
        exact heq

end KongruenzDiszRest
end Gabbro.Grammatik
