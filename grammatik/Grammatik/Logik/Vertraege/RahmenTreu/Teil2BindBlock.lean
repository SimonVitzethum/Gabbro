/- Helpers for `RahmenTreu/Teil2` (pure moves): the long `bind` arms of
    `block_treu` as standalone theorems. Each takes the mutual induction
    hypotheses it needs as explicit premises, so the mutual block in
    `Teil2` stays whole and each arm becomes one application. -/
module

public import Grammatik.Logik.Vertraege.RahmenTreu.Tactics
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil1
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil4

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}
section Rumpf
variable (O : Orakel D)
variable (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable (hR : TreuR R) (hO : TreuO O)
include hR hO
set_option linter.unusedSectionVars false

/-! ## Block bind arms -/

theorem block_bindCall_treu (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
    (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0)
    (rest : Block D V l (τ :: Γ) (nach D f Λ) Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (τ :: Γ)), rest.ScopesOk →
      HeldB bo (nach D f Λ) σ.haelt →
      TreuAusgang V.schreibt V.gschreibt σ (execBlock O passes R rest σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.bindCall f args he hp hr rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    TreuAusgang V.schreibt V.gschreibt σ
      (execBlock O passes R (Block.bindCall f args he hp hr rest) σ ρ) := by
      intro σ' h
      simp only [execBlock] at h ⊢
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
      have hscope_rest : rest.ScopesOk := by scopes_treu
      generalize hR1 : R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = rv at h ⊢
      cases rv with
      | ok σ1 v =>
          frame_call_ok (σ.lese Λ args.orte)
          exact (TreuAusgang.vorCall g1 ((ih_rest rest σ1 _ hscope_rest
            (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))).schrumpf)) σ' h
      | why σ1 r => exact keinGrund hr r
      | logik _ => simp only [Ausgang.welt, reduceCtorEq] at h
      | hardware _ => simp only [Ausgang.welt, reduceCtorEq] at h

theorem block_bindCallInd_treu (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} {τ : Ty}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (he : (D.sigNr n).erg = some τ) (hp : RufPasst D V (D.sigNr n) Λ) (hr : (D.sigNr n).gruende = 0)
    (rest : Block D V l (τ :: Γ) (nachSig D (D.sigNr n) Λ) Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (τ :: Γ)), rest.ScopesOk →
      HeldB bo (nachSig D (D.sigNr n) Λ) σ.haelt →
      TreuAusgang V.schreibt V.gschreibt σ (execBlock O passes R rest σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.bindCallInd p args he hp hr rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    TreuAusgang V.schreibt V.gschreibt σ
      (execBlock O passes R (Block.bindCallInd p args he hp hr rest) σ ρ) := by
      intro σ' h
      simp only [execBlock] at h ⊢
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (p.orte ++ args.orte)
      have hscope_rest : rest.ScopesOk := by scopes_treu
      generalize hpv : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = pv at h ⊢
      obtain ⟨f, hf⟩ := pv
      simp only at h ⊢
      replace hp := RufPasst.vonPasst (D.passt_sig hf) hp
      generalize hR1 : R f (σ.lese Λ (p.orte ++ args.orte)) (umsig hf (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args (σ.lese Λ (p.orte ++ args.orte)) ρ)) = rv at h ⊢
      cases rv with
      | ok σ1 v =>
          frame_call_ok (σ.lese Λ (p.orte ++ args.orte))
          have g2 := ih_rest rest σ1 (.cons (ergWert (ergSig hf he) v) ρ) hscope_rest
            (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
          exact (TreuAusgang.vorCall g1 g2.schrumpf) σ' h
      | why σ1 r => exact keinGrundSig hf hr r
      | logik _ => simp only [Ausgang.welt, reduceCtorEq] at h
      | hardware _ => simp only [Ausgang.welt, reduceCtorEq] at h

theorem block_bindCallElse_treu (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
    (hp : RufPasst D V (D.signatur f) Λ) (hr : 0 < D.gruende f)
    (err : Endblock D V l (.why (D.gruende f) :: Γ) (nach D f Λ))
    (rest : Block D V l (τ :: Γ) (nach D f Λ) Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (τ :: Γ)), rest.ScopesOk →
      HeldB bo (nach D f Λ) σ.haelt →
      TreuAusgang V.schreibt V.gschreibt σ (execBlock O passes R rest σ ρ))
    (ih_err : ∀ (σ : World D) (ρ : Env D (.why (D.gruende f) :: Γ)), err.ScopesOk →
      HeldB bo (nach D f Λ) σ.haelt →
      TreuEnd V.schreibt V.gschreibt σ (execEnd O passes R err σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.bindCallElse f args he hp hr err rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    TreuAusgang V.schreibt V.gschreibt σ
      (execBlock O passes R (Block.bindCallElse f args he hp hr err rest) σ ρ) := by
      intro σ' h
      simp only [execBlock] at h ⊢
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
      have hscope_rest : rest.ScopesOk := by scopes_treu
      have hscope_err : err.ScopesOk := by scopes_treu
      generalize hR1 : R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = rv at h ⊢
      cases rv with
      | ok σ1 v =>
          frame_call_ok (σ.lese Λ args.orte)
          exact (TreuAusgang.vorCall g1 ((ih_rest rest σ1 _ hscope_rest
            (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))).schrumpf)) σ' h
      | why σ1 r =>
          frame_call_why (σ.lese Λ args.orte)
          exact (TreuAusgang.vorCall g1 ((ih_err err σ1 _ hscope_err
            (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))).schrumpf.zuAusgang)) σ' h
      | logik _ => simp only [Ausgang.welt, reduceCtorEq] at h
      | hardware _ => simp only [Ausgang.welt, reduceCtorEq] at h

theorem block_bindAxiom_treu (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Block D V l (τ :: Γ) Λ Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (τ :: Γ)), rest.ScopesOk →
      HeldB bo Λ σ.haelt →
      TreuAusgang V.schreibt V.gschreibt σ (execBlock O passes R rest σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.bindAxiom a args he hw hg hd hgd rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    TreuAusgang V.schreibt V.gschreibt σ
      (execBlock O passes R (Block.bindAxiom a args he hw hg hd hgd rest) σ ρ) := by
      intro σ' h
      simp only [execBlock] at h ⊢
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
      have hscope_rest : rest.ScopesOk := by scopes_treu
      generalize ha : axiomAntwort O a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = av at h ⊢
      rcases av with ⟨σ1, _ | v⟩
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
        rw [ha] at h1
        have g1 := hl.trans (Treu.weiter hw hg h1)
        exact (TreuAusgang.vorCall g1 ((ih_rest rest σ1 _ hscope_rest
          (g1.heldB hh)).schrumpf)) σ' h

theorem block_bindAxiomElse_treu (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
    (hr : 0 < D.agruende a)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (err : Endblock D V l (.why (D.agruende a) :: Γ) Λ)
    (rest : Block D V l (τ :: Γ) Λ Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (τ :: Γ)), rest.ScopesOk →
      HeldB bo Λ σ.haelt →
      TreuAusgang V.schreibt V.gschreibt σ (execBlock O passes R rest σ ρ))
    (ih_err : ∀ (σ : World D) (ρ : Env D (.why (D.agruende a) :: Γ)), err.ScopesOk →
      HeldB bo Λ σ.haelt →
      TreuEnd V.schreibt V.gschreibt σ (execEnd O passes R err σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.bindAxiomElse a args he hr hw hg hd hgd err rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    TreuAusgang V.schreibt V.gschreibt σ
      (execBlock O passes R (Block.bindAxiomElse a args he hr hw hg hd hgd err rest) σ ρ) := by
      intro σ' h
      simp only [execBlock] at h ⊢
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
      have hscope_rest : rest.ScopesOk := by scopes_treu
      have hscope_err : err.ScopesOk := by scopes_treu
      frame_axiom_else
      generalize ha : axiomAntwortSonst O a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = av at h ⊢
      rcases av with ⟨σ1, _ | (v | r)⟩
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · rw [ha] at h1
        have g1 := hl.trans (Treu.weiter hw hg h1)
        exact (TreuAusgang.vorCall g1 ((ih_rest rest σ1 _ hscope_rest (g1.heldB hh)).schrumpf)) σ' h
      · rw [ha] at h1
        have g1 := hl.trans (Treu.weiter hw hg h1)
        exact (TreuAusgang.vorCall g1 ((ih_err err σ1 _ hscope_err (g1.heldB hh)).schrumpf.zuAusgang)) σ' h

theorem block_bindAxiomOpt_treu (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (e : Option Ty) (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
    (he : D.aerg a = e) (hp : RufPasst D V (D.asignatur a) Λ)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Block D V l (ErgCtx Γ e) (nachSig D (D.asignatur a) Λ) Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (ErgCtx Γ e)), rest.ScopesOk →
      HeldB bo (nachSig D (D.asignatur a) Λ) σ.haelt →
      TreuAusgang V.schreibt V.gschreibt σ (execBlock O passes R rest σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.bindAxiomOpt e a args he hp hd hgd rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    TreuAusgang V.schreibt V.gschreibt σ
      (execBlock O passes R (Block.bindAxiomOpt e a args he hp hd hgd rest) σ ρ) := by
      intro σ' h
      simp only [execBlock] at h ⊢
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
      have hscope_rest : rest.ScopesOk := by scopes_treu
      generalize ha : axiomAntwort O a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = av at h ⊢
      rcases av with ⟨σ1, _ | v⟩
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
        rw [ha] at h1
        have g1 := hl.trans (Treu.weiter hp.hw hp.hg h1)
        have ihr := fun ρ' => ih_rest rest σ1 ρ' hscope_rest
          (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
        cases e with
        | none =>
            simp only [Ausgang.weiterOpt] at h; exact (TreuAusgang.vorCall g1 (ihr _)) σ' h
        | some τ =>
            simp only [Ausgang.weiterOpt] at h; exact (TreuAusgang.vorCall g1 ((ihr _).schrumpf)) σ' h

theorem block_bindAxiomOptElse_treu (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (e : Option Ty) (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
    (he : D.aerg a = e) (hp : RufPasst D V (D.asignatur a) Λ)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ) (hr : 0 < D.agruende a)
    (err : Endblock D V l (reasonTy (D.agruende a) :: Γ) (nachSig D (D.asignatur a) Λ))
    (rest : Block D V l (ErgCtx Γ e) (nachSig D (D.asignatur a) Λ) Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (ErgCtx Γ e)), rest.ScopesOk →
      HeldB bo (nachSig D (D.asignatur a) Λ) σ.haelt →
      TreuAusgang V.schreibt V.gschreibt σ (execBlock O passes R rest σ ρ))
    (ih_err : ∀ (σ : World D) (ρ : Env D (reasonTy (D.agruende a) :: Γ)), err.ScopesOk →
      HeldB bo (nachSig D (D.asignatur a) Λ) σ.haelt →
      TreuEnd V.schreibt V.gschreibt σ (execEnd O passes R err σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.bindAxiomOptElse e a args he hp hd hgd hr err rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    TreuAusgang V.schreibt V.gschreibt σ
      (execBlock O passes R (Block.bindAxiomOptElse e a args he hp hd hgd hr err rest) σ ρ) := by
      intro σ' h
      simp only [execBlock] at h ⊢
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
      have hscope_rest : rest.ScopesOk := by scopes_treu
      have hscope_err : err.ScopesOk := by scopes_treu
      frame_axiom_else
      generalize ha : axiomAntwortSonst O a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = av at h ⊢
      rcases av with ⟨σ1, _ | (v | r)⟩
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · rw [ha] at h1
        have g1 := hl.trans (Treu.weiter hp.hw hp.hg h1)
        have ihr := fun ρ' => ih_rest rest σ1 ρ' hscope_rest
          (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))
        cases e with
        | none =>
            simp only [Ausgang.weiterOpt] at h; exact (TreuAusgang.vorCall g1 (ihr _)) σ' h
        | some τ =>
            simp only [Ausgang.weiterOpt] at h; exact (TreuAusgang.vorCall g1 ((ihr _).schrumpf)) σ' h
      · rw [ha] at h1
        have g1 := hl.trans (Treu.weiter hp.hw hp.hg h1)
        exact (TreuAusgang.vorCall g1 ((ih_err err σ1 _ hscope_err
          (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))).schrumpf.zuAusgang)) σ' h

theorem block_regReadElse_treu (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
    (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (D.rtyp r :: Γ) Λ Λ')
    (ih_rest : ∀ (σ : World D) (ρ : Env D (D.rtyp r :: Γ)), rest.ScopesOk →
      HeldB bo Λ σ.haelt →
      TreuAusgang V.schreibt V.gschreibt σ (execBlock O passes R rest σ ρ))
    (ih_sonst : ∀ (σ : World D) (ρ : Env D Γ), sonst.ScopesOk →
      HeldB bo Λ σ.haelt →
      TreuEnd V.schreibt V.gschreibt σ (execEnd O passes R sonst σ ρ))
    (σ : World D) (ρ : Env D Γ)
    (hscope : (Block.regReadElse r hk zusage sonst rest).ScopesOk)
    (hh : HeldB bo Λ σ.haelt) :
    TreuAusgang V.schreibt V.gschreibt σ
      (execBlock O passes R (Block.regReadElse r hk zusage sonst rest) σ ρ) := by
      intro σ' h
      have hscope_rest : rest.ScopesOk := by scopes_treu
      have hscope_sonst : sonst.ScopesOk := by scopes_treu
      simp only [execBlock] at h ⊢
      refine (TreuAusgang.vor (treu_fragt σ (.inr (.inl r))) ?_) σ' h; intro σ' h
      rw [← fragt_haelt σ (.inr (.inl r))] at hh
      generalize σ.fragt (.inr (.inl r)) = σ at h hh ⊢
      generalize hv : einpassen O.zeiger (D.rtyp r) (O.regLies r σ) = ov at h ⊢
      cases ov with
      | some v =>
        have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ zusage.orte
        by_cases hc : wahr? (eval (σ.lese Λ zusage.orte) zusage (σ.lese Λ zusage.orte) (.cons v ρ)) = true <;> simp only [hc, ite_true, ite_false, Bool.true_eq_false, Bool.false_eq_true] at h ⊢
        · exact (TreuAusgang.vor hl (ih_rest rest _ _ hscope_rest (hl.heldB hh))).schrumpf σ' h
        · exact (TreuEnd.vor hl (ih_sonst sonst _ ρ hscope_sonst (hl.heldB hh))).zuAusgang σ' h
      | none => simp only [Ausgang.welt, reduceCtorEq] at h


end Rumpf

end Gabbro.Grammatik
