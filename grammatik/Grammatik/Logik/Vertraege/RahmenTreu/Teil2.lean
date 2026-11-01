module

public import Grammatik.Kern.Syntax.Satz
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil1

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

mutual

/-- **The frame and the held locks of one statement**, at EVERY world. -/
theorem stmt_treu :
    ∀ (s : Stmt D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ),
    TreuAusgang V.schreibt V.gschreibt σ (execStmt O passes R s σ ρ)
  | .assignSlot t f i e hw hL, σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact (treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _).trans
        (treu_schreibSlot _ t Λ _ f _ hw)
  | .assignThru p t _ f i e hw hL, σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact (treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _).trans
        (treu_schreibSlot _ t Λ _ f _ hw)
  | .assignSlotRef r t _ _ f e hw hL, σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact (treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _).trans
        (treu_schreibSlot _ t Λ _ f _ hw)
  | .assignGlob g e hw hL, σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact (treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _).trans
        (treu_schreibGlob _ g Λ _ hw)
  | .putBytes t f hf n i _ _ e hw hL, σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact (treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _).trans
        (treu_schreibBytes _ t f hf Λ hw _ _)
  | .assignVar x e, σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact treu_lese σ Λ _
  | .shift t f hτ i von nach hn he hw hL, σ, ρ, σ', h => by
      simp only [execStmt] at h
      split at h
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        exact (treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _).trans
          (treu_schreibSlot _ t Λ _ f _ hw)
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .ite c t e, σ, ρ, σ', h => by
      simp only [execStmt] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ c.orte
      split at h
      · exact (TreuAusgang.vor hl (block_treu t _ ρ)) σ' h
      · exact (TreuAusgang.vor hl (block_treu e _ ρ)) σ' h
  | .onOption o p a, σ, ρ, σ', h => by
      simp only [execStmt] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ o.orte
      split at h
      · exact (TreuAusgang.vor hl (block_treu p _ _)).schrumpf σ' h
      · exact (TreuAusgang.vor hl (block_treu a _ ρ)) σ' h
  | .onTag v arms, σ, ρ, σ', h => by
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ v.orte
      exact (TreuAusgang.vor hl (arms_treu arms _ _ ρ)) σ' h
  | .onWhy r arms, σ, ρ, σ', h => by
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ r.orte
      exact (TreuAusgang.vor hl (grund_treu arms _ _ ρ)) σ' h
  | .call f args hp hr, σ, ρ, σ', h => by
      simp only [execStmt] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
      split at h
      · rename_i σ1 v hR1
        simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        exact hl.trans (Treu.weiter hp.hw hp.hg
          (hR f (σ.lese Λ args.orte) _ σ1 (by rw [hR1]; rfl)))
      · rename_i σ1 r _; exact keinGrund hr r
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .callInd p args hp hr, σ, ρ, σ', h => by
      simp only [execStmt] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (p.orte ++ args.orte)
      generalize hpv : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = pv at h
      obtain ⟨f, hf⟩ := pv
      simp only at h
      split at h
      · rename_i σ1 v hR1
        simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        replace hp := RufPasst.vonPasst (D.passt_sig hf) hp
        exact hl.trans (Treu.weiter hp.hw hp.hg
          (hR f (σ.lese Λ (p.orte ++ args.orte)) _ σ1 (by rw [hR1]; rfl)))
      · rename_i σ1 r _; exact keinGrundSig hf hr r
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .locks L hr body, σ, ρ, σ', h =>
      (TreuAusgang.gibt L (block_treu body (σ.nimmt L) ρ)) σ' h
  | .breaking _ body, σ, ρ, σ', h => block_treu body σ ρ σ' h
  | .traverse t inv body, σ, ρ, σ', h =>
      traverseLauf_treu _ _ (fun σ ρ => block_treu body σ ρ)
        (fun σ ρ => treu_lese σ Λ inv.orte) _ σ ρ σ' h
  | .retry n bis body ueberlauf, σ, ρ, σ', h =>
      retryLauf_treu _ _ _ (fun σ ρ => block_treu body σ ρ)
        (fun σ ρ => treu_lese σ Λ bis.orte)
        (fun σ ρ => block_treu ueberlauf σ ρ) n σ ρ σ' h
  | .forever a inv body, σ, ρ, σ', h =>
      foreverLauf_treu a _ _ (fun σ ρ => block_treu body σ ρ)
        (fun σ ρ => treu_lese σ Λ inv.orte) passes σ ρ σ' h
  | .axiomCall a args _ hw hg hd hgd, σ, ρ, σ', h => by
      simp only [execStmt] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
      split at h
      · rename_i σ1 v ha
        simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        have := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
        rw [ha] at this
        exact hl.trans (Treu.weiter hw hg this)
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .regWrite r _ e, σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact treu_lese σ Λ _
  | .transition .., σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _
  | .publish g e _ _ hw hL, σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact (treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _).trans
        (treu_schreibGlob _ g Λ _ hw)
  | .advances .., σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _
  | .retires .., σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _
  | .ret e _, σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact treu_lese σ Λ _
  | .retWhy .., σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _
  | .leave _, σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _
  | .next _, σ, ρ, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _

theorem block_treu :
    ∀ (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ),
    TreuAusgang V.schreibt V.gschreibt σ (execBlock O passes R b σ ρ)
  | .nil, σ, ρ, σ', h => by
      simp only [execBlock, Ausgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _
  | .cons s rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      split at h
      · rename_i σ1 ρ1 hs
        have g1 := stmt_treu s σ ρ σ1 (by rw [hs]; rfl)
        exact g1.trans (block_treu rest σ1 ρ1 σ' h)
      · subst_vars
        exact stmt_treu s σ ρ σ' h
  | .bind e rest, σ, ρ, σ', h => by
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
      exact (TreuAusgang.vor hl (block_treu rest _ _)).schrumpf σ' h
  | .bindCall f args he hp hr rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
      split at h
      · rename_i σ1 v hR1
        have g1 := hl.trans (Treu.weiter hp.hw hp.hg
          (hR f (σ.lese Λ args.orte) _ σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((block_treu rest σ1 _).schrumpf σ' h)
      · rename_i σ1 r _; exact keinGrund hr r
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .bindCallInd p args he hp hr rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (p.orte ++ args.orte)
      generalize hpv : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = pv at h
      obtain ⟨f, hf⟩ := pv
      simp only at h
      split at h
      · rename_i σ1 v hR1
        have g2 := block_treu rest σ1 (.cons (ergWert (ergSig hf he) v) ρ)
        replace hp := RufPasst.vonPasst (D.passt_sig hf) hp
        have g1 := hl.trans (Treu.weiter hp.hw hp.hg
          (hR f (σ.lese Λ (p.orte ++ args.orte)) _ σ1 (by rw [hR1]; rfl)))
        exact g1.trans (g2.schrumpf σ' h)
      · rename_i σ1 r _; exact keinGrundSig hf hr r
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .bindCallElse f args he hp _ err rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
      split at h
      · rename_i σ1 v hR1
        have g1 := hl.trans (Treu.weiter hp.hw hp.hg
          (hR f (σ.lese Λ args.orte) _ σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((block_treu rest σ1 _).schrumpf σ' h)
      · rename_i σ1 r hR1
        have g1 := hl.trans (Treu.weiter hp.hw hp.hg
          (hR f (σ.lese Λ args.orte) _ σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((end_treu err σ1 _).schrumpf.zuAusgang σ' h)
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .bindAxiom a args he hw hg hd hgd rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
      split at h
      · rename_i σ1 v ha
        have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
        rw [ha] at h1
        have g1 := hl.trans (Treu.weiter hw hg h1)
        exact g1.trans ((block_treu rest σ1 _).schrumpf σ' h)
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .bindAxiomElse a args he hr hw hg hd hgd err rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
      have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
      rw [← axiomAntwortSonst_fst] at h1
      split at h
      · rename_i σ1 v ha
        rw [ha] at h1
        have g1 := hl.trans (Treu.weiter hw hg h1)
        exact g1.trans ((block_treu rest σ1 _).schrumpf σ' h)
      · rename_i σ1 r ha
        rw [ha] at h1
        have g1 := hl.trans (Treu.weiter hw hg h1)
        exact g1.trans ((end_treu err σ1 _).schrumpf.zuAusgang σ' h)
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .regRead r _ rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      refine (treu_fragt σ (.inr (.inl r))).trans ?_
      generalize σ.fragt (.inr (.inl r)) = σ at h ⊢
      split at h
      · split at h
        · exact (block_treu rest σ _).schrumpf σ' h
        · simp only [Ausgang.welt, reduceCtorEq] at h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .regReadElse r _ zusage sonst rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      refine (treu_fragt σ (.inr (.inl r))).trans ?_
      generalize σ.fragt (.inr (.inl r)) = σ at h ⊢
      split at h
      · have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ zusage.orte
        split at h
        · exact (TreuAusgang.vor hl (block_treu rest _ _)).schrumpf σ' h
        · exact (TreuEnd.vor hl (end_treu sonst _ ρ)).zuAusgang σ' h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .awaits g _ _ hL _ rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      refine (treu_fragt σ (.inr (.inr g))).trans ?_
      generalize σ.fragt (.inr (.inr g)) = σ at h ⊢
      split at h
      · have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ [.inr g]
        exact (TreuAusgang.vor hl (block_treu rest _ _)).schrumpf σ' h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .exchange g neu hw hL rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (.inr g :: neu.orte)
      have g1 := hl.trans (treu_schreibGlob (W := V.schreibt) (G := V.gschreibt)
        (σ.lese Λ (.inr g :: neu.orte)) g Λ (eval (σ.lese Λ (.inr g :: neu.orte)) neu
          (σ.lese Λ (.inr g :: neu.orte)) (.cons ((σ.lese Λ (.inr g :: neu.orte)).globs g) ρ))
          hw)
      exact (TreuAusgang.vor g1 (block_treu rest _ _)).schrumpf σ' h
  | .narrow e lo' hi' sonst rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
      split at h
      · exact (TreuAusgang.vor hl (block_treu rest _ _)).schrumpf σ' h
      · exact (TreuEnd.vor hl (end_treu sonst _ ρ)).zuAusgang σ' h
  | .check c sonst rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ c.orte
      split at h
      · exact (TreuAusgang.vor hl (block_treu rest _ ρ)) σ' h
      · exact (TreuEnd.vor hl (end_treu sonst _ ρ)).zuAusgang σ' h
  | .float op a b lo hi rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (a.orte ++ b.orte)
      split at h
      · exact (TreuAusgang.vor hl (block_treu rest _ _)).schrumpf σ' h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .floatLit q lo hi rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      split at h
      · exact (block_treu rest σ _).schrumpf σ' h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .floatOf e lo hi rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
      split at h
      · exact (TreuAusgang.vor hl (block_treu rest _ _)).schrumpf σ' h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .floatNarrow e lo hi sonst rest, σ, ρ, σ', h => by
      simp only [execBlock] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
      split at h
      · exact (TreuAusgang.vor hl (block_treu rest _ _)).schrumpf σ' h
      · exact (TreuEnd.vor hl (end_treu sonst _ ρ)).zuAusgang σ' h

theorem end_treu :
    ∀ (b : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ),
    TreuEnd V.schreibt V.gschreibt σ (execEnd O passes R b σ ρ)
  | .ret e _, σ, ρ, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h
      exact treu_lese σ Λ _
  | .retWhy .., σ, ρ, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _
  | .leave _, σ, ρ, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _
  | .next _, σ, ρ, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _
  | .cons s rest, σ, ρ, σ', h => by
      simp only [execEnd] at h
      have hs := stmt_treu s σ ρ
      split at h
      · rename_i σ1 ρ1 hs1
        have g1 := hs σ1 (by rw [hs1]; rfl)
        exact g1.trans (end_treu rest σ1 ρ1 σ' h)
      all_goals first
        | (rename_i hs1; simp only [EndAusgang.welt, Option.some.injEq] at h; subst h
           exact hs _ (by rw [hs1]; rfl))
        | (simp only [EndAusgang.welt, reduceCtorEq] at h)
  | .bind e rest, σ, ρ, σ', h => by
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
      exact (TreuEnd.vor hl (end_treu rest _ _)).schrumpf σ' h
  | .bindCall f args he hp hr rest, σ, ρ, σ', h => by
      simp only [execEnd] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
      split at h
      · rename_i σ1 v hR1
        have g1 := hl.trans (Treu.weiter hp.hw hp.hg
          (hR f (σ.lese Λ args.orte) _ σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((end_treu rest σ1 _).schrumpf σ' h)
      · rename_i σ1 r _; exact keinGrund hr r
      · simp only [EndAusgang.welt, reduceCtorEq] at h
      · simp only [EndAusgang.welt, reduceCtorEq] at h
  | .bindCallElse f args he hp _ err rest, σ, ρ, σ', h => by
      simp only [execEnd] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
      split at h
      · rename_i σ1 v hR1
        have g1 := hl.trans (Treu.weiter hp.hw hp.hg
          (hR f (σ.lese Λ args.orte) _ σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((end_treu rest σ1 _).schrumpf σ' h)
      · rename_i σ1 r hR1
        have g1 := hl.trans (Treu.weiter hp.hw hp.hg
          (hR f (σ.lese Λ args.orte) _ σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((end_treu err σ1 _).schrumpf σ' h)
      · simp only [EndAusgang.welt, reduceCtorEq] at h
      · simp only [EndAusgang.welt, reduceCtorEq] at h
  | .bindAxiom a args he hw hg hd hgd rest, σ, ρ, σ', h => by
      simp only [execEnd] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
      split at h
      · rename_i σ1 v ha
        have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
        rw [ha] at h1
        have g1 := hl.trans (Treu.weiter hw hg h1)
        exact g1.trans ((end_treu rest σ1 _).schrumpf σ' h)
      · simp only [EndAusgang.welt, reduceCtorEq] at h
  | .bindAxiomElse a args he hr hw hg hd hgd err rest, σ, ρ, σ', h => by
      simp only [execEnd] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
      have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
      rw [← axiomAntwortSonst_fst] at h1
      split at h
      · rename_i σ1 v ha
        rw [ha] at h1
        have g1 := hl.trans (Treu.weiter hw hg h1)
        exact g1.trans ((end_treu rest σ1 _).schrumpf σ' h)
      · rename_i σ1 r ha
        rw [ha] at h1
        have g1 := hl.trans (Treu.weiter hw hg h1)
        exact g1.trans ((end_treu err σ1 _).schrumpf σ' h)
      · simp only [EndAusgang.welt, reduceCtorEq] at h
  | .regRead r _ rest, σ, ρ, σ', h => by
      simp only [execEnd] at h
      refine (treu_fragt σ (.inr (.inl r))).trans ?_
      generalize σ.fragt (.inr (.inl r)) = σ at h ⊢
      split at h
      · split at h
        · exact (end_treu rest σ _).schrumpf σ' h
        · simp only [EndAusgang.welt, reduceCtorEq] at h
      · simp only [EndAusgang.welt, reduceCtorEq] at h
  | .regReadElse r _ zusage sonst rest, σ, ρ, σ', h => by
      simp only [execEnd] at h
      refine (treu_fragt σ (.inr (.inl r))).trans ?_
      generalize σ.fragt (.inr (.inl r)) = σ at h ⊢
      split at h
      · have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ zusage.orte
        split at h
        · exact (TreuEnd.vor hl (end_treu rest _ _)).schrumpf σ' h
        · exact (TreuEnd.vor hl (end_treu sonst _ ρ)) σ' h
      · simp only [EndAusgang.welt, reduceCtorEq] at h
  | .awaits g _ _ hL _ rest, σ, ρ, σ', h => by
      simp only [execEnd] at h
      refine (treu_fragt σ (.inr (.inr g))).trans ?_
      generalize σ.fragt (.inr (.inr g)) = σ at h ⊢
      split at h
      · have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ [.inr g]
        exact (TreuEnd.vor hl (end_treu rest _ _)).schrumpf σ' h
      · simp only [EndAusgang.welt, reduceCtorEq] at h
  | .bindCallInd p args he hp hr rest, σ, ρ, σ', h => by
      simp only [execEnd] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (p.orte ++ args.orte)
      generalize hpv : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = pv at h
      obtain ⟨f, hf⟩ := pv
      simp only at h
      split at h
      · rename_i σ1 v hR1
        have g2 := end_treu rest σ1 (.cons (ergWert (ergSig hf he) v) ρ)
        replace hp := RufPasst.vonPasst (D.passt_sig hf) hp
        have g1 := hl.trans (Treu.weiter hp.hw hp.hg
          (hR f (σ.lese Λ (p.orte ++ args.orte)) _ σ1 (by rw [hR1]; rfl)))
        exact g1.trans (g2.schrumpf σ' h)
      · rename_i σ1 r _; exact keinGrundSig hf hr r
      · simp only [EndAusgang.welt, reduceCtorEq] at h
      · simp only [EndAusgang.welt, reduceCtorEq] at h
  | .narrow e lo' hi' sonst rest, σ, ρ, σ', h => by
      simp only [execEnd] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
      split at h
      · exact (TreuEnd.vor hl (end_treu rest _ _)).schrumpf σ' h
      · exact (TreuEnd.vor hl (end_treu sonst _ ρ)) σ' h
  | .exchange g neu hw hL rest, σ, ρ, σ', h => by
      simp only [execEnd] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (.inr g :: neu.orte)
      have g1 := hl.trans (treu_schreibGlob (W := V.schreibt) (G := V.gschreibt)
        (σ.lese Λ (.inr g :: neu.orte)) g Λ (eval (σ.lese Λ (.inr g :: neu.orte)) neu
          (σ.lese Λ (.inr g :: neu.orte)) (.cons ((σ.lese Λ (.inr g :: neu.orte)).globs g) ρ))
          hw)
      exact (TreuEnd.vor g1 (end_treu rest _ _)).schrumpf σ' h
  | .ite c t e, σ, ρ, σ', h => by
      simp only [execEnd] at h
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ c.orte
      split at h
      · exact (TreuEnd.vor hl (end_treu t _ ρ)) σ' h
      · exact (TreuEnd.vor hl (end_treu e _ ρ)) σ' h

theorem arms_treu :
    ∀ (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)) (σ : World D) (ρ : Env D Γ),
    TreuAusgang V.schreibt V.gschreibt σ (execArms O passes R arms v σ ρ)
  | .cons b _, ⟨⟨0, _⟩, _⟩, σ, _, σ', h => (block_treu b σ _).schrumpfArm _ σ' h
  | .cons _ rest, ⟨⟨_ + 1, _⟩, _⟩, σ, ρ, σ', h => arms_treu rest _ σ ρ σ' h

theorem grund_treu :
    ∀ (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n) (σ : World D) (ρ : Env D Γ),
    TreuAusgang V.schreibt V.gschreibt σ (execGrund O passes R arms r σ ρ)
  | .cons b _, ⟨0, _⟩, σ, ρ, σ', h => block_treu b σ ρ σ' h
  | .cons _ rest, ⟨_ + 1, _⟩, σ, ρ, σ', h => grund_treu rest _ σ ρ σ' h

end

end Rumpf

end Gabbro.Grammatik
