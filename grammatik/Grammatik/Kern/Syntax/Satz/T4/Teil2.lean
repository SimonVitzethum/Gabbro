module
public import Grammatik.Kern.Syntax.Satz.T3
public import Grammatik.Kern.Syntax.Satz.T4.Teil1
@[expose] public section
namespace Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}
section Rumpf
variable (O : Orakel D)
variable (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable (hR : GutR R) (hO : GutO O)
include hR hO
set_option linter.unusedSectionVars false
-- Unfold scope-premise abbreviations before simplifying their Boolean checks.
set_option hygiene false in
local macro "scopes_gut" : tactic => `(tactic| first
  | exact hscope
  | (have hsc := hscope
     dsimp only [Stmt.ScopesOk, Block.ScopesOk, Endblock.ScopesOk, Arms.ScopesOk, GrundArms.ScopesOk] at hsc
     simp only [Stmt.scopesOk, Block.scopesOk, Endblock.scopesOk, Arms.scopesOk, GrundArms.scopesOk, Bool.and_eq_true] at hsc
     first | exact hsc | exact hsc.1 | exact hsc.2 | exact hsc.2.1 | exact hsc.2.2 | exact hsc.1.1 | exact hsc.1.2))
mutual
/-- Statement frame and trace: only writable carriers may change, ordinary
    outcomes keep the held locks, returns release only checked scopes, and
    every new event carries its guards. -/
theorem stmt_gutB (bo : Option Int) (hbV : BodenUnter bo V.boden) :
    ∀ (s : Stmt D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ), s.BodenOk bo → s.ScopesOk →
    ResidHeld V Λ → HeldB bo Λ σ.haelt →
    GutAusgang V.schreibt V.gschreibt σ (execStmt O passes R s σ ρ)
  | .assignSlot t f i e hw hL, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append i.orte_darf e.orte_darf) hh.heldIn
      exact hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldB hh).heldIn)
  | .assignThru p t _ f i e hw hL, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append (orte_append p.orte_darf i.orte_darf) e.orte_darf) hh.heldIn
      exact hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldB hh).heldIn)
  | .assignSlotRef r t _ _ f e hw hL, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append r.orte_darf e.orte_darf) hh.heldIn
      exact hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldB hh).heldIn)
  | .assignGlob g e hw hL, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      exact hl.trans (gut_schreibGlob _ g Λ _ hw hL (hl.heldB hh).heldIn)
  | .putBytes t f hf n i _ _ e hw hL, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append i.orte_darf e.orte_darf) hh.heldIn
      exact hl.trans (gut_schreibBytes _ t f hf Λ hw hL _ _ (hl.heldB hh).heldIn)
  | .assignVar x e, σ, ρ, hbo, hscope, hresid, hh, σ', h => by simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact gut_lese σ Λ _ e.orte_darf hh.heldIn
  | .shift t f hτ i von nach hn he hw hL, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execStmt] at h ⊢; by_cases hc : (hτ ▸ (σ.lese Λ (.inl t :: i.orte)).slots t (eval (σ.lese Λ (.inl t :: i.orte)) i (σ.lese Λ (.inl t :: i.orte)) ρ).n f : Zahl _ _).n = von <;> simp only [hc, ite_true, ite_false, Bool.true_eq_false, Bool.false_eq_true] at h ⊢
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_cons (orte_tab hL) i.orte_darf) hh.heldIn
        exact hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldB hh).heldIn)
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .ite c t e, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execStmt] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ c.orte_darf hh.heldIn; by_cases hc : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true <;> simp only [hc, ite_true, ite_false, Bool.true_eq_false, Bool.false_eq_true] at h ⊢
      · exact (GutAusgang.vor hl (block_gutB bo hbV t _ ρ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))) σ' h
      · exact (GutAusgang.vor hl (block_gutB bo hbV e _ ρ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))) σ' h
  | .onOption o p a, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execStmt] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ o.orte_darf hh.heldIn; generalize hv : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = ov at h ⊢; cases ov with
      | some v => exact (GutAusgang.vor hl (block_gutB bo hbV p _ _ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))).schrumpf σ' h
      | none => exact (GutAusgang.vor hl (block_gutB bo hbV a _ ρ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))) σ' h
  | .onTag v arms, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ v.orte_darf hh.heldIn
      exact (GutAusgang.vor hl (arms_gutB bo hbV arms _ _ ρ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))) σ' h
  | .onWhy r arms, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ r.orte_darf hh.heldIn
      exact (GutAusgang.vor hl (grund_gutB bo hbV arms _ _ ρ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))) σ' h
  | .call f args hp hr, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execStmt] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn; generalize hR1 : R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = rv at h ⊢; cases rv
      · rename_i σ1 v; simp only [Ausgang.welt, Option.some.injEq] at h; subst h; exact hl.trans (Gut.weiter hp.hw hp.hg (by have h2 := hR f (σ.lese Λ args.orte) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl); rw [hR1] at h2; exact h2))
      · rename_i σ1 r; exact keinGrund hr r
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .callInd p args hp hr, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execStmt] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append p.orte_darf args.orte_darf) hh.heldIn
      generalize hpv : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = pv at h ⊢
      obtain ⟨f, hf⟩ := pv
      simp only at h ⊢; generalize hR1 : R f (σ.lese Λ (p.orte ++ args.orte)) (umsig hf (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args (σ.lese Λ (p.orte ++ args.orte)) ρ)) = rv at h ⊢; cases rv
      · rename_i σ1 v; simp only [Ausgang.welt, Option.some.injEq] at h; subst h; replace hp := RufPasst.vonPasst (D.passt_sig hf) hp
        exact hl.trans (Gut.weiter hp.hw hp.hg (by have h2 := hR f (σ.lese Λ (p.orte ++ args.orte)) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl); rw [hR1] at h2; exact h2))
      · rename_i σ1 r; exact keinGrundSig hf hr r
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .callIndElse p args he hp hr err, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execStmt] at h ⊢; exact indSonst_gutB R hR bo hbV p args he hp hr σ _ ρ hh hresid (gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append p.orte_darf args.orte_darf) hh.heldIn)
        _ _ (fun s1 _ _ s2 h2 => by simp only [Ausgang.welt, Option.some.injEq] at h2; subst h2; exact Gut.refl _ _ _) (fun s1 r hh1 => (end_gutB bo hbV err s1 _ (by boden_tac) (by scopes_gut) (ResidHeld.of_iff (fun L => held_nachSig_iff _ _ L) hresid) hh1).schrumpf.zuAusgang) σ' h
  | .locks L hr body, σ, ρ, hbo, hscope, hresid, hh, σ', h =>
      (GutAusgang.gibt L (nicht_gehaltenB L hr hh (fun c hc => by
          have hsc := hbo c hc; simp only [Stmt.ueberBoden, Bool.and_eq_true, decide_eq_true_eq] at hsc; exact hsc.1))
        (block_gutB bo hbV body (σ.nimmt L) ρ (by boden_tac) (by scopes_gut)
          (fun M hV => List.mem_cons_of_mem _ (hresid M hV)) (heldB_locks L hh))) σ' h
  | .breaking _ body, σ, ρ, hbo, hscope, hresid, hh, σ', h => block_gutB bo hbV body σ ρ (by boden_tac) (by scopes_gut) hresid hh σ' h
  | .traverse t inv body, σ, ρ, hbo, hscope, hresid, hh, σ', h =>
      traverseLauf_gut (Λ := Λ) _ _ (fun σ ρ hh => block_gutB bo hbV body σ ρ (by boden_tac) (by scopes_gut) hresid hh) (fun σ ρ hh => gut_lese σ Λ _ inv.orte_darf hh.heldIn) _ σ ρ hh σ' h
  | .consumeTraverse t _ _ inv _ _ body, σ, ρ, hbo, hscope, hresid, hh, σ', h =>
      traverseLauf_gut (Λ := Λ) _ _ (fun σ ρ hh => block_gutB bo hbV body σ ρ (by boden_tac) (by scopes_gut) hresid hh) (fun σ ρ hh => gut_lese σ Λ _ inv.orte_darf hh.heldIn) _ σ ρ hh σ' h
  | .retry n bis body ueberlauf, σ, ρ, hbo, hscope, hresid, hh, σ', h =>
      retryLauf_gut (Λ := Λ) _ _ _ (fun σ ρ hh => block_gutB bo hbV body σ ρ (by boden_tac) (by scopes_gut) hresid hh) (fun σ ρ hh => gut_lese σ Λ _ bis.orte_darf hh.heldIn) (fun σ ρ hh => block_gutB bo hbV ueberlauf σ ρ (by boden_tac) (by scopes_gut) hresid hh) n σ ρ hh σ' h
  | .forever a inv body, σ, ρ, hbo, hscope, hresid, hh, σ', h =>
      foreverLauf_gut (Λ := Λ) a _ _ (fun σ ρ hh => block_gutB bo hbV body σ ρ (by boden_tac) (by scopes_gut) hresid hh) (fun σ ρ hh => gut_lese σ Λ _ inv.orte_darf hh.heldIn) passes σ ρ hh σ' h
  | .axiomCall a args _ hw hg hd hgd, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execStmt] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn; generalize ha : axiomAntwort O a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = av at h ⊢; rcases av with ⟨σ1, _ | v⟩
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h; have := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldB hh).heldIn
        rw [ha] at this
        exact hl.trans (Gut.weiter hw hg this)
  | .axiomCallElse _ a args _ hp hd hgd _ err, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execStmt] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      have h1 := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldB hh).heldIn
      rw [← axiomAntwortSonst_fst] at h1; generalize ha : axiomAntwortSonst O a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = av at h ⊢; rcases av with ⟨σ1, _ | (v | r)⟩
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        rw [ha] at h1
        exact hl.trans (Gut.weiter hp.hw hp.hg h1)
      · rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg h1)
        exact (GutAusgang.vor g1 ((end_gutB bo hbV err σ1 _ (by boden_tac) (by scopes_gut) (ResidHeld.of_iff (fun L => held_nachSig_iff _ _ L) hresid)
          (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf.zuAusgang)) σ' h
  | .regWrite r _ e, σ, ρ, hbo, hscope, hresid, hh, σ', h => by simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact gut_lese σ Λ _ e.orte_darf hh.heldIn
  | .transition .., σ, ρ, hbo, hscope, hresid, hh, σ', h => by simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact gut_fragt _ _
  | .publish g e _ _ hw hL, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      exact hl.trans (gut_schreibGlob _ g Λ _ hw hL (hl.heldB hh).heldIn)
  | .advances .., σ, ρ, hbo, hscope, hresid, hh, σ', h => by simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .retires .., σ, ρ, hbo, hscope, hresid, hh, σ', h => by simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .ret e _, σ, ρ, hbo, hscope, hresid, hh, σ', h => by simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact (gut_lese σ Λ _ e.orte_darf hh.heldIn).toRetV
  | .retScoped e R, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      have hsc : scopesOkScopes V.haelt V.boden R.scopes = true := by scopes_gut
      exact gutRetV_retScoped R.scopes (gut_lese σ Λ _ e.orte_darf hh.heldIn)
        (fun L hL => (scopesOkScopes_mem hsc hL).1)
        (fun L hL c hc => (scopesOkScopes_mem hsc hL).2 c hc)
  | .retWhyScoped _ R, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      have hsc : scopesOkScopes V.haelt V.boden R.scopes = true := by scopes_gut
      exact gutRetV_retWhyScoped σ R.scopes
        (fun L hL => (scopesOkScopes_mem hsc hL).1)
        (fun L hL c hc => (scopesOkScopes_mem hsc hL).2 c hc)
  | .retWhy .., σ, ρ, hbo, hscope, hresid, hh, σ', h => by simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact (Gut.refl _ _ _).toRetV
  | .leave _, σ, ρ, hbo, hscope, hresid, hh, σ', h => by simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .next _, σ, ρ, hbo, hscope, hresid, hh, σ', h => by simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
theorem block_gutB (bo : Option Int) (hbV : BodenUnter bo V.boden) :
    ∀ (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ), b.BodenOk bo → b.ScopesOk →
    ResidHeld V Λ → HeldB bo Λ σ.haelt →
    GutAusgang V.schreibt V.gschreibt σ (execBlock O passes R b σ ρ)
  | .nil, σ, ρ, hbo, hscope, hresid, hh, σ', h => by simp only [execBlock, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .cons s rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execBlock] at h ⊢; generalize hs : execStmt O passes R s σ ρ = sv at h ⊢; cases sv
      · rename_i σ1 ρ1
        have g1 := stmt_gutB bo hbV s σ ρ (by boden_tac) (by scopes_gut) hresid hh σ1 (by rw [hs]; rfl); rw [hs] at g1
        exact (GutAusgang.vor g1 (block_gutB bo hbV rest σ1 ρ1 (by boden_tac) (by scopes_gut) (ResidHeld.of_iff s.held_iff hresid) (heldB_weiter s.held_iff g1 hh))) σ' h
      all_goals simpa only [hs] using stmt_gutB bo hbV s σ ρ (by boden_tac) (by scopes_gut) hresid hh σ' (by simpa only [hs] using h)
  | .bind e rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      exact (GutAusgang.vor hl (block_gutB bo hbV rest _ _ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))).schrumpf σ' h
  | .bindCall f args he hp hr rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execBlock] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn; generalize hR1 : R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = rv at h ⊢; cases rv
      · rename_i σ1 v
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg (by have h2 := hR f (σ.lese Λ args.orte) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl); rw [hR1] at h2; exact h2))
        exact (GutAusgang.vor g1 ((block_gutB bo hbV rest σ1 _ (by boden_tac) (by scopes_gut) (ResidHeld.of_iff (fun L => held_nachSig_iff _ _ L) hresid)
          (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf)) σ' h
      · rename_i σ1 r; exact keinGrund hr r
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .bindCallInd p args he hp hr rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execBlock] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append p.orte_darf args.orte_darf) hh.heldIn
      generalize hpv : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = pv at h ⊢
      obtain ⟨f, hf⟩ := pv
      simp only at h ⊢; generalize hR1 : R f (σ.lese Λ (p.orte ++ args.orte)) (umsig hf (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args (σ.lese Λ (p.orte ++ args.orte)) ρ)) = rv at h ⊢; cases rv
      · rename_i σ1 v
        have g2 := block_gutB bo hbV rest σ1 (.cons (ergWert (ergSig hf he) v) ρ) (by boden_tac)
          (by scopes_gut) (ResidHeld.of_iff (fun L => held_nachSig_iff _ _ L) hresid)
        replace hp := RufPasst.vonPasst (D.passt_sig hf) hp
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg (by have h2 := hR f (σ.lese Λ (p.orte ++ args.orte)) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl); rw [hR1] at h2; exact h2))
        exact (GutAusgang.vor g1 ((g2 (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf)) σ' h
      · rename_i σ1 r; exact keinGrundSig hf hr r
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .bindCallIndElse p args he hp hr err rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execBlock] at h ⊢
      refine indSonst_gutB R hR bo hbV p args he hp hr σ _ ρ hh hresid (gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append p.orte_darf args.orte_darf) hh.heldIn)
        _ _ ?_ ?_ σ' h
      · exact fun s1 v hh1 => (block_gutB bo hbV rest s1 _ (by boden_tac) (by scopes_gut)
          (ResidHeld.of_iff (fun L => held_nachSig_iff _ _ L) hresid) hh1).schrumpf
      · exact fun s1 r hh1 => (end_gutB bo hbV err s1 _ (by boden_tac) (by scopes_gut) (ResidHeld.of_iff (fun L => held_nachSig_iff _ _ L) hresid) hh1).schrumpf.zuAusgang
  | .bindCallElse f args he hp _ err rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execBlock] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn; generalize hR1 : R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = rv at h ⊢; cases rv
      · rename_i σ1 v
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg (by have h2 := hR f (σ.lese Λ args.orte) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl); rw [hR1] at h2; exact h2))
        exact (GutAusgang.vor g1 ((block_gutB bo hbV rest σ1 _ (by boden_tac) (by scopes_gut) (ResidHeld.of_iff (fun L => held_nachSig_iff _ _ L) hresid)
          (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf)) σ' h
      · rename_i σ1 r
        have h2 := hR f (σ.lese Λ args.orte) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl)
        rw [hR1] at h2
        have g1 := hl.trans ((h2.toGut_entry (heldB_ruf hp hbV (hl.heldB hh))).weiter hp.hw hp.hg)
        exact (GutAusgang.vor g1 ((end_gutB bo hbV err σ1 _ (by boden_tac) (by scopes_gut)
          (ResidHeld.of_iff (fun L => held_nachSig_iff _ _ L) hresid)
          (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf.zuAusgang)) σ' h
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .bindAxiom a args he hw hg hd hgd rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execBlock] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn; generalize ha : axiomAntwort O a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = av at h ⊢; rcases av with ⟨σ1, _ | v⟩
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · have h1 := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldB hh).heldIn
        rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hw hg h1)
        exact (GutAusgang.vor g1 ((block_gutB bo hbV rest σ1 _ (by boden_tac) (by scopes_gut) hresid (g1.heldB hh)).schrumpf)) σ' h
  | .bindAxiomElse a args he hr hw hg hd hgd err rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execBlock] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      have h1 := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldB hh).heldIn
      rw [← axiomAntwortSonst_fst] at h1; generalize ha : axiomAntwortSonst O a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = av at h ⊢; rcases av with ⟨σ1, _ | (v | r)⟩
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hw hg h1)
        exact (GutAusgang.vor g1 ((block_gutB bo hbV rest σ1 _ (by boden_tac) (by scopes_gut) hresid (g1.heldB hh)).schrumpf)) σ' h
      · rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hw hg h1)
        exact (GutAusgang.vor g1 ((end_gutB bo hbV err σ1 _ (by boden_tac) (by scopes_gut) hresid (g1.heldB hh)).schrumpf.zuAusgang)) σ' h
  | .bindAxiomOpt e a args he hp hd hgd rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execBlock] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn; generalize ha : axiomAntwort O a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = av at h ⊢; rcases av with ⟨σ1, _ | v⟩
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · have h1 := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldB hh).heldIn
        rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg h1)
        have ihr := fun ρ' => block_gutB bo hbV rest σ1 ρ' (by boden_tac) (by scopes_gut) (ResidHeld.of_iff (fun L => held_nachSig_iff _ _ L) hresid)
          (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)
        cases e with
        | none =>
            simp only [Ausgang.weiterOpt] at h; exact (GutAusgang.vor g1 (ihr _)) σ' h
        | some τ =>
            simp only [Ausgang.weiterOpt] at h; exact (GutAusgang.vor g1 ((ihr _).schrumpf)) σ' h
  | .bindAxiomOptElse e a args he hp hd hgd hr err rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execBlock] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      have h1 := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldB hh).heldIn
      rw [← axiomAntwortSonst_fst] at h1; generalize ha : axiomAntwortSonst O a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = av at h ⊢; rcases av with ⟨σ1, _ | (v | r)⟩
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg h1)
        have ihr := fun ρ' => block_gutB bo hbV rest σ1 ρ' (by boden_tac) (by scopes_gut) (ResidHeld.of_iff (fun L => held_nachSig_iff _ _ L) hresid)
          (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)
        cases e with
        | none =>
            simp only [Ausgang.weiterOpt] at h; exact (GutAusgang.vor g1 (ihr _)) σ' h
        | some τ =>
            simp only [Ausgang.weiterOpt] at h; exact (GutAusgang.vor g1 ((ihr _).schrumpf)) σ' h
      · rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg h1)
        exact (GutAusgang.vor g1 ((end_gutB bo hbV err σ1 _ (by boden_tac) (by scopes_gut) (ResidHeld.of_iff (fun L => held_nachSig_iff _ _ L) hresid)
          (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf.zuAusgang)) σ' h
  | .regRead r _ rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execBlock] at h ⊢
      refine (GutAusgang.vor (gut_fragt σ (.inr (.inl r))) ?_) σ' h; intro σ' h
      rw [← fragt_haelt σ (.inr (.inl r))] at hh
      generalize σ.fragt (.inr (.inl r)) = σ at h hh ⊢; generalize hv : einpassen O.zeiger (D.rtyp r) (O.regLies r σ) = ov at h ⊢; cases ov with
      | some v =>
          by_cases hc : D.rzusage r v = true <;> simp only [hc, ite_true, ite_false, Bool.true_eq_false, Bool.false_eq_true] at h ⊢
          · exact (block_gutB bo hbV rest σ _ (by boden_tac) (by scopes_gut) hresid hh).schrumpf σ' h
          · simp only [Ausgang.welt, reduceCtorEq] at h
      | none => simp only [Ausgang.welt, reduceCtorEq] at h
  | .regReadElse r _ zusage sonst rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execBlock] at h ⊢
      refine (GutAusgang.vor (gut_fragt σ (.inr (.inl r))) ?_) σ' h; intro σ' h
      rw [← fragt_haelt σ (.inr (.inl r))] at hh
      generalize σ.fragt (.inr (.inl r)) = σ at h hh ⊢; generalize hv : einpassen O.zeiger (D.rtyp r) (O.regLies r σ) = ov at h ⊢; cases ov with
      | some v => have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ zusage.orte_darf hh.heldIn
        by_cases hc : wahr? (eval (σ.lese Λ zusage.orte) zusage (σ.lese Λ zusage.orte) (.cons v ρ)) = true <;> simp only [hc, ite_true, ite_false, Bool.true_eq_false, Bool.false_eq_true] at h ⊢
        · exact (GutAusgang.vor hl (block_gutB bo hbV rest _ _ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))).schrumpf σ' h
        · exact (GutEnd.vor hl (end_gutB bo hbV sonst _ ρ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))).zuAusgang σ' h
      | none => simp only [Ausgang.welt, reduceCtorEq] at h
  | .awaits g _ _ hL _ rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execBlock] at h ⊢
      refine (GutAusgang.vor (gut_fragt σ (.inr (.inr g))) ?_) σ' h; intro σ' h
      rw [← fragt_haelt σ (.inr (.inr g))] at hh
      generalize σ.fragt (.inr (.inr g)) = σ at h hh ⊢; by_cases hc : O.sichtbar g σ = true <;> simp only [hc, ite_true, ite_false, Bool.true_eq_false, Bool.false_eq_true] at h ⊢
      · have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ [.inr g] (orte_cons (orte_glob hL) (by intro o ho; simp only [List.not_mem_nil] at ho)) hh.heldIn
        exact (GutAusgang.vor hl (block_gutB bo hbV rest _ _ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))).schrumpf σ' h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .exchange g neu hw hL rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execBlock] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_cons (orte_glob hL) neu.orte_darf) hh.heldIn
      have g1 := hl.trans (gut_schreibGlob (W := V.schreibt) (G := V.gschreibt) (σ.lese Λ (.inr g :: neu.orte)) g Λ (eval (σ.lese Λ (.inr g :: neu.orte)) neu (σ.lese Λ (.inr g :: neu.orte)) (.cons ((σ.lese Λ (.inr g :: neu.orte)).globs g) ρ))
          hw hL (hl.heldB hh).heldIn)
      exact (GutAusgang.vor g1 (block_gutB bo hbV rest _ _ (by boden_tac) (by scopes_gut) hresid (g1.heldB hh))).schrumpf σ' h
  | .narrow e lo' hi' sonst rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execBlock] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn; by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi' <;> simp only [hc, dif_pos, dif_neg] at h ⊢
      · exact (GutAusgang.vor hl (block_gutB bo hbV rest _ _ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))).schrumpf σ' h
      · exact (GutEnd.vor hl (end_gutB bo hbV sonst _ ρ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))).zuAusgang σ' h
  | .narrowRequired e lo' hi' rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execBlock] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn; by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi' <;> simp only [hc, dif_pos, dif_neg] at h ⊢
      · exact (GutAusgang.vor hl (block_gutB bo hbV rest _ _ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))).schrumpf σ' h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .check c sonst rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execBlock] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ c.orte_darf hh.heldIn; by_cases hc : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true <;> simp only [hc, ite_true, ite_false, Bool.true_eq_false, Bool.false_eq_true] at h ⊢
      · exact (GutAusgang.vor hl (block_gutB bo hbV rest _ ρ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))) σ' h
      · exact (GutEnd.vor hl (end_gutB bo hbV sonst _ ρ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))).zuAusgang σ' h
  | .float op a b lo hi rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execBlock] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append a.orte_darf b.orte_darf) hh.heldIn; generalize hv : gleitPasst lo hi (gleitRechne op (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) = ov at h ⊢; cases ov with
      | some v => exact (GutAusgang.vor hl (block_gutB bo hbV rest _ _ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))).schrumpf σ' h
      | none => simp only [Ausgang.welt, reduceCtorEq] at h
  | .floatLit q lo hi rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execBlock] at h ⊢; generalize hv : gleitPasst lo hi (bruch q) = ov at h ⊢; cases ov with
      | some v => exact (block_gutB bo hbV rest σ _ (by boden_tac) (by scopes_gut) hresid hh).schrumpf σ' h
      | none => simp only [Ausgang.welt, reduceCtorEq] at h
  | .floatOf e lo hi rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execBlock] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn; generalize hv : gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n) = ov at h ⊢; cases ov with
      | some v => exact (GutAusgang.vor hl (block_gutB bo hbV rest _ _ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))).schrumpf σ' h
      | none => simp only [Ausgang.welt, reduceCtorEq] at h
  | .floatNarrow e lo hi sonst rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execBlock] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn; generalize hv : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = ov at h ⊢; cases ov with
      | some v => exact (GutAusgang.vor hl (block_gutB bo hbV rest _ _ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))).schrumpf σ' h
      | none => exact (GutEnd.vor hl (end_gutB bo hbV sonst _ ρ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))).zuAusgang σ' h
theorem end_gutB (bo : Option Int) (hbV : BodenUnter bo V.boden) :
    ∀ (b : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ), b.BodenOk bo → b.ScopesOk →
    ResidHeld V Λ → HeldB bo Λ σ.haelt →
    GutEnd V.schreibt V.gschreibt σ (execEnd O passes R b σ ρ)
  | .ret e _, σ, ρ, hbo, hscope, hresid, hh, σ', h => by simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h; exact (gut_lese σ Λ _ e.orte_darf hh.heldIn).toRetV
  | .retScoped e R, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h
      have hsc : scopesOkScopes V.haelt V.boden R.scopes = true := by scopes_gut
      exact gutRetV_retScoped R.scopes (gut_lese σ Λ _ e.orte_darf hh.heldIn)
        (fun L hL => (scopesOkScopes_mem hsc hL).1)
        (fun L hL c hc => (scopesOkScopes_mem hsc hL).2 c hc)
  | .retWhyScoped _ R, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h
      have hsc : scopesOkScopes V.haelt V.boden R.scopes = true := by scopes_gut
      exact gutRetV_retWhyScoped σ R.scopes
        (fun L hL => (scopesOkScopes_mem hsc hL).1)
        (fun L hL c hc => (scopesOkScopes_mem hsc hL).2 c hc)
  | .retWhy .., σ, ρ, hbo, hscope, hresid, hh, σ', h => by simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h; exact (Gut.refl _ _ _).toRetV
  | .leave _, σ, ρ, hbo, hscope, hresid, hh, σ', h => by simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .next _, σ, ρ, hbo, hscope, hresid, hh, σ', h => by simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .cons s rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execEnd] at h ⊢; have hs := stmt_gutB bo hbV s σ ρ (by boden_tac) (by scopes_gut) hresid hh; generalize hs1 : execStmt O passes R s σ ρ = sv at h ⊢; cases sv
      · rename_i σ1 ρ1
        have g1 := hs σ1 (by rw [hs1]; rfl); rw [hs1] at g1
        exact (GutEnd.vor g1 (end_gutB bo hbV rest σ1 ρ1 (by boden_tac) (by scopes_gut) (ResidHeld.of_iff s.held_iff hresid) (heldB_weiter s.held_iff g1 hh))) σ' h
      all_goals first
        | (simp only [EndAusgang.welt, Option.some.injEq] at h; subst h
           simpa only [hs1] using hs _ (by rw [hs1]; rfl))
        | (simp only [EndAusgang.welt, reduceCtorEq] at h)
  | .bind e rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      exact (GutEnd.vor hl (end_gutB bo hbV rest _ _ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))).schrumpf σ' h
  | .bindCall f args he hp hr rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execEnd] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn; generalize hR1 : R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = rv at h ⊢; cases rv
      · rename_i σ1 v
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg (by have h2 := hR f (σ.lese Λ args.orte) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl); rw [hR1] at h2; exact h2))
        exact (GutEnd.vor g1 ((end_gutB bo hbV rest σ1 _ (by boden_tac) (by scopes_gut) (ResidHeld.of_iff (fun L => held_nachSig_iff _ _ L) hresid)
          (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf)) σ' h
      · rename_i σ1 r; exact keinGrund hr r
      · simp only [EndAusgang.welt, reduceCtorEq] at h
      · simp only [EndAusgang.welt, reduceCtorEq] at h
  | .bindCallElse f args he hp _ err rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execEnd] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn; generalize hR1 : R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = rv at h ⊢; cases rv
      · rename_i σ1 v
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg (by have h2 := hR f (σ.lese Λ args.orte) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl); rw [hR1] at h2; exact h2))
        exact (GutEnd.vor g1 ((end_gutB bo hbV rest σ1 _ (by boden_tac) (by scopes_gut) (ResidHeld.of_iff (fun L => held_nachSig_iff _ _ L) hresid)
          (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf)) σ' h
      · rename_i σ1 r
        have h2 := hR f (σ.lese Λ args.orte) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl)
        rw [hR1] at h2
        have g1 := hl.trans ((h2.toGut_entry (heldB_ruf hp hbV (hl.heldB hh))).weiter hp.hw hp.hg)
        exact (GutEnd.vor g1 ((end_gutB bo hbV err σ1 _ (by boden_tac) (by scopes_gut)
          (ResidHeld.of_iff (fun L => held_nachSig_iff _ _ L) hresid)
          (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf)) σ' h
      · simp only [EndAusgang.welt, reduceCtorEq] at h
      · simp only [EndAusgang.welt, reduceCtorEq] at h
  | .bindAxiom a args he hw hg hd hgd rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execEnd] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn; generalize ha : axiomAntwort O a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = av at h ⊢; rcases av with ⟨σ1, _ | v⟩
      · simp only [EndAusgang.welt, reduceCtorEq] at h
      · have h1 := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldB hh).heldIn
        rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hw hg h1)
        exact (GutEnd.vor g1 ((end_gutB bo hbV rest σ1 _ (by boden_tac) (by scopes_gut) hresid (g1.heldB hh)).schrumpf)) σ' h
  | .bindAxiomElse a args he hr hw hg hd hgd err rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execEnd] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      have h1 := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldB hh).heldIn
      rw [← axiomAntwortSonst_fst] at h1; generalize ha : axiomAntwortSonst O a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = av at h ⊢; rcases av with ⟨σ1, _ | (v | r)⟩
      · simp only [EndAusgang.welt, reduceCtorEq] at h
      · rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hw hg h1)
        exact (GutEnd.vor g1 ((end_gutB bo hbV rest σ1 _ (by boden_tac) (by scopes_gut) hresid (g1.heldB hh)).schrumpf)) σ' h
      · rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hw hg h1)
        exact (GutEnd.vor g1 ((end_gutB bo hbV err σ1 _ (by boden_tac) (by scopes_gut) hresid (g1.heldB hh)).schrumpf)) σ' h
  | .bindAxiomOpt e a args he hp hd hgd rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execEnd] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn; generalize ha : axiomAntwort O a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = av at h ⊢; rcases av with ⟨σ1, _ | v⟩
      · simp only [EndAusgang.welt, reduceCtorEq] at h
      · have h1 := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldB hh).heldIn
        rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg h1)
        have ihr := fun ρ' => end_gutB bo hbV rest σ1 ρ' (by boden_tac) (by scopes_gut) (ResidHeld.of_iff (fun L => held_nachSig_iff _ _ L) hresid)
          (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)
        cases e with
        | none =>
            simp only [EndAusgang.weiterOpt] at h; exact (GutEnd.vor g1 (ihr _)) σ' h
        | some τ =>
            simp only [EndAusgang.weiterOpt] at h; exact (GutEnd.vor g1 ((ihr _).schrumpf)) σ' h
  | .bindAxiomOptElse e a args he hp hd hgd hr err rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execEnd] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      have h1 := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldB hh).heldIn
      rw [← axiomAntwortSonst_fst] at h1; generalize ha : axiomAntwortSonst O a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = av at h ⊢; rcases av with ⟨σ1, _ | (v | r)⟩
      · simp only [EndAusgang.welt, reduceCtorEq] at h
      · rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg h1)
        have ihr := fun ρ' => end_gutB bo hbV rest σ1 ρ' (by boden_tac) (by scopes_gut) (ResidHeld.of_iff (fun L => held_nachSig_iff _ _ L) hresid)
          (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)
        cases e with
        | none =>
            simp only [EndAusgang.weiterOpt] at h; exact (GutEnd.vor g1 (ihr _)) σ' h
        | some τ =>
            simp only [EndAusgang.weiterOpt] at h; exact (GutEnd.vor g1 ((ihr _).schrumpf)) σ' h
      · rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg h1)
        exact (GutEnd.vor g1 ((end_gutB bo hbV err σ1 _ (by boden_tac) (by scopes_gut) (ResidHeld.of_iff (fun L => held_nachSig_iff _ _ L) hresid)
          (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf)) σ' h
  | .regRead r _ rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execEnd] at h ⊢
      refine (GutEnd.vor (gut_fragt σ (.inr (.inl r))) ?_) σ' h; intro σ' h
      rw [← fragt_haelt σ (.inr (.inl r))] at hh
      generalize σ.fragt (.inr (.inl r)) = σ at h hh ⊢; generalize hv : einpassen O.zeiger (D.rtyp r) (O.regLies r σ) = ov at h ⊢; cases ov with
      | some v =>
          by_cases hc : D.rzusage r v = true <;> simp only [hc, ite_true, ite_false, Bool.true_eq_false, Bool.false_eq_true] at h ⊢
          · exact (end_gutB bo hbV rest σ _ (by boden_tac) (by scopes_gut) hresid hh).schrumpf σ' h
          · simp only [EndAusgang.welt, reduceCtorEq] at h
      | none => simp only [EndAusgang.welt, reduceCtorEq] at h
  | .regReadElse r _ zusage sonst rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execEnd] at h ⊢
      refine (GutEnd.vor (gut_fragt σ (.inr (.inl r))) ?_) σ' h; intro σ' h
      rw [← fragt_haelt σ (.inr (.inl r))] at hh
      generalize σ.fragt (.inr (.inl r)) = σ at h hh ⊢; generalize hv : einpassen O.zeiger (D.rtyp r) (O.regLies r σ) = ov at h ⊢; cases ov with
      | some v => have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ zusage.orte_darf hh.heldIn
        by_cases hc : wahr? (eval (σ.lese Λ zusage.orte) zusage (σ.lese Λ zusage.orte) (.cons v ρ)) = true <;> simp only [hc, ite_true, ite_false, Bool.true_eq_false, Bool.false_eq_true] at h ⊢
        · exact (GutEnd.vor hl (end_gutB bo hbV rest _ _ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))).schrumpf σ' h
        · exact (GutEnd.vor hl (end_gutB bo hbV sonst _ ρ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))) σ' h
      | none => simp only [EndAusgang.welt, reduceCtorEq] at h
  | .awaits g _ _ hL _ rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execEnd] at h ⊢
      refine (GutEnd.vor (gut_fragt σ (.inr (.inr g))) ?_) σ' h; intro σ' h
      rw [← fragt_haelt σ (.inr (.inr g))] at hh
      generalize σ.fragt (.inr (.inr g)) = σ at h hh ⊢; by_cases hc : O.sichtbar g σ = true <;> simp only [hc, ite_true, ite_false, Bool.true_eq_false, Bool.false_eq_true] at h ⊢
      · have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ [.inr g] (orte_cons (orte_glob hL) (by intro o ho; simp only [List.not_mem_nil] at ho)) hh.heldIn
        exact (GutEnd.vor hl (end_gutB bo hbV rest _ _ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))).schrumpf σ' h
      · simp only [EndAusgang.welt, reduceCtorEq] at h
  | .bindCallInd p args he hp hr rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execEnd] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append p.orte_darf args.orte_darf) hh.heldIn
      generalize hpv : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = pv at h ⊢
      obtain ⟨f, hf⟩ := pv
      simp only at h ⊢; generalize hR1 : R f (σ.lese Λ (p.orte ++ args.orte)) (umsig hf (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args (σ.lese Λ (p.orte ++ args.orte)) ρ)) = rv at h ⊢; cases rv
      · rename_i σ1 v
        have g2 := end_gutB bo hbV rest σ1 (.cons (ergWert (ergSig hf he) v) ρ) (by boden_tac)
          (by scopes_gut) (ResidHeld.of_iff (fun L => held_nachSig_iff _ _ L) hresid)
        replace hp := RufPasst.vonPasst (D.passt_sig hf) hp
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg (by have h2 := hR f (σ.lese Λ (p.orte ++ args.orte)) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl); rw [hR1] at h2; exact h2))
        exact (GutEnd.vor g1 ((g2 (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf)) σ' h
      · rename_i σ1 r; exact keinGrundSig hf hr r
      · simp only [EndAusgang.welt, reduceCtorEq] at h
      · simp only [EndAusgang.welt, reduceCtorEq] at h
  | .bindCallIndElse p args he hp hr err rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execEnd] at h ⊢; exact indSonstE_gutB R hR bo hbV p args he hp hr σ _ ρ hh hresid (gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append p.orte_darf args.orte_darf) hh.heldIn)
        (fun s1 v => (execEnd O passes R rest s1 (.cons v ρ)).schrumpf)
        (fun s1 r => (execEnd O passes R err s1 (.cons r ρ)).schrumpf)
        (fun s1 v hh1 => (end_gutB bo hbV rest s1 _ (by boden_tac) (by scopes_gut)
          (ResidHeld.of_iff (fun L => held_nachSig_iff _ _ L) hresid) hh1).schrumpf)
        (fun s1 r hh1 => (end_gutB bo hbV err s1 _ (by boden_tac) (by scopes_gut) (ResidHeld.of_iff (fun L => held_nachSig_iff _ _ L) hresid) hh1).schrumpf) σ' h
  | .narrow e lo' hi' sonst rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execEnd] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn; by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi' <;> simp only [hc, dif_pos, dif_neg] at h ⊢
      · exact (GutEnd.vor hl (end_gutB bo hbV rest _ _ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))).schrumpf σ' h
      · exact (GutEnd.vor hl (end_gutB bo hbV sonst _ ρ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))) σ' h
  | .narrowRequired e lo' hi' rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execEnd] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn; by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi' <;> simp only [hc, dif_pos, dif_neg] at h ⊢
      · exact (GutEnd.vor hl (end_gutB bo hbV rest _ _ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))).schrumpf σ' h
      · simp only [EndAusgang.welt, reduceCtorEq] at h
  | .exchange g neu hw hL rest, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execEnd] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_cons (orte_glob hL) neu.orte_darf) hh.heldIn
      have g1 := hl.trans (gut_schreibGlob (W := V.schreibt) (G := V.gschreibt) (σ.lese Λ (.inr g :: neu.orte)) g Λ (eval (σ.lese Λ (.inr g :: neu.orte)) neu (σ.lese Λ (.inr g :: neu.orte)) (.cons ((σ.lese Λ (.inr g :: neu.orte)).globs g) ρ))
          hw hL (hl.heldB hh).heldIn)
      exact (GutEnd.vor g1 (end_gutB bo hbV rest _ _ (by boden_tac) (by scopes_gut) hresid (g1.heldB hh))).schrumpf σ' h
  | .ite c t e, σ, ρ, hbo, hscope, hresid, hh, σ', h => by
      simp only [execEnd] at h ⊢; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ c.orte_darf hh.heldIn; by_cases hc : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true <;> simp only [hc, ite_true, ite_false, Bool.true_eq_false, Bool.false_eq_true] at h ⊢
      · exact (GutEnd.vor hl (end_gutB bo hbV t _ ρ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))) σ' h
      · exact (GutEnd.vor hl (end_gutB bo hbV e _ ρ (by boden_tac) (by scopes_gut) hresid (hl.heldB hh))) σ' h
theorem arms_gutB (bo : Option Int) (hbV : BodenUnter bo V.boden) :
    ∀ (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)) (σ : World D) (ρ : Env D Γ),
    arms.BodenOk bo → arms.ScopesOk →
    ResidHeld V Λ → HeldB bo Λ σ.haelt → GutAusgang V.schreibt V.gschreibt σ (execArms O passes R arms v σ ρ)
  | .cons b _, ⟨⟨0, _⟩, _⟩, σ, _, hbo, hscope, hresid, hh, σ', h => (block_gutB bo hbV b σ _ (by boden_tac) (by scopes_gut) hresid hh).schrumpfArm _ σ' h
  | .cons _ rest, ⟨⟨_ + 1, _⟩, _⟩, σ, ρ, hbo, hscope, hresid, hh, σ', h => arms_gutB bo hbV rest _ σ ρ (by boden_tac) (by scopes_gut) hresid hh σ' h
theorem grund_gutB (bo : Option Int) (hbV : BodenUnter bo V.boden) :
    ∀ (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n) (σ : World D) (ρ : Env D Γ),
    arms.BodenOk bo → arms.ScopesOk →
    ResidHeld V Λ → HeldB bo Λ σ.haelt → GutAusgang V.schreibt V.gschreibt σ (execGrund O passes R arms r σ ρ)
  | .cons b _, ⟨0, _⟩, σ, ρ, hbo, hscope, hresid, hh, σ', h => block_gutB bo hbV b σ ρ (by boden_tac) (by scopes_gut) hresid hh σ' h
  | .cons _ rest, ⟨_ + 1, _⟩, σ, ρ, hbo, hscope, hresid, hh, σ', h => grund_gutB bo hbV rest _ σ ρ (by boden_tac) (by scopes_gut) hresid hh σ' h
end
end Rumpf
end Gabbro.Grammatik
