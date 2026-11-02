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
mutual
/-- **Rahmen und Spur einer Anweisung**: ihr Ausgang unterscheidet sich von der Eingangswelt
    hoechstens an Traegern mit Schreibrecht im Vertrag, jede Sperre ist am Ende
    zurueckgegeben, und jedes neue Ereignis traegt seine Waechter. -/
theorem stmt_gutB (bo : Option Int) (hbV : BodenUnter bo V.boden) : ∀ (s : Stmt D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ), s.BodenOk bo → HeldB bo Λ σ.haelt → GutAusgang V.schreibt V.gschreibt σ (execStmt O passes R s σ ρ)
  | .assignSlot t f i e hw hL, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append i.orte_darf e.orte_darf) hh.heldIn
      exact hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldB hh).heldIn)
  | .assignThru p t _ f i e hw hL, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append (orte_append p.orte_darf i.orte_darf) e.orte_darf) hh.heldIn
      exact hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldB hh).heldIn)
  | .assignSlotRef r t _ _ f e hw hL, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append r.orte_darf e.orte_darf) hh.heldIn
      exact hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldB hh).heldIn)
  | .assignGlob g e hw hL, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      exact hl.trans (gut_schreibGlob _ g Λ _ hw hL (hl.heldB hh).heldIn)
  | .putBytes t f hf n i _ _ e hw hL, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append i.orte_darf e.orte_darf) hh.heldIn
      exact hl.trans (gut_schreibBytes _ t f hf Λ hw hL _ _ (hl.heldB hh).heldIn)
  | .assignVar x e, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact gut_lese σ Λ _ e.orte_darf hh.heldIn
  | .shift t f hτ i von nach hn he hw hL, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt] at h; split at h
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_cons (orte_tab hL) i.orte_darf) hh.heldIn
        exact hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldB hh).heldIn)
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .ite c t e, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ c.orte_darf hh.heldIn
      split at h
      · exact (GutAusgang.vor hl (block_gutB bo hbV t _ ρ (by boden_tac) (hl.heldB hh))) σ' h
      · exact (GutAusgang.vor hl (block_gutB bo hbV e _ ρ (by boden_tac) (hl.heldB hh))) σ' h
  | .onOption o p a, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ o.orte_darf hh.heldIn
      split at h
      · exact (GutAusgang.vor hl (block_gutB bo hbV p _ _ (by boden_tac) (hl.heldB hh))).schrumpf σ' h
      · exact (GutAusgang.vor hl (block_gutB bo hbV a _ ρ (by boden_tac) (hl.heldB hh))) σ' h
  | .onTag v arms, σ, ρ, hbo, hh, σ', h => by
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ v.orte_darf hh.heldIn
      exact (GutAusgang.vor hl (arms_gutB bo hbV arms _ _ ρ (by boden_tac) (hl.heldB hh))) σ' h
  | .onWhy r arms, σ, ρ, hbo, hh, σ', h => by
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ r.orte_darf hh.heldIn
      exact (GutAusgang.vor hl (grund_gutB bo hbV arms _ _ ρ (by boden_tac) (hl.heldB hh))) σ' h
  | .call f args hp hr, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      split at h
      · rename_i σ1 v hR1
        simp only [Ausgang.welt, Option.some.injEq] at h; subst h; exact hl.trans (Gut.weiter hp.hw hp.hg (hR f (σ.lese Λ args.orte) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl)))
      · rename_i σ1 r _; exact keinGrund hr r
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .callInd p args hp hr, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append p.orte_darf args.orte_darf) hh.heldIn
      generalize hpv : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = pv at h
      obtain ⟨f, hf⟩ := pv
      simp only at h
      split at h
      · rename_i σ1 v hR1
        simp only [Ausgang.welt, Option.some.injEq] at h; subst h; replace hp := RufPasst.vonPasst (D.passt_sig hf) hp
        exact hl.trans (Gut.weiter hp.hw hp.hg (hR f (σ.lese Λ (p.orte ++ args.orte)) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl)))
      · rename_i σ1 r _; exact keinGrundSig hf hr r
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .callIndElse p args he hp hr err, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt] at h; exact indSonst_gutB R hR bo hbV p args he hp hr σ _ ρ hh (gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append p.orte_darf args.orte_darf) hh.heldIn)
        _ _ (fun s1 _ _ s2 h2 => by simp only [Ausgang.welt, Option.some.injEq] at h2; subst h2; exact Gut.refl _ _ _) (fun s1 r hh1 => (end_gutB bo hbV err s1 _ (by boden_tac) hh1).schrumpf.zuAusgang) σ' h
  | .locks L hr body, σ, ρ, hbo, hh, σ', h =>
      (GutAusgang.gibt L (nicht_gehaltenB L hr hh (fun c hc => by
          have hsc := hbo c hc; simp only [Stmt.ueberBoden, Bool.and_eq_true, decide_eq_true_eq] at hsc; exact hsc.1)) (block_gutB bo hbV body (σ.nimmt L) ρ (by boden_tac) (heldB_locks L hh))) σ' h
  | .breaking _ body, σ, ρ, hbo, hh, σ', h => block_gutB bo hbV body σ ρ (by boden_tac) hh σ' h
  | .traverse t inv body, σ, ρ, hbo, hh, σ', h =>
      traverseLauf_gut (Λ := Λ) _ _ (fun σ ρ hh => block_gutB bo hbV body σ ρ (by boden_tac) hh) (fun σ ρ hh => gut_lese σ Λ _ inv.orte_darf hh.heldIn) _ σ ρ hh σ' h
  | .consumeTraverse t member edge inv bound mass body, σ, ρ, hbo, hh, σ', h =>
      verbrauchLauf_gut (Λ := Λ) t _ _ _ _ _
        (fun σ ρ hh => block_gutB bo hbV body σ ρ (by boden_tac) hh)
        (fun σ ρ hh => gut_lese σ Λ _ inv.orte_darf hh.heldIn)
        (fun σ ρ hh => gut_lese σ Λ _ (orte_append member.orte_darf edge.orte_darf) hh.heldIn)
        (fun σ ρ hh => gut_lese σ Λ _ mass.orte_darf hh.heldIn)
        _ σ ρ hh σ' h
  | .retry n bis body ueberlauf, σ, ρ, hbo, hh, σ', h =>
      retryLauf_gut (Λ := Λ) _ _ _ (fun σ ρ hh => block_gutB bo hbV body σ ρ (by boden_tac) hh) (fun σ ρ hh => gut_lese σ Λ _ bis.orte_darf hh.heldIn) (fun σ ρ hh => block_gutB bo hbV ueberlauf σ ρ (by boden_tac) hh) n σ ρ hh σ' h
  | .forever a inv body, σ, ρ, hbo, hh, σ', h =>
      foreverLauf_gut (Λ := Λ) a _ _ (fun σ ρ hh => block_gutB bo hbV body σ ρ (by boden_tac) hh) (fun σ ρ hh => gut_lese σ Λ _ inv.orte_darf hh.heldIn) passes σ ρ hh σ' h
  | .axiomCall a args _ hw hg hd hgd, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      split at h
      · rename_i σ1 v ha
        simp only [Ausgang.welt, Option.some.injEq] at h; subst h; have := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldB hh).heldIn
        rw [ha] at this
        exact hl.trans (Gut.weiter hw hg this)
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .axiomCallElse _ a args _ hp hd hgd _ err, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      have h1 := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldB hh).heldIn
      rw [← axiomAntwortSonst_fst] at h1
      split at h
      · rename_i σ1 v ha
        simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        rw [ha] at h1
        exact hl.trans (Gut.weiter hp.hw hp.hg h1)
      · rename_i σ1 r ha
        rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg h1)
        exact g1.trans ((end_gutB bo hbV err σ1 _ (by boden_tac) (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf.zuAusgang σ' h)
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .regWrite r _ e, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact gut_lese σ Λ _ e.orte_darf hh.heldIn
  | .transition .., σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact gut_fragt _ _
  | .publish g e _ _ hw hL, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      exact hl.trans (gut_schreibGlob _ g Λ _ hw hL (hl.heldB hh).heldIn)
  | .advances .., σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .retires .., σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .ret e _, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact gut_lese σ Λ _ e.orte_darf hh.heldIn
  | .retScoped e _, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact gut_lese σ Λ _ e.orte_darf hh.heldIn
  | .retWhyScoped .., σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .retWhy .., σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .leave _, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .next _, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
theorem block_gutB (bo : Option Int) (hbV : BodenUnter bo V.boden) : ∀ (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ), b.BodenOk bo → HeldB bo Λ σ.haelt → GutAusgang V.schreibt V.gschreibt σ (execBlock O passes R b σ ρ)
  | .nil, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .cons s rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h; split at h
      · rename_i σ1 ρ1 hs
        have g1 := stmt_gutB bo hbV s σ ρ (by boden_tac) hh σ1 (by rw [hs]; rfl)
        exact g1.trans (block_gutB bo hbV rest σ1 ρ1 (by boden_tac) (heldB_weiter s.held_iff g1 hh) σ' h)
      · subst_vars
        exact stmt_gutB bo hbV s σ ρ (by boden_tac) hh σ' h
  | .bind e rest, σ, ρ, hbo, hh, σ', h => by
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      exact (GutAusgang.vor hl (block_gutB bo hbV rest _ _ (by boden_tac) (hl.heldB hh))).schrumpf σ' h
  | .bindCall f args he hp hr rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      split at h
      · rename_i σ1 v hR1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg (hR f (σ.lese Λ args.orte) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((block_gutB bo hbV rest σ1 _ (by boden_tac) (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf σ' h)
      · rename_i σ1 r _; exact keinGrund hr r
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .bindCallInd p args he hp hr rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append p.orte_darf args.orte_darf) hh.heldIn
      generalize hpv : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = pv at h
      obtain ⟨f, hf⟩ := pv
      simp only at h
      split at h
      · rename_i σ1 v hR1
        have g2 := block_gutB bo hbV rest σ1 (.cons (ergWert (ergSig hf he) v) ρ) (by boden_tac)
        replace hp := RufPasst.vonPasst (D.passt_sig hf) hp
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg (hR f (σ.lese Λ (p.orte ++ args.orte)) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((g2 (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf σ' h)
      · rename_i σ1 r _; exact keinGrundSig hf hr r
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .bindCallIndElse p args he hp hr err rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h
      refine indSonst_gutB R hR bo hbV p args he hp hr σ _ ρ hh (gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append p.orte_darf args.orte_darf) hh.heldIn)
        _ _ ?_ ?_ σ' h
      · exact fun s1 v hh1 => (block_gutB bo hbV rest s1 _ (by boden_tac) hh1).schrumpf
      · exact fun s1 r hh1 => (end_gutB bo hbV err s1 _ (by boden_tac) hh1).schrumpf.zuAusgang
  | .bindCallElse f args he hp _ err rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      split at h
      · rename_i σ1 v hR1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg (hR f (σ.lese Λ args.orte) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((block_gutB bo hbV rest σ1 _ (by boden_tac) (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf σ' h)
      · rename_i σ1 r hR1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg (hR f (σ.lese Λ args.orte) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((end_gutB bo hbV err σ1 _ (by boden_tac) (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf.zuAusgang σ' h)
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .bindAxiom a args he hw hg hd hgd rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      split at h
      · rename_i σ1 v ha
        have h1 := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldB hh).heldIn
        rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hw hg h1)
        exact g1.trans ((block_gutB bo hbV rest σ1 _ (by boden_tac) (g1.heldB hh)).schrumpf σ' h)
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .bindAxiomElse a args he hr hw hg hd hgd err rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      have h1 := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldB hh).heldIn
      rw [← axiomAntwortSonst_fst] at h1
      split at h
      · rename_i σ1 v ha
        rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hw hg h1)
        exact g1.trans ((block_gutB bo hbV rest σ1 _ (by boden_tac) (g1.heldB hh)).schrumpf σ' h)
      · rename_i σ1 r ha
        rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hw hg h1)
        exact g1.trans ((end_gutB bo hbV err σ1 _ (by boden_tac) (g1.heldB hh)).schrumpf.zuAusgang σ' h)
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .bindAxiomOpt e a args he hp hd hgd rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      split at h
      · rename_i σ1 v ha
        have h1 := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldB hh).heldIn
        rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg h1)
        have ihr := fun ρ' => block_gutB bo hbV rest σ1 ρ' (by boden_tac) (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)
        cases e with
        | none =>
            simp only [Ausgang.weiterOpt] at h; exact g1.trans ((ihr _) σ' h)
        | some τ =>
            simp only [Ausgang.weiterOpt] at h; exact g1.trans ((ihr _).schrumpf σ' h)
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .bindAxiomOptElse e a args he hp hd hgd hr err rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      have h1 := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldB hh).heldIn
      rw [← axiomAntwortSonst_fst] at h1
      split at h
      · rename_i σ1 v ha
        rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg h1)
        have ihr := fun ρ' => block_gutB bo hbV rest σ1 ρ' (by boden_tac) (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)
        cases e with
        | none =>
            simp only [Ausgang.weiterOpt] at h; exact g1.trans ((ihr _) σ' h)
        | some τ =>
            simp only [Ausgang.weiterOpt] at h; exact g1.trans ((ihr _).schrumpf σ' h)
      · rename_i σ1 r ha
        rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg h1)
        exact g1.trans ((end_gutB bo hbV err σ1 _ (by boden_tac) (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf.zuAusgang σ' h)
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .regRead r _ rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h
      refine (gut_fragt σ (.inr (.inl r))).trans ?_
      rw [← fragt_haelt σ (.inr (.inl r))] at hh
      generalize σ.fragt (.inr (.inl r)) = σ at h hh ⊢
      split at h
      · split at h
        · exact (block_gutB bo hbV rest σ _ (by boden_tac) hh).schrumpf σ' h
        · simp only [Ausgang.welt, reduceCtorEq] at h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .regReadElse r _ zusage sonst rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h
      refine (gut_fragt σ (.inr (.inl r))).trans ?_
      rw [← fragt_haelt σ (.inr (.inl r))] at hh
      generalize σ.fragt (.inr (.inl r)) = σ at h hh ⊢
      split at h
      · have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ zusage.orte_darf hh.heldIn
        split at h
        · exact (GutAusgang.vor hl (block_gutB bo hbV rest _ _ (by boden_tac) (hl.heldB hh))).schrumpf σ' h
        · exact (GutEnd.vor hl (end_gutB bo hbV sonst _ ρ (by boden_tac) (hl.heldB hh))).zuAusgang σ' h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .awaits g _ _ hL _ rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h
      refine (gut_fragt σ (.inr (.inr g))).trans ?_
      rw [← fragt_haelt σ (.inr (.inr g))] at hh
      generalize σ.fragt (.inr (.inr g)) = σ at h hh ⊢
      split at h
      · have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ [.inr g] (orte_cons (orte_glob hL) (by intro o ho; simp only [List.not_mem_nil] at ho)) hh.heldIn
        exact (GutAusgang.vor hl (block_gutB bo hbV rest _ _ (by boden_tac) (hl.heldB hh))).schrumpf σ' h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .exchange g neu hw hL rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_cons (orte_glob hL) neu.orte_darf) hh.heldIn
      have g1 := hl.trans (gut_schreibGlob (W := V.schreibt) (G := V.gschreibt) (σ.lese Λ (.inr g :: neu.orte)) g Λ (eval (σ.lese Λ (.inr g :: neu.orte)) neu (σ.lese Λ (.inr g :: neu.orte)) (.cons ((σ.lese Λ (.inr g :: neu.orte)).globs g) ρ))
          hw hL (hl.heldB hh).heldIn)
      exact (GutAusgang.vor g1 (block_gutB bo hbV rest _ _ (by boden_tac) (g1.heldB hh))).schrumpf σ' h
  | .narrow e lo' hi' sonst rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      split at h
      · exact (GutAusgang.vor hl (block_gutB bo hbV rest _ _ (by boden_tac) (hl.heldB hh))).schrumpf σ' h
      · exact (GutEnd.vor hl (end_gutB bo hbV sonst _ ρ (by boden_tac) (hl.heldB hh))).zuAusgang σ' h
  | .narrowRequired e lo' hi' rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      split at h
      · exact (GutAusgang.vor hl (block_gutB bo hbV rest _ _ (by boden_tac) (hl.heldB hh))).schrumpf σ' h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .check c sonst rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ c.orte_darf hh.heldIn
      split at h
      · exact (GutAusgang.vor hl (block_gutB bo hbV rest _ ρ (by boden_tac) (hl.heldB hh))) σ' h
      · exact (GutEnd.vor hl (end_gutB bo hbV sonst _ ρ (by boden_tac) (hl.heldB hh))).zuAusgang σ' h
  | .float op a b lo hi rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append a.orte_darf b.orte_darf) hh.heldIn
      split at h
      · exact (GutAusgang.vor hl (block_gutB bo hbV rest _ _ (by boden_tac) (hl.heldB hh))).schrumpf σ' h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .floatLit q lo hi rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h; split at h
      · exact (block_gutB bo hbV rest σ _ (by boden_tac) hh).schrumpf σ' h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .floatOf e lo hi rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      split at h
      · exact (GutAusgang.vor hl (block_gutB bo hbV rest _ _ (by boden_tac) (hl.heldB hh))).schrumpf σ' h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .floatNarrow e lo hi sonst rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      split at h
      · exact (GutAusgang.vor hl (block_gutB bo hbV rest _ _ (by boden_tac) (hl.heldB hh))).schrumpf σ' h
      · exact (GutEnd.vor hl (end_gutB bo hbV sonst _ ρ (by boden_tac) (hl.heldB hh))).zuAusgang σ' h
theorem end_gutB (bo : Option Int) (hbV : BodenUnter bo V.boden) : ∀ (b : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ), b.BodenOk bo → HeldB bo Λ σ.haelt →
    GutEnd V.schreibt V.gschreibt σ (execEnd O passes R b σ ρ)
  | .ret e _, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h; exact gut_lese σ Λ _ e.orte_darf hh.heldIn
  | .retScoped e _, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h; exact gut_lese σ Λ _ e.orte_darf hh.heldIn
  | .retWhyScoped .., σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .retWhy .., σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .leave _, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .next _, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .cons s rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd] at h; have hs := stmt_gutB bo hbV s σ ρ (by boden_tac) hh
      split at h
      · rename_i σ1 ρ1 hs1
        have g1 := hs σ1 (by rw [hs1]; rfl)
        exact g1.trans (end_gutB bo hbV rest σ1 ρ1 (by boden_tac) (heldB_weiter s.held_iff g1 hh) σ' h)
      all_goals first
        | (rename_i hs1; simp only [EndAusgang.welt, Option.some.injEq] at h; subst h
           exact hs _ (by rw [hs1]; rfl))
        | (simp only [EndAusgang.welt, reduceCtorEq] at h)
  | .bind e rest, σ, ρ, hbo, hh, σ', h => by
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      exact (GutEnd.vor hl (end_gutB bo hbV rest _ _ (by boden_tac) (hl.heldB hh))).schrumpf σ' h
  | .bindCall f args he hp hr rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      split at h
      · rename_i σ1 v hR1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg (hR f (σ.lese Λ args.orte) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((end_gutB bo hbV rest σ1 _ (by boden_tac) (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf σ' h)
      · rename_i σ1 r _; exact keinGrund hr r
      · simp only [EndAusgang.welt, reduceCtorEq] at h
      · simp only [EndAusgang.welt, reduceCtorEq] at h
  | .bindCallElse f args he hp _ err rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      split at h
      · rename_i σ1 v hR1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg (hR f (σ.lese Λ args.orte) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((end_gutB bo hbV rest σ1 _ (by boden_tac) (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf σ' h)
      · rename_i σ1 r hR1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg (hR f (σ.lese Λ args.orte) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((end_gutB bo hbV err σ1 _ (by boden_tac) (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf σ' h)
      · simp only [EndAusgang.welt, reduceCtorEq] at h
      · simp only [EndAusgang.welt, reduceCtorEq] at h
  | .bindAxiom a args he hw hg hd hgd rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      split at h
      · rename_i σ1 v ha
        have h1 := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldB hh).heldIn
        rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hw hg h1)
        exact g1.trans ((end_gutB bo hbV rest σ1 _ (by boden_tac) (g1.heldB hh)).schrumpf σ' h)
      · simp only [EndAusgang.welt, reduceCtorEq] at h
  | .bindAxiomElse a args he hr hw hg hd hgd err rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      have h1 := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldB hh).heldIn
      rw [← axiomAntwortSonst_fst] at h1
      split at h
      · rename_i σ1 v ha
        rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hw hg h1)
        exact g1.trans ((end_gutB bo hbV rest σ1 _ (by boden_tac) (g1.heldB hh)).schrumpf σ' h)
      · rename_i σ1 r ha
        rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hw hg h1)
        exact g1.trans ((end_gutB bo hbV err σ1 _ (by boden_tac) (g1.heldB hh)).schrumpf σ' h)
      · simp only [EndAusgang.welt, reduceCtorEq] at h
  | .bindAxiomOpt e a args he hp hd hgd rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      split at h
      · rename_i σ1 v ha
        have h1 := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldB hh).heldIn
        rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg h1)
        have ihr := fun ρ' => end_gutB bo hbV rest σ1 ρ' (by boden_tac) (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)
        cases e with
        | none =>
            simp only [EndAusgang.weiterOpt] at h; exact g1.trans ((ihr _) σ' h)
        | some τ =>
            simp only [EndAusgang.weiterOpt] at h; exact g1.trans ((ihr _).schrumpf σ' h)
      · simp only [EndAusgang.welt, reduceCtorEq] at h
  | .bindAxiomOptElse e a args he hp hd hgd hr err rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      have h1 := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldB hh).heldIn
      rw [← axiomAntwortSonst_fst] at h1
      split at h
      · rename_i σ1 v ha
        rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg h1)
        have ihr := fun ρ' => end_gutB bo hbV rest σ1 ρ' (by boden_tac) (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)
        cases e with
        | none =>
            simp only [EndAusgang.weiterOpt] at h; exact g1.trans ((ihr _) σ' h)
        | some τ =>
            simp only [EndAusgang.weiterOpt] at h; exact g1.trans ((ihr _).schrumpf σ' h)
      · rename_i σ1 r ha
        rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg h1)
        exact g1.trans ((end_gutB bo hbV err σ1 _ (by boden_tac) (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf σ' h)
      · simp only [EndAusgang.welt, reduceCtorEq] at h
  | .regRead r _ rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd] at h
      refine (gut_fragt σ (.inr (.inl r))).trans ?_
      rw [← fragt_haelt σ (.inr (.inl r))] at hh
      generalize σ.fragt (.inr (.inl r)) = σ at h hh ⊢
      split at h
      · split at h
        · exact (end_gutB bo hbV rest σ _ (by boden_tac) hh).schrumpf σ' h
        · simp only [EndAusgang.welt, reduceCtorEq] at h
      · simp only [EndAusgang.welt, reduceCtorEq] at h
  | .regReadElse r _ zusage sonst rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd] at h
      refine (gut_fragt σ (.inr (.inl r))).trans ?_
      rw [← fragt_haelt σ (.inr (.inl r))] at hh
      generalize σ.fragt (.inr (.inl r)) = σ at h hh ⊢
      split at h
      · have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ zusage.orte_darf hh.heldIn
        split at h
        · exact (GutEnd.vor hl (end_gutB bo hbV rest _ _ (by boden_tac) (hl.heldB hh))).schrumpf σ' h
        · exact (GutEnd.vor hl (end_gutB bo hbV sonst _ ρ (by boden_tac) (hl.heldB hh))) σ' h
      · simp only [EndAusgang.welt, reduceCtorEq] at h
  | .awaits g _ _ hL _ rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd] at h
      refine (gut_fragt σ (.inr (.inr g))).trans ?_
      rw [← fragt_haelt σ (.inr (.inr g))] at hh
      generalize σ.fragt (.inr (.inr g)) = σ at h hh ⊢
      split at h
      · have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ [.inr g] (orte_cons (orte_glob hL) (by intro o ho; simp only [List.not_mem_nil] at ho)) hh.heldIn
        exact (GutEnd.vor hl (end_gutB bo hbV rest _ _ (by boden_tac) (hl.heldB hh))).schrumpf σ' h
      · simp only [EndAusgang.welt, reduceCtorEq] at h
  | .bindCallInd p args he hp hr rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append p.orte_darf args.orte_darf) hh.heldIn
      generalize hpv : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = pv at h
      obtain ⟨f, hf⟩ := pv
      simp only at h
      split at h
      · rename_i σ1 v hR1
        have g2 := end_gutB bo hbV rest σ1 (.cons (ergWert (ergSig hf he) v) ρ) (by boden_tac)
        replace hp := RufPasst.vonPasst (D.passt_sig hf) hp
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg (hR f (σ.lese Λ (p.orte ++ args.orte)) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((g2 (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf σ' h)
      · rename_i σ1 r _; exact keinGrundSig hf hr r
      · simp only [EndAusgang.welt, reduceCtorEq] at h
      · simp only [EndAusgang.welt, reduceCtorEq] at h
  | .bindCallIndElse p args he hp hr err rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd] at h; exact indSonstE_gutB R hR bo hbV p args he hp hr σ _ ρ hh (gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append p.orte_darf args.orte_darf) hh.heldIn)
        _
        _ (fun s1 v hh1 => (end_gutB bo hbV rest s1 _ (by boden_tac) hh1).schrumpf) (fun s1 r hh1 => (end_gutB bo hbV err s1 _ (by boden_tac) hh1).schrumpf) σ' h
  | .narrow e lo' hi' sonst rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      split at h
      · exact (GutEnd.vor hl (end_gutB bo hbV rest _ _ (by boden_tac) (hl.heldB hh))).schrumpf σ' h
      · exact (GutEnd.vor hl (end_gutB bo hbV sonst _ ρ (by boden_tac) (hl.heldB hh))) σ' h
  | .narrowRequired e lo' hi' rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      split at h
      · exact (GutEnd.vor hl (end_gutB bo hbV rest _ _ (by boden_tac) (hl.heldB hh))).schrumpf σ' h
      · simp only [EndAusgang.welt, reduceCtorEq] at h
  | .exchange g neu hw hL rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_cons (orte_glob hL) neu.orte_darf) hh.heldIn
      have g1 := hl.trans (gut_schreibGlob (W := V.schreibt) (G := V.gschreibt) (σ.lese Λ (.inr g :: neu.orte)) g Λ (eval (σ.lese Λ (.inr g :: neu.orte)) neu (σ.lese Λ (.inr g :: neu.orte)) (.cons ((σ.lese Λ (.inr g :: neu.orte)).globs g) ρ))
          hw hL (hl.heldB hh).heldIn)
      exact (GutEnd.vor g1 (end_gutB bo hbV rest _ _ (by boden_tac) (g1.heldB hh))).schrumpf σ' h
  | .ite c t e, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd] at h; have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ c.orte_darf hh.heldIn
      split at h
      · exact (GutEnd.vor hl (end_gutB bo hbV t _ ρ (by boden_tac) (hl.heldB hh))) σ' h
      · exact (GutEnd.vor hl (end_gutB bo hbV e _ ρ (by boden_tac) (hl.heldB hh))) σ' h
theorem arms_gutB (bo : Option Int) (hbV : BodenUnter bo V.boden) : ∀ (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)) (σ : World D) (ρ : Env D Γ),
    arms.BodenOk bo → HeldB bo Λ σ.haelt → GutAusgang V.schreibt V.gschreibt σ (execArms O passes R arms v σ ρ)
  | .cons b _, ⟨⟨0, _⟩, _⟩, σ, _, hbo, hh, σ', h => (block_gutB bo hbV b σ _ (by boden_tac) hh).schrumpfArm _ σ' h
  | .cons _ rest, ⟨⟨_ + 1, _⟩, _⟩, σ, ρ, hbo, hh, σ', h => arms_gutB bo hbV rest _ σ ρ (by boden_tac) hh σ' h
theorem grund_gutB (bo : Option Int) (hbV : BodenUnter bo V.boden) : ∀ (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n) (σ : World D) (ρ : Env D Γ),
    arms.BodenOk bo → HeldB bo Λ σ.haelt → GutAusgang V.schreibt V.gschreibt σ (execGrund O passes R arms r σ ρ)
  | .cons b _, ⟨0, _⟩, σ, ρ, hbo, hh, σ', h => block_gutB bo hbV b σ ρ (by boden_tac) hh σ' h
  | .cons _ rest, ⟨_ + 1, _⟩, σ, ρ, hbo, hh, σ', h => grund_gutB bo hbV rest _ σ ρ (by boden_tac) hh σ' h
end
end Rumpf
end Gabbro.Grammatik
