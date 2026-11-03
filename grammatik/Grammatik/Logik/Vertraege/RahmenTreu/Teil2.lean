module

public import Grammatik.Logik.Vertraege.RahmenTreu.Tactics
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil1
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil2BindBlock
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil2BindEnd
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

mutual

/-- **The frame and the held locks of one statement**, under the entry
    discipline. Reads, writes and `locks` need none of it; call arms restore
    the frame (`TreuR` under the transported entry discipline, propagated
    reasons via `TreuRet.toTreu_entry`), scoped returns check it. -/
theorem stmt_treu (bo : Option Int) (hbV : BodenUnter bo V.boden) :
    ∀ (s : Stmt D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ), s.ScopesOk →
    HeldB bo Λ σ.haelt →
    TreuAusgang V.schreibt V.gschreibt σ (execStmt O passes R s σ ρ)
  | .assignSlot t f i e hw hL, σ, ρ, _hscope, _hh, σ', h => by
      frame_value execStmt Ausgang.welt; exact (treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _).trans
        (treu_schreibSlot _ t Λ _ f _ hw)
  | .assignThru p t _ f i e hw hL, σ, ρ, _hscope, _hh, σ', h => by
      frame_value execStmt Ausgang.welt; exact (treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _).trans
        (treu_schreibSlot _ t Λ _ f _ hw)
  | .assignThruOwn p t _ f i e _ _ _ _ _ hw hL, σ, ρ, _hscope, _hh, σ', h => by
      frame_value execStmt Ausgang.welt; exact (treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _).trans
        (treu_schreibSlot _ t Λ _ f _ hw)
  | .assignSlotRef r t _ _ f e hw hL, σ, ρ, _hscope, _hh, σ', h => by
      frame_value execStmt Ausgang.welt; exact (treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _).trans
        (treu_schreibSlot _ t Λ _ f _ hw)
  | .assignGlob g e hw hL, σ, ρ, _hscope, _hh, σ', h => by
      frame_value execStmt Ausgang.welt; exact (treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _).trans
        (treu_schreibGlob _ g Λ _ hw)
  | .putBytes t f hf n i _ _ e hw hL, σ, ρ, _hscope, _hh, σ', h => by
      frame_value execStmt Ausgang.welt; exact (treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _).trans
        (treu_schreibBytes _ t f hf Λ hw _ _)
  | .assignVar x e, σ, ρ, _hscope, _hh, σ', h => by
      frame_value execStmt Ausgang.welt; exact treu_lese σ Λ _
  | .shift t f hτ i von nach hn he hw hL, σ, ρ, _hscope, _hh, σ', h => by
      simp only [execStmt] at h ⊢
      by_cases hc : (hτ ▸ (σ.lese Λ (.inl t :: i.orte)).slots t (eval (σ.lese Λ (.inl t :: i.orte)) i (σ.lese Λ (.inl t :: i.orte)) ρ).n f : Zahl _ _).n = von <;> simp only [hc, ite_true, ite_false, Bool.true_eq_false, Bool.false_eq_true] at h ⊢
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        exact (treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _).trans
          (treu_schreibSlot _ t Λ _ f _ hw)
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .ite c t e, σ, ρ, hscope, hh, σ', h => by
      have hscope_t : t.ScopesOk := by scopes_treu
      have hscope_e : e.ScopesOk := by scopes_treu
      simp only [execStmt] at h ⊢
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ c.orte
      by_cases hc : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true <;> simp only [hc, ite_true, ite_false, Bool.true_eq_false, Bool.false_eq_true] at h ⊢
      · exact (TreuAusgang.vor hl (block_treu bo hbV t _ _ hscope_t (hl.heldB hh))) σ' h
      · exact (TreuAusgang.vor hl (block_treu bo hbV e _ _ hscope_e (hl.heldB hh))) σ' h
  | .onOption o p a, σ, ρ, hscope, hh, σ', h => by
      have hscope_p : p.ScopesOk := by scopes_treu
      have hscope_a : a.ScopesOk := by scopes_treu
      simp only [execStmt] at h ⊢
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ o.orte
      generalize hv : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = ov at h ⊢
      cases ov with
      | some v => exact (TreuAusgang.vor hl (block_treu bo hbV p _ _ hscope_p (hl.heldB hh))).schrumpf σ' h
      | none => exact (TreuAusgang.vor hl (block_treu bo hbV a _ _ hscope_a (hl.heldB hh))) σ' h
  | .onTag v arms, σ, ρ, hscope, hh, σ', h => by
      have hscope_a : arms.ScopesOk := by scopes_treu
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ v.orte
      exact (TreuAusgang.vor hl (arms_treu bo hbV arms _ _ _ hscope_a (hl.heldB hh))) σ' h
  | .onWhy r arms, σ, ρ, hscope, hh, σ', h => by
      have hscope_a : arms.ScopesOk := by scopes_treu
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ r.orte
      exact (TreuAusgang.vor hl (grund_treu bo hbV arms _ _ _ hscope_a (hl.heldB hh))) σ' h
  | .call f args hp hr, σ, ρ, _hscope, hh, σ', h => by
      simp only [execStmt] at h ⊢
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
      generalize hR1 : R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = rv at h ⊢
      cases rv with
      | ok σ1 v =>
          simp only [Ausgang.welt, Option.some.injEq] at h; subst h
          frame_call_ok (σ.lese Λ args.orte)
          exact g1
      | why σ1 r => exact keinGrund hr r
      | logik _ => simp only [Ausgang.welt, reduceCtorEq] at h
      | hardware _ => simp only [Ausgang.welt, reduceCtorEq] at h
  | .callInd p args hp hr, σ, ρ, _hscope, hh, σ', h => by
      simp only [execStmt] at h ⊢
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (p.orte ++ args.orte)
      generalize hpv : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = pv at h ⊢
      obtain ⟨f, hf⟩ := pv
      simp only at h ⊢
      replace hp := RufPasst.vonPasst (D.passt_sig hf) hp
      generalize hR1 : R f (σ.lese Λ (p.orte ++ args.orte)) (umsig hf (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args (σ.lese Λ (p.orte ++ args.orte)) ρ)) = rv at h ⊢
      cases rv with
      | ok σ1 v =>
          simp only [Ausgang.welt, Option.some.injEq] at h; subst h
          frame_call_ok (σ.lese Λ (p.orte ++ args.orte))
          exact g1
      | why σ1 r => exact keinGrundSig hf hr r
      | logik _ => simp only [Ausgang.welt, reduceCtorEq] at h
      | hardware _ => simp only [Ausgang.welt, reduceCtorEq] at h
  | .callIndElse p args he hp hr err, σ, ρ, hscope, hh, σ', h => by
      simp only [execStmt] at h
      have hscope_err : err.ScopesOk := by scopes_treu
      exact indSonst_treu R hR p args he hp hr σ _ ρ (treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (p.orte ++ args.orte))
        bo hbV hh
        _ _
        (fun s1 _ _ s2 h2 => by simp only [Ausgang.welt, Option.some.injEq] at h2; subst h2; exact Treu.refl _ _ _) (fun s1 r hh1 => (end_treu bo hbV err s1 _ hscope_err hh1).schrumpf.zuAusgang) σ' h
  | .locks L hr body, σ, ρ, hscope, hh, σ', h => by
      have hscope_body : body.ScopesOk := by scopes_treu
      exact (TreuAusgang.gibt L (block_treu bo hbV body (σ.nimmt L) ρ hscope_body (heldB_locks L hh))) σ' h
  | .breaking _ body, σ, ρ, hscope, hh, σ', h => by
      have hscope_body : body.ScopesOk := by scopes_treu
      exact block_treu bo hbV body σ ρ hscope_body hh σ' h
  | .traverse t inv body, σ, ρ, hscope, hh, σ', h => by
      have hscope_body : body.ScopesOk := by scopes_treu
      exact traverseLauf_treu bo _ _ _ (fun σ ρ hh => block_treu bo hbV body σ ρ hscope_body hh)
        (fun σ ρ _ => treu_lese σ Λ inv.orte) _ σ ρ hh σ' h
  | .consumeTraverse t member edge inv bound mass body, σ, ρ, hscope, hh, σ', h => by
      have hscope_body : body.ScopesOk := by scopes_treu
      exact verbrauchLauf_treu bo _ t _ _ _ _ _
        (fun σ ρ hh => block_treu bo hbV body σ ρ hscope_body hh)
        (fun σ ρ _ => treu_lese σ Λ inv.orte)
        (fun σ ρ _ => treu_lese σ Λ (member.orte ++ edge.orte))
        (fun σ ρ _ => treu_lese σ Λ mass.orte) _ σ ρ hh σ' h
  | .retry n bis body ueberlauf, σ, ρ, hscope, hh, σ', h => by
      have hscope_body : body.ScopesOk := by scopes_treu
      have hscope_ueber : ueberlauf.ScopesOk := by scopes_treu
      exact retryLauf_treu bo _ _ _ _ (fun σ ρ hh => block_treu bo hbV body σ ρ hscope_body hh)
        (fun σ ρ _ => treu_lese σ Λ bis.orte)
        (fun σ ρ hh => block_treu bo hbV ueberlauf σ ρ hscope_ueber hh) n σ ρ hh σ' h
  | .forever a inv body, σ, ρ, hscope, hh, σ', h => by
      have hscope_body : body.ScopesOk := by scopes_treu
      exact foreverLauf_treu bo _ a _ _ (fun σ ρ hh => block_treu bo hbV body σ ρ hscope_body hh)
        (fun σ ρ _ => treu_lese σ Λ inv.orte) passes σ ρ hh σ' h
  | .axiomCall a args _ hw hg hd hgd, σ, ρ, _hscope, _hh, σ', h => by
      simp only [execStmt] at h ⊢
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
      generalize ha : axiomAntwort O a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = av at h ⊢
      rcases av with ⟨σ1, _ | v⟩
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
        rw [ha] at h1
        exact hl.trans (Treu.weiter hw hg h1)
  | .axiomCallElse _ a args _ hp hd hgd _ err, σ, ρ, hscope, hh, σ', h => by
      simp only [execStmt] at h ⊢
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ args.orte
      have hscope_err : err.ScopesOk := by scopes_treu
      frame_axiom_else
      generalize ha : axiomAntwortSonst O a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = av at h ⊢
      rcases av with ⟨σ1, _ | (v | r)⟩
      · simp only [Ausgang.welt, reduceCtorEq] at h
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        rw [ha] at h1
        exact hl.trans (Treu.weiter hp.hw hp.hg h1)
      · rw [ha] at h1
        have g1 := hl.trans (Treu.weiter hp.hw hp.hg h1)
        exact (TreuAusgang.vorCall g1 ((end_treu bo hbV err σ1 _ hscope_err
          (HeldB.of_iff (fun L => held_nachSig_iff _ _ L) (g1.heldB hh))).schrumpf.zuAusgang)) σ' h
  | .regWrite r _ e, σ, ρ, _hscope, _hh, σ', h => by
      frame_value execStmt Ausgang.welt; exact treu_lese σ Λ _
  | .transition .., σ, ρ, _hscope, _hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _
  | .publish g e _ _ hw hL, σ, ρ, _hscope, _hh, σ', h => by
      frame_value execStmt Ausgang.welt; exact (treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _).trans
        (treu_schreibGlob _ g Λ _ hw)
  | .advances .., σ, ρ, _hscope, _hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _
  | .retires .., σ, ρ, _hscope, _hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _
  | .ret e _, σ, ρ, _hscope, _hh, σ', h => by
      frame_value execStmt Ausgang.welt; exact (treu_lese σ Λ _).toRet
  | .retWhy .., σ, ρ, _hscope, _hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact (Treu.refl _ _ _).toRet
  | .retScoped e R, σ, ρ, hscope, _hh, σ', h => by
      frame_value execStmt Ausgang.welt
      have hsc : scopesOkScopes V.haelt V.boden R.scopes = true := by scopes_treu
      exact treuRet_retScoped R.scopes (treu_lese σ Λ _)
        (fun L hL => (scopesOkScopes_mem hsc hL).1)
        (fun L hL c hc => (scopesOkScopes_mem hsc hL).2 c hc)
  | .retWhyScoped _ R, σ, ρ, hscope, _hh, σ', h => by
      frame_value execStmt Ausgang.welt
      have hsc : scopesOkScopes V.haelt V.boden R.scopes = true := by scopes_treu
      exact treuRet_retWhyScoped σ R.scopes
        (fun L hL => (scopesOkScopes_mem hsc hL).1)
        (fun L hL c hc => (scopesOkScopes_mem hsc hL).2 c hc)
  | .leave _, σ, ρ, _hscope, _hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _
  | .next _, σ, ρ, _hscope, _hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _

theorem block_treu (bo : Option Int) (hbV : BodenUnter bo V.boden) :
    ∀ (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ), b.ScopesOk →
    HeldB bo Λ σ.haelt →
    TreuAusgang V.schreibt V.gschreibt σ (execBlock O passes R b σ ρ)
  | .nil, σ, ρ, _hscope, _hh, σ', h => by
      simp only [execBlock, Ausgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _
  | .cons s rest, σ, ρ, hscope, hh, σ', h => by
      simp only [execBlock] at h ⊢
      have hscope_s : s.ScopesOk := by scopes_treu
      have hscope_rest : rest.ScopesOk := by scopes_treu
      generalize hs : execStmt O passes R s σ ρ = sv at h ⊢
      cases sv
      · rename_i σ1 ρ1
        have g1 := stmt_treu bo hbV s σ ρ hscope_s hh σ1 (by rw [hs]; rfl); rw [hs] at g1
        exact (TreuAusgang.vorCall g1 (block_treu bo hbV rest σ1 ρ1 hscope_rest
          (HeldB.of_iff s.held_iff (g1.heldB hh)))) σ' h
      all_goals simpa only [hs] using stmt_treu bo hbV s σ ρ hscope_s hh σ' (by simpa only [hs] using h)
  | .bind e rest, σ, ρ, hscope, hh, σ', h => by
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
      have hscope_rest : rest.ScopesOk := by scopes_treu
      exact (TreuAusgang.vor hl (block_treu bo hbV rest _ _ hscope_rest (hl.heldB hh))).schrumpf σ' h
  | .bindCall f args he hp hr rest, σ, ρ, hscope, hh, σ', h => by
      exact block_bindCall_treu O passes R hR hO bo hbV f args he hp hr rest (fun σ ρ hs hh => block_treu bo hbV rest σ ρ hs hh) σ ρ hscope hh σ' h
  | .bindCallInd p args he hp hr rest, σ, ρ, hscope, hh, σ', h => by
      exact block_bindCallInd_treu O passes R hR hO bo hbV p args he hp hr rest (fun σ ρ hs hh => block_treu bo hbV rest σ ρ hs hh) σ ρ hscope hh σ' h
  | .bindCallIndElse p args he hp hr err rest, σ, ρ, hscope, hh, σ', h => by
      simp only [execBlock] at h
      have hscope_rest : rest.ScopesOk := by scopes_treu
      have hscope_err : err.ScopesOk := by scopes_treu
      exact indSonst_treu R hR p args he hp hr σ _ ρ (treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (p.orte ++ args.orte))
        bo hbV hh
        _ _
        (fun s1 v hh1 => (block_treu bo hbV rest s1 _ hscope_rest hh1).schrumpf) (fun s1 r hh1 => (end_treu bo hbV err s1 _ hscope_err hh1).schrumpf.zuAusgang) σ' h
  | .bindCallElse f args he hp hr err rest, σ, ρ, hscope, hh, σ', h => by
      exact block_bindCallElse_treu O passes R hR hO bo hbV f args he hp hr err rest (fun σ ρ hs hh => block_treu bo hbV rest σ ρ hs hh) (fun σ ρ hs hh => end_treu bo hbV err σ ρ hs hh) σ ρ hscope hh σ' h
  | .bindAxiom a args he hw hg hd hgd rest, σ, ρ, hscope, hh, σ', h => by
      exact block_bindAxiom_treu O passes R hR hO bo hbV a args he hw hg hd hgd rest (fun σ ρ hs hh => block_treu bo hbV rest σ ρ hs hh) σ ρ hscope hh σ' h
  | .bindAxiomElse a args he hr hw hg hd hgd err rest, σ, ρ, hscope, hh, σ', h => by
      exact block_bindAxiomElse_treu O passes R hR hO bo hbV a args he hr hw hg hd hgd err rest (fun σ ρ hs hh => block_treu bo hbV rest σ ρ hs hh) (fun σ ρ hs hh => end_treu bo hbV err σ ρ hs hh) σ ρ hscope hh σ' h
  | .bindAxiomOpt e a args he hp hd hgd rest, σ, ρ, hscope, hh, σ', h => by
      exact block_bindAxiomOpt_treu O passes R hR hO bo hbV e a args he hp hd hgd rest (fun σ ρ hs hh => block_treu bo hbV rest σ ρ hs hh) σ ρ hscope hh σ' h
  | .bindAxiomOptElse e a args he hp hd hgd hr err rest, σ, ρ, hscope, hh, σ', h => by
      exact block_bindAxiomOptElse_treu O passes R hR hO bo hbV e a args he hp hd hgd hr err rest (fun σ ρ hs hh => block_treu bo hbV rest σ ρ hs hh) (fun σ ρ hs hh => end_treu bo hbV err σ ρ hs hh) σ ρ hscope hh σ' h
  | .regRead r _ rest, σ, ρ, hscope, hh, σ', h => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      simp only [execBlock] at h ⊢
      refine (TreuAusgang.vor (treu_fragt σ (.inr (.inl r))) ?_) σ' h; intro σ' h
      rw [← fragt_haelt σ (.inr (.inl r))] at hh
      generalize σ.fragt (.inr (.inl r)) = σ at h hh ⊢
      generalize hv : einpassen O.zeiger (D.rtyp r) (O.regLies r σ) = ov at h ⊢
      cases ov with
      | some v =>
          by_cases hc : D.rzusage r v = true <;> simp only [hc, ite_true, ite_false, Bool.true_eq_false, Bool.false_eq_true] at h ⊢
          · exact (block_treu bo hbV rest σ _ hscope_rest hh).schrumpf σ' h
          · simp only [Ausgang.welt, reduceCtorEq] at h
      | none => simp only [Ausgang.welt, reduceCtorEq] at h
  | .regReadElse r hk zusage sonst rest, σ, ρ, hscope, hh, σ', h => by
      exact block_regReadElse_treu O passes R hR hO bo hbV r hk zusage sonst rest (fun σ ρ hs hh => block_treu bo hbV rest σ ρ hs hh) (fun σ ρ hs hh => end_treu bo hbV sonst σ ρ hs hh) σ ρ hscope hh σ' h
  | .awaits g _ _ hL _ rest, σ, ρ, hscope, hh, σ', h => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      simp only [execBlock] at h ⊢
      refine (TreuAusgang.vor (treu_fragt σ (.inr (.inr g))) ?_) σ' h; intro σ' h
      rw [← fragt_haelt σ (.inr (.inr g))] at hh
      generalize σ.fragt (.inr (.inr g)) = σ at h hh ⊢
      by_cases hc : O.sichtbar g σ = true <;> simp only [hc, ite_true, ite_false, Bool.true_eq_false, Bool.false_eq_true] at h ⊢
      · have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ [.inr g]
        exact (TreuAusgang.vor hl (block_treu bo hbV rest _ _ hscope_rest (hl.heldB hh))).schrumpf σ' h
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .exchange g neu hw hL rest, σ, ρ, hscope, hh, σ', h => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      simp only [execBlock] at h ⊢
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (.inr g :: neu.orte)
      have g1 := hl.trans (treu_schreibGlob (W := V.schreibt) (G := V.gschreibt)
        (σ.lese Λ (.inr g :: neu.orte)) g Λ (eval (σ.lese Λ (.inr g :: neu.orte)) neu
          (σ.lese Λ (.inr g :: neu.orte)) (.cons ((σ.lese Λ (.inr g :: neu.orte)).globs g) ρ))
          hw)
      exact (TreuAusgang.vor g1 (block_treu bo hbV rest _ _ hscope_rest (g1.heldB hh))).schrumpf σ' h
  | .narrow e lo' hi' sonst rest, σ, ρ, hscope, hh, σ', h => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      have hscope_sonst : sonst.ScopesOk := by scopes_treu
      simp only [execBlock] at h ⊢
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
      by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi' <;> simp only [hc, dif_pos, dif_neg] at h ⊢
      · exact (TreuAusgang.vor hl (block_treu bo hbV rest _ _ hscope_rest (hl.heldB hh))).schrumpf σ' h
      · exact (TreuEnd.vor hl (end_treu bo hbV sonst _ ρ hscope_sonst (hl.heldB hh))).zuAusgang σ' h
  | .narrowRequired e lo' hi' rest, σ, ρ, hscope, hh, σ', h => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      simp only [execBlock] at h ⊢
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
      by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi' <;> simp only [hc, dif_pos, dif_neg] at h ⊢
      · exact (TreuAusgang.vor hl (block_treu bo hbV rest _ _ hscope_rest (hl.heldB hh))).schrumpf σ' h
      · simp only [dite_false, Ausgang.welt, reduceCtorEq] at h
  | .check c sonst rest, σ, ρ, hscope, hh, σ', h => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      have hscope_sonst : sonst.ScopesOk := by scopes_treu
      simp only [execBlock] at h ⊢
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ c.orte
      by_cases hc : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true <;> simp only [hc, ite_true, ite_false, Bool.true_eq_false, Bool.false_eq_true] at h ⊢
      · exact (TreuAusgang.vor hl (block_treu bo hbV rest _ ρ hscope_rest (hl.heldB hh))) σ' h
      · exact (TreuEnd.vor hl (end_treu bo hbV sonst _ ρ hscope_sonst (hl.heldB hh))).zuAusgang σ' h
  | .float op a b lo hi rest, σ, ρ, hscope, hh, σ', h => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      simp only [execBlock] at h ⊢
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (a.orte ++ b.orte)
      generalize hv : gleitPasst lo hi (gleitRechne op (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) = ov at h ⊢
      cases ov with
      | some v => exact (TreuAusgang.vor hl (block_treu bo hbV rest _ _ hscope_rest (hl.heldB hh))).schrumpf σ' h
      | none => simp only [Ausgang.welt, reduceCtorEq] at h
  | .floatLit q lo hi rest, σ, ρ, hscope, hh, σ', h => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      simp only [execBlock] at h ⊢
      generalize hv : gleitPasst lo hi (bruch q) = ov at h ⊢
      cases ov with
      | some v => exact (block_treu bo hbV rest σ _ hscope_rest hh).schrumpf σ' h
      | none => simp only [Ausgang.welt, reduceCtorEq] at h
  | .floatOf e lo hi rest, σ, ρ, hscope, hh, σ', h => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      simp only [execBlock] at h ⊢
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
      generalize hv : gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n) = ov at h ⊢
      cases ov with
      | some v => exact (TreuAusgang.vor hl (block_treu bo hbV rest _ _ hscope_rest (hl.heldB hh))).schrumpf σ' h
      | none => simp only [Ausgang.welt, reduceCtorEq] at h
  | .floatNarrow e lo hi sonst rest, σ, ρ, hscope, hh, σ', h => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      have hscope_sonst : sonst.ScopesOk := by scopes_treu
      simp only [execBlock] at h ⊢
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
      generalize hv : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = ov at h ⊢
      cases ov with
      | some v => exact (TreuAusgang.vor hl (block_treu bo hbV rest _ _ hscope_rest (hl.heldB hh))).schrumpf σ' h
      | none => exact (TreuEnd.vor hl (end_treu bo hbV sonst _ ρ hscope_sonst (hl.heldB hh))).zuAusgang σ' h

theorem end_treu (bo : Option Int) (hbV : BodenUnter bo V.boden) :
    ∀ (b : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ), b.ScopesOk →
    HeldB bo Λ σ.haelt →
    TreuEnd V.schreibt V.gschreibt σ (execEnd O passes R b σ ρ)
  | .ret e _, σ, ρ, _hscope, _hh, σ', h => by
      frame_value execEnd EndAusgang.welt; exact (treu_lese σ Λ _).toRet
  | .retWhy .., σ, ρ, _hscope, _hh, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h; exact (Treu.refl _ _ _).toRet
  | .retScoped e R, σ, ρ, hscope, _hh, σ', h => by
      frame_value execEnd EndAusgang.welt
      have hsc : scopesOkScopes V.haelt V.boden R.scopes = true := by scopes_treu
      exact treuRet_retScoped R.scopes (treu_lese σ Λ _)
        (fun L hL => (scopesOkScopes_mem hsc hL).1)
        (fun L hL c hc => (scopesOkScopes_mem hsc hL).2 c hc)
  | .retWhyScoped _ R, σ, ρ, hscope, _hh, σ', h => by
      frame_value execEnd EndAusgang.welt
      have hsc : scopesOkScopes V.haelt V.boden R.scopes = true := by scopes_treu
      exact treuRet_retWhyScoped σ R.scopes
        (fun L hL => (scopesOkScopes_mem hsc hL).1)
        (fun L hL c hc => (scopesOkScopes_mem hsc hL).2 c hc)
  | .leave _, σ, ρ, _hscope, _hh, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _
  | .next _, σ, ρ, _hscope, _hh, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h; exact Treu.refl _ _ _
  | .cons s rest, σ, ρ, hscope, hh, σ', h => by
      simp only [execEnd] at h ⊢
      have hscope_s : s.ScopesOk := by scopes_treu
      have hscope_rest : rest.ScopesOk := by scopes_treu
      have hs := stmt_treu bo hbV s σ ρ hscope_s hh
      generalize hs1 : execStmt O passes R s σ ρ = sv at h ⊢
      cases sv
      · rename_i σ1 ρ1
        have g1 := hs σ1 (by rw [hs1]; rfl); rw [hs1] at g1
        exact (TreuEnd.vorCall g1 (end_treu bo hbV rest σ1 ρ1 hscope_rest
          (HeldB.of_iff s.held_iff (g1.heldB hh)))) σ' h
      all_goals first
        | (simp only [EndAusgang.welt, Option.some.injEq] at h; subst h
           simpa only [hs1] using hs _ (by rw [hs1]; rfl))
        | (simp only [EndAusgang.welt, reduceCtorEq] at h)
  | .bind e rest, σ, ρ, hscope, hh, σ', h => by
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
      have hscope_rest : rest.ScopesOk := by scopes_treu
      exact (TreuEnd.vor hl (end_treu bo hbV rest _ _ hscope_rest (hl.heldB hh))).schrumpf σ' h
  | .bindCall f args he hp hr rest, σ, ρ, hscope, hh, σ', h => by
      exact end_bindCall_treu O passes R hR hO bo hbV f args he hp hr rest (fun σ ρ hs hh => end_treu bo hbV rest σ ρ hs hh) σ ρ hscope hh σ' h
  | .bindCallElse f args he hp hr err rest, σ, ρ, hscope, hh, σ', h => by
      exact end_bindCallElse_treu O passes R hR hO bo hbV f args he hp hr err rest (fun σ ρ hs hh => end_treu bo hbV rest σ ρ hs hh) (fun σ ρ hs hh => end_treu bo hbV err σ ρ hs hh) σ ρ hscope hh σ' h
  | .bindAxiom a args he hw hg hd hgd rest, σ, ρ, hscope, hh, σ', h => by
      exact end_bindAxiom_treu O passes R hR hO bo hbV a args he hw hg hd hgd rest (fun σ ρ hs hh => end_treu bo hbV rest σ ρ hs hh) σ ρ hscope hh σ' h
  | .bindAxiomElse a args he hr hw hg hd hgd err rest, σ, ρ, hscope, hh, σ', h => by
      exact end_bindAxiomElse_treu O passes R hR hO bo hbV a args he hr hw hg hd hgd err rest (fun σ ρ hs hh => end_treu bo hbV rest σ ρ hs hh) (fun σ ρ hs hh => end_treu bo hbV err σ ρ hs hh) σ ρ hscope hh σ' h
  | .bindAxiomOpt e a args he hp hd hgd rest, σ, ρ, hscope, hh, σ', h => by
      exact end_bindAxiomOpt_treu O passes R hR hO bo hbV e a args he hp hd hgd rest (fun σ ρ hs hh => end_treu bo hbV rest σ ρ hs hh) σ ρ hscope hh σ' h
  | .bindAxiomOptElse e a args he hp hd hgd hr err rest, σ, ρ, hscope, hh, σ', h => by
      exact end_bindAxiomOptElse_treu O passes R hR hO bo hbV e a args he hp hd hgd hr err rest (fun σ ρ hs hh => end_treu bo hbV rest σ ρ hs hh) (fun σ ρ hs hh => end_treu bo hbV err σ ρ hs hh) σ ρ hscope hh σ' h
  | .regRead r _ rest, σ, ρ, hscope, hh, σ', h => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      simp only [execEnd] at h ⊢
      refine (TreuEnd.vor (treu_fragt σ (.inr (.inl r))) ?_) σ' h; intro σ' h
      rw [← fragt_haelt σ (.inr (.inl r))] at hh
      generalize σ.fragt (.inr (.inl r)) = σ at h hh ⊢
      generalize hv : einpassen O.zeiger (D.rtyp r) (O.regLies r σ) = ov at h ⊢
      cases ov with
      | some v =>
          by_cases hc : D.rzusage r v = true <;> simp only [hc, ite_true, ite_false, Bool.true_eq_false, Bool.false_eq_true] at h ⊢
          · exact (end_treu bo hbV rest σ _ hscope_rest hh).schrumpf σ' h
          · simp only [EndAusgang.welt, reduceCtorEq] at h
      | none => simp only [EndAusgang.welt, reduceCtorEq] at h
  | .regReadElse r hk zusage sonst rest, σ, ρ, hscope, hh, σ', h => by
      exact end_regReadElse_treu O passes R hR hO bo hbV r hk zusage sonst rest (fun σ ρ hs hh => end_treu bo hbV rest σ ρ hs hh) (fun σ ρ hs hh => end_treu bo hbV sonst σ ρ hs hh) σ ρ hscope hh σ' h
  | .awaits g _ _ hL _ rest, σ, ρ, hscope, hh, σ', h => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      simp only [execEnd] at h ⊢
      refine (TreuEnd.vor (treu_fragt σ (.inr (.inr g))) ?_) σ' h; intro σ' h
      rw [← fragt_haelt σ (.inr (.inr g))] at hh
      generalize σ.fragt (.inr (.inr g)) = σ at h hh ⊢
      by_cases hc : O.sichtbar g σ = true <;> simp only [hc, ite_true, ite_false, Bool.true_eq_false, Bool.false_eq_true] at h ⊢
      · have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ [.inr g]
        exact (TreuEnd.vor hl (end_treu bo hbV rest _ _ hscope_rest (hl.heldB hh))).schrumpf σ' h
      · simp only [EndAusgang.welt, reduceCtorEq] at h
  | .bindCallInd p args he hp hr rest, σ, ρ, hscope, hh, σ', h => by
      exact end_bindCallInd_treu O passes R hR hO bo hbV p args he hp hr rest (fun σ ρ hs hh => end_treu bo hbV rest σ ρ hs hh) σ ρ hscope hh σ' h
  | .bindCallIndElse p args he hp hr err rest, σ, ρ, hscope, hh, σ', h => by
      simp only [execEnd] at h
      have hscope_rest : rest.ScopesOk := by scopes_treu
      have hscope_err : err.ScopesOk := by scopes_treu
      exact indSonstE_treu R hR p args he hp hr σ _ ρ (treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (p.orte ++ args.orte))
        bo hbV hh
        _ _
        (fun s1 v hh1 => (end_treu bo hbV rest s1 _ hscope_rest hh1).schrumpf)
        (fun s1 r hh1 => (end_treu bo hbV err s1 _ hscope_err hh1).schrumpf) σ' h
  | .narrow e lo' hi' sonst rest, σ, ρ, hscope, hh, σ', h => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      have hscope_sonst : sonst.ScopesOk := by scopes_treu
      simp only [execEnd] at h ⊢
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
      by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi' <;> simp only [hc, dif_pos, dif_neg] at h ⊢
      · exact (TreuEnd.vor hl (end_treu bo hbV rest _ _ hscope_rest (hl.heldB hh))).schrumpf σ' h
      · exact (TreuEnd.vor hl (end_treu bo hbV sonst _ ρ hscope_sonst (hl.heldB hh))) σ' h
  | .exchange g neu hw hL rest, σ, ρ, hscope, hh, σ', h => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      simp only [execEnd] at h ⊢
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ (.inr g :: neu.orte)
      have g1 := hl.trans (treu_schreibGlob (W := V.schreibt) (G := V.gschreibt)
        (σ.lese Λ (.inr g :: neu.orte)) g Λ (eval (σ.lese Λ (.inr g :: neu.orte)) neu
          (σ.lese Λ (.inr g :: neu.orte)) (.cons ((σ.lese Λ (.inr g :: neu.orte)).globs g) ρ))
          hw)
      exact (TreuEnd.vor g1 (end_treu bo hbV rest _ _ hscope_rest (g1.heldB hh))).schrumpf σ' h
  | .ite c t e, σ, ρ, hscope, hh, σ', h => by
      have hscope_t : t.ScopesOk := by scopes_treu
      have hscope_e : e.ScopesOk := by scopes_treu
      simp only [execEnd] at h ⊢
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ c.orte
      by_cases hc : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true <;> simp only [hc, ite_true, ite_false, Bool.true_eq_false, Bool.false_eq_true] at h ⊢
      · exact (TreuEnd.vor hl (end_treu bo hbV t _ ρ hscope_t (hl.heldB hh))) σ' h
      · exact (TreuEnd.vor hl (end_treu bo hbV e _ ρ hscope_e (hl.heldB hh))) σ' h
  | .narrowRequired e lo' hi' rest, σ, ρ, hscope, hh, σ', h => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      simp only [execEnd] at h ⊢
      have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ e.orte
      by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi' <;> simp only [hc, dif_pos, dif_neg] at h ⊢
      · exact (TreuEnd.vor hl (end_treu bo hbV rest _ _ hscope_rest (hl.heldB hh))).schrumpf σ' h
      · simp only [dite_false, EndAusgang.welt, reduceCtorEq] at h

theorem arms_treu (bo : Option Int) (hbV : BodenUnter bo V.boden) :
    ∀ (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)) (σ : World D) (ρ : Env D Γ),
    arms.ScopesOk → HeldB bo Λ σ.haelt →
    TreuAusgang V.schreibt V.gschreibt σ (execArms O passes R arms v σ ρ)
  | .cons b _, ⟨⟨0, _⟩, _⟩, σ, _, hscope, hh, σ', h => by
      have hscope_b : b.ScopesOk := by scopes_treu
      exact (block_treu bo hbV b σ _ hscope_b hh).schrumpfArm _ σ' h
  | .cons _ rest, ⟨⟨_ + 1, _⟩, _⟩, σ, ρ, hscope, hh, σ', h => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      exact arms_treu bo hbV rest _ σ ρ hscope_rest hh σ' h

theorem grund_treu (bo : Option Int) (hbV : BodenUnter bo V.boden) :
    ∀ (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n) (σ : World D) (ρ : Env D Γ),
    arms.ScopesOk → HeldB bo Λ σ.haelt →
    TreuAusgang V.schreibt V.gschreibt σ (execGrund O passes R arms r σ ρ)
  | .cons b _, ⟨0, _⟩, σ, ρ, hscope, hh, σ', h => by
      have hscope_b : b.ScopesOk := by scopes_treu
      exact block_treu bo hbV b σ ρ hscope_b hh σ' h
  | .cons _ rest, ⟨_ + 1, _⟩, σ, ρ, hscope, hh, σ', h => by
      have hscope_rest : rest.ScopesOk := by scopes_treu
      exact grund_treu bo hbV rest _ σ ρ hscope_rest hh σ' h

end

end Rumpf

end Gabbro.Grammatik
