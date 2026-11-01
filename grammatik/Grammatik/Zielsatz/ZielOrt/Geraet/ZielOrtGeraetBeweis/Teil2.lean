module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetSem
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetBeweis.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Schritte2
variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **A leaf step keeps the replay**: a non-axiom leaf by leaf locality, an
    axiom call by recording its answer (`fadenG_ax`). -/
theorem fadenG_blatt (e0 : Ereignis D) (hO : GutO O) {z : RufFadenG D} {W : World D}
    (hF : FadenG P O passes z W) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (s : Stmt D (vertragVon D z.kopf.f) l Γ Λ Λ') (K : GRest D (vertragVon D z.kopf.f) l Γ Λ')
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (σ : World D), semV O' passes R r σ ρ = weiterZ O' passes R K (execStmt O' passes R s σ ρ))
    (hok : r.okG P (fussOrteG P z.kopf.f) →
      stmtOrteP P s ⊆ fussOrteG P z.kopf.f ∧ K.okG P (fussOrteG P z.kopf.f))
    (hleaf : s.istBlatt = true) (σ' : World D) (ρ' : Env D Γ)
    (hstep : execStmt O passes keinRuf s W ρ = .ok σ' ρ') :
    FadenG P O passes
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, Λ', ρ', K⟩⟩, σ'.spur, z.log⟩
      (σ'.speicher.welt σ'.spur) := by
  cases hax : s.istAxiom with
  | false =>
      refine fadenG_lokal hF hr ρ' K σ'.spur (fun σ hg hok' => ?_)
      obtain ⟨hs, hK⟩ := hok hok'
      obtain ⟨σs, hes, hgs, hls⟩ := blatt_lokalV P O passes s hleaf hax hs hg hstep
      refine ⟨σs, hls, ⟨fun t ht => hgs.1 t ht, fun g hg' => hgs.2 g hg'⟩, hK, fun R O' => ?_⟩
      rw [hsem, hes]
      exact ZErg.folgt_refl _
  | true =>
      cases s with
      | axiomCall a args h hw hg hd hgd =>
          obtain ⟨e1, e2, u, hu⟩ := axiomCall_ok_inv O passes keinRuf a args h hw hg hd hgd W ρ σ' ρ'
            hstep
          subst e2
          have hfr := (hO a ((W.lese Λ args.orte).fragt (.inl a))
            (evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ')).1
          rw [← e1] at hfr
          refine fadenG_ax e0 hF hr ρ' K σ'.spur a args (fun h' => (hok h').2)
            (σ', (O.wirkt a ((W.lese Λ args.orte).fragt (.inl a))
              (evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ')).2) hfr ?_
          intro O' R σ hz hw
          rw [hsem]
          apply ZErg.folgt_of_eq
          simp only [execStmt, axiomAntwort, hw]
          simp only [(show O'.zeiger = O.zeiger from hz), hu]
          rfl
      | _ => simp only [Stmt.istAxiom, Bool.false_eq_true] at hax

end Schritte2

/-! ## CUTS:

  What is proved: the replay invariants over the sequential oracles with the
  machine's register and visibility answers (`KopfG`, `WarteG`, `StapelG`,
  `FadenG`, `ZielInvG`) and the steps that keep them, exactly as in
  `ZielOrtVollBeweis.lean`: head-local (`fadenG_lokalQ`, `fadenG_lokal`),
  memory outside the widened footprint (`fadenG_speicher`), return
  (`popG_ens`), call (`pushG_req`, `pushG_ok`, `pushG_gen`), resume
  (`popG_kopf`), axiom answer (`fadenG_ax`), leaf (`fadenG_blatt`). The
  hardware premise `RegLokal O` enters where the record oracle meets the
  user obligation (`popG_ens`, `pushG_req`).

  What is NOT here: the rule-by-rule step and the theorem
  (`ZielOrtGeraet.lean`).
-/

#print axioms Gabbro.Grammatik.popG_kopf
#print axioms Gabbro.Grammatik.pushG_ok
#print axioms Gabbro.Grammatik.fadenG_blatt

end Gabbro.Grammatik
