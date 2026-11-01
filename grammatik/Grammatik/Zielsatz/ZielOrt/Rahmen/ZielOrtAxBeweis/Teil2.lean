module

public import Grammatik.Logik.Vertraege.AxiomVertrag
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtAxBeweis.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Schritte2
variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D}

/-- **A leaf step keeps the replay**: a non-axiom leaf by leaf locality, an
    axiom call by recording its answer (`fadenA_ax`). -/
theorem fadenA_blatt (e0 : Ereignis D) (hO : GutO O) (hQ : AxVertragO Q O)
    (hlok : AxEnsLokal Q) {z : RufFadenG D} {W : World D}
    (hF : FadenA P O passes Q z W) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (s : Stmt D (vertragVon D z.kopf.f) l Γ Λ Λ') (K : GRest D (vertragVon D z.kopf.f) l Γ Λ')
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (σ : World D), semV O' passes R r σ ρ = weiterZ O' passes R K (execStmt O' passes R s σ ρ))
    (hok : r.okV P (fussOrte P z.kopf.f) →
      stmtOrteP P s ⊆ fussOrte P z.kopf.f ∧ K.okV P (fussOrte P z.kopf.f))
    (hleaf : s.istBlatt = true) (σ' : World D) (ρ' : Env D Γ)
    (hstep : execStmt O passes keinRuf s W ρ = .ok σ' ρ') :
    FadenA P O passes Q
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, Λ', ρ', K⟩⟩, σ'.spur, z.log⟩
      (σ'.speicher.welt σ'.spur) := by
  cases hax : s.istAxiom with
  | false =>
      refine fadenA_lokal hF hr ρ' K σ'.spur (fun σ hg hok' => ?_)
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
          refine fadenA_ax e0 hF hr ρ' K σ'.spur a args (fun h' => (hok h').2)
            (σ', (O.wirkt a ((W.lese Λ args.orte).fragt (.inl a))
              (evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ')).2) hfr hlok
            (fun v hv => by
              rw [e1]
              exact hQ a _ _ v hv) ?_
          intro O' R σ hz hw
          rw [hsem]
          apply ZErg.folgt_of_eq
          simp only [execStmt, axiomAntwort, hw]
          simp only [(show O'.zeiger = O.zeiger from hz), hu]
          rfl
      | _ => simp only [Stmt.istAxiom, Bool.false_eq_true] at hax

end Schritte2

/-! ## CUTS:

  What is proved: the replay invariants with the declared-ensures record
  conjunct (`KopfA`/`WarteA`/`FadenA`/`ZielInvA`) and every step lemma of
  `ZielOrtVollBeweis.lean` for them (`fadenA_lokal`, `fadenA_speicher`,
  `popA_ens`, `pushA_req`, `popA_kopf`, `pushA_ok`, `pushA_gen`,
  `fadenA_ax`, `fadenA_blatt`); the obligation `KoerperGutA` is applied to
  the record oracle through `orakelAus_vertrag`.

  What is NOT here: the rule-by-rule step and the theorem (`ZielOrtAx.lean`).
-/

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.fadenA_ax
#print axioms Gabbro.Grammatik.pushA_ok
