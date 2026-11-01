module

public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmenSem
public import Grammatik.Logik.Vertraege.AxiomVertrag
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmenBeweis.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

section Schritte2

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D}

/-- **An axiom step keeps the replay.** The answer of the machine's oracle
    (`xm`, in the axiom's frame around the machine's call world) is recorded
    at the sequential key, with the answer world `axWelt`: the declared
    carriers from the machine, the rest from the key world, a fresh trace
    position. -/
theorem fadenR_ax (e0 : Ereignis D) {z : RufFadenG D} {W : World D} (hF : FadenR P O passes Q z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    {l' : Bool} {Γ' : Ctx} {Λ' : List (Res D)} (ρ' : Env D Γ')
    (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (spur' : List (Ereignis D))
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
    (hok : r.okG P (fussOrteG P z.kopf.f) → r'.okG P (fussOrteG P z.kopf.f))
    (xm : World D × Int) (hxm : Rahmen (D.aschreibt a) (D.agschreibt a) (W.lese Λ args.orte) xm.1)
    (hlok : AxEnsLokal Q)
    (hxq : ∀ v : ErgVal D (D.aerg a), einpassenErg O.zeiger (D.aerg a) xm.2 = some v → Q a xm.1 v = true)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (σ : World D), ZeigerGleich O O' →
      O'.wirkt a ((σ.lese Λ args.orte).fragt (.inl a)) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
        (axWelt e0 a ((σ.lese Λ args.orte).fragt (.inl a)) xm.1, xm.2) →
      (semV O' passes R r σ ρ).folgt
        (semV O' passes R r' (axWelt e0 a ((σ.lese Λ args.orte).fragt (.inl a)) xm.1) ρ')) :
    FadenR P O passes Q
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩
      (xm.1.speicher.welt spur') := by
  obtain ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hg, hok0, heq⟩, hS⟩ := hF
  have hok' : r.okG P (fussOrteG P z.kopf.f) := by rw [hr] at hok0; exact hok0
  have hlen : σ.spur.length ≤ ((σ.lese Λ args.orte).fragt (.inl a)).spur.length :=
    Nat.le_trans (lese_laenge _ _ _) (Nat.le_succ _)
  refine ⟨⟨H, HA ++ [⟨a, (σ.lese Λ args.orte).fragt (.inl a),
      evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ,
      (axWelt e0 a ((σ.lese Λ args.orte).fragt (.inl a)) xm.1, xm.2)⟩],
    axWelt e0 a ((σ.lese Λ args.orte).fragt (.inl a)) xm.1, hreq, hf, hv,
    kurzV_mono hk (Nat.le_trans hlen (Nat.le_succ _)), funkA_append hfa hka _ hlen, ?_, ?_, ?_,
    ?_, hok hok', ?_⟩, hS⟩
  · intro a' σk ρk x hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hra a' σk ρk x hm
    · rw [List.mem_singleton] at hm
      cases hm
      exact axWelt_rahmen e0 a _ _
  · intro a' σk ρk x hm v hv
    rcases List.mem_append.mp hm with hm | hm
    · exact hqa a' σk ρk x hm v hv
    · rw [List.mem_singleton] at hm
      cases hm
      exact axWelt_vertrag hlok e0 a _ _ v (hxq v hv)
  · intro e hm
    rcases List.mem_append.mp hm with hm | hm
    · exact Nat.lt_of_lt_of_le (hka e hm) (Nat.le_trans hlen (Nat.le_succ _))
    · rw [List.mem_singleton] at hm
      subst hm
      exact Nat.lt_succ_self _
  · have h1 := axWelt_gleichAuf (κ := (σ.lese Λ args.orte).fragt (.inl a)) e0 a
      (hg.lese Λ Λ args.orte args.orte) hxm
    exact ⟨fun t ht => h1.1 t ht, fun g hg' => h1.2 g hg'⟩
  · intro R O' hR hA hQ
    have h1 := heq R O' hR (passtA_append hA) hQ
    rw [hr] at h1
    exact ZErg.folgt_trans h1 (hsem O' R σ hQ.2.2 (hA _ _ _ _ (List.mem_append_right _ List.mem_cons_self)))

/-- **A leaf step keeps the replay**: a non-axiom leaf by leaf locality, an
    axiom call by recording its answer (`fadenR_ax`). -/
theorem fadenR_blatt (e0 : Ereignis D) (hO : GutO O) (hQ : AxVertragO Q O)
    (hlok : AxEnsLokal Q) {z : RufFadenG D} {W : World D}
    (hF : FadenR P O passes Q z W) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (s : Stmt D (vertragVon D z.kopf.f) l Γ Λ Λ') (K : GRest D (vertragVon D z.kopf.f) l Γ Λ')
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (σ : World D), semV O' passes R r σ ρ = weiterZ O' passes R K (execStmt O' passes R s σ ρ))
    (hok : r.okG P (fussOrteG P z.kopf.f) →
      stmtOrteP P s ⊆ fussOrteG P z.kopf.f ∧ K.okG P (fussOrteG P z.kopf.f))
    (hleaf : s.istBlatt = true) (σ' : World D) (ρ' : Env D Γ)
    (hstep : execStmt O passes keinRuf s W ρ = .ok σ' ρ') :
    FadenR P O passes Q
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, Λ', ρ', K⟩⟩, σ'.spur, z.log⟩
      (σ'.speicher.welt σ'.spur) := by
  cases hax : s.istAxiom with
  | false =>
      refine fadenR_lokal hF hr ρ' K σ'.spur (fun σ hg hok' => ?_)
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
          refine fadenR_ax e0 hF hr ρ' K σ'.spur a args (fun h' => (hok h').2)
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

  What is proved: the replay invariants against frame-respecting handlers
  (`KopfR`, `WarteR`, `StapelR`, `FadenR`, `ZielInvR`) and the steps that
  keep them, as in `ZielOrtGeraetBeweis.lean`: head-local (`fadenR_lokalQ`,
  `fadenR_lokal`), memory outside the widened footprint (`fadenR_speicher`),
  return (`popR_ens`), call (`pushR_req`, `pushR_ok`, `pushR_gen`), resume
  with the frame-shaped answer world (`popR_kopf`), axiom answer
  (`fadenR_ax`), leaf (`fadenR_blatt`). The user obligation `KoerperGutR`
  enters where the record handler meets it (`popR_ens`, `pushR_req`); the
  machine's frame fact enters where a call answer is recorded
  (`popR_kopf`, premise `hRah`).

  What is NOT here: the rule-by-rule step and the theorem
  (`ZielOrtRahmen.lean`).
-/

#print axioms Gabbro.Grammatik.popR_kopf
#print axioms Gabbro.Grammatik.pushR_ok
#print axioms Gabbro.Grammatik.fadenR_blatt

end Gabbro.Grammatik
