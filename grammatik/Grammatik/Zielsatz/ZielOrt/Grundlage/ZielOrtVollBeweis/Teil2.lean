module
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollBeweis.Teil2Basis
import all Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollBeweis.Teil2Basis

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollSem
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollBeweis.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-! ## 5. Leaves and axiom calls -/

/-- A statement is an axiom call. -/
def Stmt.istAxiom {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → Bool
  | .axiomCall .. => true
  | _ => false

/-- A leaf other than an axiom call consults neither the oracle nor the
    call handler. -/
theorem blatt_orakel (O O' : Orakel D) (passes : Nat)
    (R R' : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'} (hb : s.istBlatt = true)
    (ha : s.istAxiom = false) (σ : World D) (ρ : Env D Γ) :
    execStmt O passes R s σ ρ = execStmt O' passes R' s σ ρ := by
  cases s <;> first | rfl | (simp only [Stmt.istBlatt, Bool.false_eq_true] at hb; done) |
    (simp only [Stmt.istAxiom, Bool.true_eq_false] at ha; done)

/-- **Leaf locality, for any oracle and handler.** A leaf other than an
    axiom call, run at a world agreeing with the machine world on a
    footprint covering its carriers, ends where the machine's run ends (in
    environment, and in memory on the footprint), for every oracle and
    handler; its trace only grows. -/
theorem blatt_lokalV (P : Programm D) (O : Orakel D) (passes : Nat) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (hb : s.istBlatt = true)
    (ha : s.istAxiom = false) {S : List (D.Tab ⊕ D.Glob)} (hS : stmtOrteP P s ⊆ S)
    {σ W : World D} (hg : GleichAuf S σ W) {ρ : Env D Γ} {W' : World D} {ρ' : Env D Γ}
    (h : execStmt O passes keinRuf s W ρ = .ok W' ρ') :
    ∃ σ', (∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
        execStmt O' passes R s σ ρ = .ok σ' ρ') ∧ GleichAuf S σ' W' ∧
      σ.rang ≤ σ'.rang := by
  have hk : s.kOk = true := by
    cases s <;> first | rfl | (simp only [Stmt.istBlatt, Bool.false_eq_true] at hb; done) |
      (simp only [Stmt.istAxiom, Bool.true_eq_false] at ha; done) | (simp only [execStmt, reduceCtorEq] at h; done)
  obtain ⟨σ', h1, h2, h3⟩ := blatt_lokal P O passes s hk hb (fun o ho => hS ho) hg h
  exact ⟨σ', fun O' R => by rw [blatt_orakel O' O passes R keinRuf hb ha]; exact h1, h2, h3⟩

/-- What an `ok` run of an axiom call statement is. -/
theorem axiomCall_ok_inv {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (h : D.aerg a = none)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (σ : World D) (ρ : Env D Γ) (σ' : World D) (ρ' : Env D Γ)
    (hst : execStmt O passes R (Stmt.axiomCall (V := V) (l := l) a args h hw hg hd hgd) σ ρ =
      .ok σ' ρ') :
    σ' = (O.wirkt a ((σ.lese Λ args.orte).fragt (.inl a))
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).1 ∧ ρ' = ρ ∧
    ∃ u : ErgVal D (D.aerg a), einpassenErg O.zeiger (D.aerg a) (O.wirkt a ((σ.lese Λ args.orte).fragt (.inl a))
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).2 = some u := by
  simp only [execStmt, axiomAntwort] at hst
  split at hst
  · rename_i σx u hx
    cases hst
    simp only [Prod.mk.injEq] at hx
    exact ⟨hx.1.symm, rfl, u, hx.2⟩
  · cases hst

/-! ## 6. The steps of the replay that record an answer or pop -/

section Schritte2

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **An axiom step keeps the replay.** The answer of the machine's oracle
    (`xm`, in the axiom's frame around the machine's call world) is recorded
    at the sequential key, with the answer world `axWelt`: the declared
    carriers from the machine, the rest from the key world, a fresh trace
    position. -/
theorem fadenV_ax (e0 : Ereignis D) {z : RufFadenG D} {W : World D} (hF : FadenV P O passes z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    {l' : Bool} {Γ' : Ctx} {Λ' : List (Res D)} (ρ' : Env D Γ')
    (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (spur' : List (Ereignis D))
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
    (hok : r.okV P (fussOrte P z.kopf.f) → r'.okV P (fussOrte P z.kopf.f))
    (xm : World D × Int) (hxm : Rahmen (D.aschreibt a) (D.agschreibt a) (W.lese Λ args.orte) xm.1)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (σ : World D), ZeigerGleich O O' →
      O'.wirkt a ((σ.lese Λ args.orte).fragt (.inl a)) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
        (axWelt e0 a ((σ.lese Λ args.orte).fragt (.inl a)) xm.1, xm.2) →
      (semV O' passes R r σ ρ).folgt
        (semV O' passes R r' (axWelt e0 a ((σ.lese Λ args.orte).fragt (.inl a)) xm.1) ρ')) :
    FadenV P O passes
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩
      (xm.1.speicher.welt spur') := by
  obtain ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hka, hg, hok0, heq⟩, hS⟩ := hF
  have hok' : r.okV P (fussOrte P z.kopf.f) := by rw [hr] at hok0; exact hok0
  have hlen : σ.rang ≤ ((σ.lese Λ args.orte).fragt (.inl a)).rang :=
    Nat.le_trans (lese_laenge _ _ _) (World.rang_le_fragt _ _)
  refine ⟨⟨H, HA ++ [⟨a, (σ.lese Λ args.orte).fragt (.inl a),
      evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ,
      (axWelt e0 a ((σ.lese Λ args.orte).fragt (.inl a)) xm.1, xm.2)⟩],
    axWelt e0 a ((σ.lese Λ args.orte).fragt (.inl a)) xm.1, hreq, hf, hv,
    kurzV_mono hk (Nat.le_trans hlen (axWelt_rang_le _ _ _ _)),
    funkA_append hfa hka _ hlen (axWelt_spur _ _ _ _), ?_, ?_, ?_,
    hok hok', ?_⟩, hS⟩
  · intro a' σk ρk x hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hra a' σk ρk x hm
    · rw [List.mem_singleton] at hm
      cases hm
      exact axWelt_rahmen e0 a _ _
  · intro e hm
    rcases List.mem_append.mp hm with hm | hm
    · exact Nat.lt_of_lt_of_le (hka e hm) (Nat.le_trans hlen (axWelt_rang_le _ _ _ _))
    · rw [List.mem_singleton] at hm
      subst hm
      exact axWelt_rang_lt _ _ _ _
  · have h1 := axWelt_gleichAuf (κ := (σ.lese Λ args.orte).fragt (.inl a)) e0 a
      (hg.lese Λ Λ args.orte args.orte) hxm
    exact ⟨fun t ht => h1.1 t ht, fun g hg' => h1.2 g hg'⟩
  · intro R O' hR hA hz
    have h1 := heq R O' hR (passtA_append hA) hz
    rw [hr] at h1
    exact ZErg.folgt_trans h1 (hsem O' R σ hz (hA _ _ _ _ (List.mem_append_right _ List.mem_cons_self)))

/-- **A leaf step keeps the replay**: a non-axiom leaf by leaf locality, an
    axiom call by recording its answer (`fadenV_ax`). -/
theorem fadenV_blatt (e0 : Ereignis D) (hO : GutO O) {z : RufFadenG D} {W : World D}
    (hF : FadenV P O passes z W) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (s : Stmt D (vertragVon D z.kopf.f) l Γ Λ Λ') (K : GRest D (vertragVon D z.kopf.f) l Γ Λ')
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (σ : World D), semV O' passes R r σ ρ = weiterZ O' passes R K (execStmt O' passes R s σ ρ))
    (hok : r.okV P (fussOrte P z.kopf.f) →
      stmtOrteP P s ⊆ fussOrte P z.kopf.f ∧ K.okV P (fussOrte P z.kopf.f))
    (hleaf : s.istBlatt = true) (σ' : World D) (ρ' : Env D Γ)
    (hstep : execStmt O passes keinRuf s W ρ = .ok σ' ρ') :
    FadenV P O passes
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, Λ', ρ', K⟩⟩, σ'.spur, z.log⟩
      (σ'.speicher.welt σ'.spur) := by
  cases hax : s.istAxiom with
  | false =>
      refine fadenV_lokal hF hr ρ' K σ'.spur (fun σ hg hok' => ?_)
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
          refine fadenV_ax e0 hF hr ρ' K σ'.spur a args (fun h' => (hok h').2)
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

  What is proved: the user obligation `KoerperGutV` (the body triple for
  every oracle respecting the declared axiom frames, `RahmenO`); the
  records of call answers with reason answers (`EintragV`, `rufAusV` is a
  contract-respecting handler that never blames a caller) and of axiom
  answers (`AxEintrag`, `orakelAus` respects every declared frame under
  `GutO`); the recorded axiom answer world `axWelt` (inside the frame
  around the key, agreeing with the machine's answer on the footprint);
  the replay invariants `KopfV`/`WarteV`/`FortV`/`FadenV` and the steps
  that keep them: head-local (`fadenV_lokal`), memory outside the footprint
  (`fadenV_speicher`), return (`popV_ens`), call (`pushV_req`,
  `pushV_ok`), resume after a normal or reason answer (`popV_kopf`),
  axiom answer (`fadenV_ax`), leaf (`fadenV_blatt`).

  What is NOT here: the rule-by-rule step and the theorem
  (`ZielOrtVoll.lean`). The oracle's register and visibility answers
  (`regLies`, `sichtbar`) are not recorded: the fragment excludes the forms
  that consult them (see the CUTS of `ZielOrtVoll.lean` for why).
-/

#print axioms Gabbro.Grammatik.popV_kopf
#print axioms Gabbro.Grammatik.pushV_ok
#print axioms Gabbro.Grammatik.fadenV_blatt

end Gabbro.Grammatik
