module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollSem
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollBeweis.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Schritte
variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **The call leg.** -/
theorem pushV_req (hO : GutO O) (hK : ∀ f, KoerperGutV P passes f) {F : RufRahmenG D}
    {H : List (EintragV D)} {HA : List (AxEintrag D)} {σ : World D}
    (hreq : ReqAmEintritt P F.f F.s0 F.rho) (hf : FunkV H) (hv : VertraegeOkV P H)
    (hfa : FunkA HA) (hra : RahmenA HA)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    (r : GRest D (vertragVon D F.f) l Γ Λ)
    (heq : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D),
      PasstV R H → PasstA O' HA → ZeigerGleich O O' →
      (zErg (execEnd (V := vertragVon D F.f) O' passes R (P.rumpf F.f) F.s0 F.rho)).folgt
        (semV O' passes R r σ ρ))
    (g : D.Fn) (κ : World D) (ρk : Env D (D.params g))
    (hlogik : ∀ (O' : Orakel D) R (e : Logik D), R g κ ρk = .logik e →
      semV O' passes R r σ ρ = .logik e) :
    ReqAmEintritt P g κ ρk := by
  cases hq : wahr? (eval κ (P.requires g) κ ρk) with
  | true => exact hq
  | false =>
      exfalso
      have htor : torRuf P (rufAusV H) g κ ρk = .logik (.vorbedingung g) := by
        simp only [torRuf, hq]
        rfl
      have h1 := heq _ (orakelAus O HA) (torRuf_passtV (rufAusV_passt hf) hv)
        (orakelAus_passt O hfa) rfl
      rw [hlogik _ _ _ htor] at h1
      have hex := zErg_gleich_logik (ZErg.folgt_logik h1)
      exact (hK F.f (orakelAus O HA) (orakelAus_rahmen hO hra) (rufAusV H)
        (rufAusV_respektiert hv) (rufAusV_ohneVorbedingung hv) F.s0 F.rho hreq).2 g hex

/-- **The caller resumes** after its pending call to `G` was answered by
    `mk` (a normal answer, whose `ensures` holds at the machine's return
    world `s1`, or a reason): the answer is recorded at the pending key with
    the machine's memory and a fresh trace position, and the frame becomes a
    replayed head with the continuation `r'` chosen by the pop. -/
theorem popV_kopf (e0 : Ereignis D) {F : RufRahmenG D}
    {G : Σ f : D.Fn, Env D (D.params f) × World D}
    (hW : WarteV P O passes F G) (s1 : World D) (mk : World D → RufAusgang G.1)
    (hmk : (∃ v, (∀ σa, mk σa = .ok σa v) ∧ EnsAmRueck P G.1 G.2.2 s1 G.2.1 v) ∨
      (∃ r, ∀ σa, mk σa = .why σa r))
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ' : Env D Γ) (r' : GRest D (vertragVon D F.f) l Γ Λ)
    (hok' : F.rest.2.2.2.2.okV P (fussOrte P F.f) → r'.okV P (fussOrte P F.f))
    (hwahl : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
      (σa : World D) (X : ZErg (vertragVon D F.f)),
      FortV passes F G.1 X R O' (mk σa) → X.folgt (semV O' passes R r' σa ρ'))
    (W' : World D) (hW' : W'.slots = s1.slots ∧ W'.globs = s1.globs) :
    KopfV P O passes ⟨F.f, F.rho, F.s0, ⟨l, Γ, Λ, ρ', r'⟩⟩ W' := by
  obtain ⟨H, HA, κ, hreq, hf, hv, hk, hfa, hra, hka, hok, hreqκ, hglκ, hcont⟩ := hW
  have hmem : (⟨G.1, κ, G.2.1, mk (antwortWelt e0 s1 κ)⟩ : EintragV D) ∈
      H ++ [⟨G.1, κ, G.2.1, mk (antwortWelt e0 s1 κ)⟩] :=
    List.mem_append_right _ List.mem_cons_self
  refine ⟨H ++ [⟨G.1, κ, G.2.1, mk (antwortWelt e0 s1 κ)⟩], HA, antwortWelt e0 s1 κ, hreq,
    funkV_append hf hk _ (Nat.le_refl _), ?_, ?_, hfa, hra,
    kurzA_mono hka (Nat.le_succ _), ?_, hok' hok, ?_⟩
  · intro g σ ρ a hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hv g σ ρ a hm
    · rw [List.mem_singleton] at hm
      cases hm
      refine ⟨hreqκ, ?_, ?_⟩
      · intro σa w hw
        rcases hmk with ⟨v, hv', hens⟩ | ⟨rr, hr'⟩
        · rw [hv'] at hw
          cases hw
          refine ens_transfer hens ?_ ?_
          · exact GleichAuf.mono (fun _ h => List.mem_append_right _ h) hglκ.symm
          · exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
        · rw [hr'] at hw
          cases hw
      · intro e he
        rcases hmk with ⟨v, hv', _⟩ | ⟨rr, hr'⟩
        · rw [hv'] at he; cases he
        · rw [hr'] at he; cases he
  · intro e hm
    rcases List.mem_append.mp hm with hm | hm
    · exact Nat.lt_succ_of_lt (hk e hm)
    · rw [List.mem_singleton] at hm
      subst hm
      exact Nat.lt_succ_self _
  · exact ⟨fun t _ => congrFun hW'.1.symm t, fun g _ => congrFun hW'.2.symm g⟩
  · intro R O' hR hA hz
    have hans := hR _ _ _ _ hmem
    have hc := hcont R O' (passtV_append hR) hA hz
    rw [hans] at hc
    exact hwahl R O' _ _ hc

/-- **A push keeps the replay.** The head frame calls `g` with `args`; it
    becomes a suspended frame with the continuation `rc`, and the callee's
    frame becomes a fresh replayed head. The callee's `requires` holds at
    the machine's entry world (`pushV_req`), for the log. -/
theorem pushV_ok (hO : GutO O) (hK : ∀ f, KoerperGutV P passes f)
    (hFrag : ∀ f, (P.rumpf f).vOk (kandP P (fussOrte P f)) = true)
    {z : RufFadenG D} {W : World D} (hF : FadenV P O passes z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (g : D.Fn) (args : Args D Γ Λ (D.params g))
    (hS : r.okV P (fussOrte P z.kopf.f) → args.orte ⊆ fussOrte P z.kopf.f ∧
      (P.requires g).orte ++ (P.ensures g).orte ⊆ fussOrte P z.kopf.f)
    {lc : Bool} {Γc : Ctx} {Λc : List (Res D)} (ρc : Env D Γc)
    (rc : GRest D (vertragVon D z.kopf.f) lc Γc Λc)
    (hrc : r.okV P (fussOrte P z.kopf.f) → rc.okV P (fussOrte P z.kopf.f))
    (hlogik : ∀ (O' : Orakel D) R σ (e : Logik D),
      R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
        .logik e → semV O' passes R r σ ρ = .logik e)
    (hweiter : ∀ (O' : Orakel D) R σ,
      FortV passes ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩ g
        (semV O' passes R r σ ρ) R O'
        (R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ))) :
    FadenV P O passes
      ⟨⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩ :: z.stapel,
        ⟨g, evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ, W.lese Λ args.orte,
          ⟨false, D.params g, Signatur.anfang D (D.signatur g),
            evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ, .ende (P.rumpf g)⟩⟩,
        (W.lese Λ args.orte).spur,
        RufEreignisF.eintritt g (evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ)
          (W.lese Λ args.orte) :: z.log⟩
      (W.lese Λ args.orte) ∧
    ReqAmEintritt P g (W.lese Λ args.orte)
      (evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ) := by
  obtain ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hka, hg, hok, heq⟩, hSt⟩ := hF
  have hok' : r.okV P (fussOrte P z.kopf.f) := by rw [hr] at hok; exact hok
  have heq' : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D),
      PasstV R H → PasstA O' HA → ZeigerGleich O O' →
      (zErg (execEnd (V := vertragVon D z.kopf.f) O' passes R (P.rumpf z.kopf.f) z.kopf.s0
        z.kopf.rho)).folgt (semV O' passes R r σ ρ) := by
    intro R O' hR hA hz
    have := heq R O' hR hA hz
    rw [hr] at this
    exact this
  obtain ⟨hargs, hctr⟩ := hS hok'
  have hgκ : GleichAuf (fussOrte P z.kopf.f) (σ.lese Λ args.orte) (W.lese Λ args.orte) :=
    hg.lese Λ Λ args.orte args.orte
  have hρk : evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ =
      evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ :=
    evalArgs_gleichAuf args (fun _ h => hargs h) hgκ ρ
  have hreqκ := pushV_req hO hK hreq hf hv hfa hra r heq' g (σ.lese Λ args.orte)
    (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
    (fun O' R e h => hlogik O' R σ e h)
  rw [hρk] at hreqκ
  have hctrκ : GleichAuf ((P.requires g).orte ++ (P.ensures g).orte) (σ.lese Λ args.orte)
      (W.lese Λ args.orte) := GleichAuf.mono (fun _ h => hctr h) hgκ
  have hreq0 := req_transfer hreqκ
    (GleichAuf.mono (fun _ h => List.mem_append_left _ h) hctrκ)
  refine ⟨⟨⟨[], [], W.lese Λ args.orte, hreq0, funkV_nil, vertraegeOkV_nil P, kurzV_nil _,
    funkA_nil, rahmenA_nil, kurzA_nil _,
    GleichAuf.refl _ _, ⟨hFrag g, fuss_rumpf P g⟩, fun R O' _ _ _ => ZErg.folgt_refl _⟩,
    ⟨H, HA, σ.lese Λ args.orte, hreq, hf, hv, kurzV_mono hk (lese_laenge _ _ _), hfa, hra,
      kurzA_mono hka (lese_laenge _ _ _), hrc hok', hreqκ, hctrκ, ?_⟩, hSt⟩, hreq0⟩
  intro R O' hR hA hz
  have hw := hweiter O' R σ
  rw [hρk] at hw
  exact fortV_mono (F := ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩)
    (heq' R O' hR hA hz) hw

/-- **A push through a read set `os` and a parameter function `rhoF`** --
    the shape of an indirect call, whose callee `g` the pointer read at the
    key names (the sequential side only needs it at worlds agreeing with the
    machine world on the footprint, `hlogik`, `hweiter`). -/
theorem pushV_gen (hO : GutO O) (hK : ∀ f, KoerperGutV P passes f)
    (hFrag : ∀ f, (P.rumpf f).vOk (kandP P (fussOrte P f)) = true)
    {z : RufFadenG D} {W : World D} (hF : FadenV P O passes z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (os : List (D.Tab ⊕ D.Glob)) (g : D.Fn) (rhoF : World D → Env D (D.params g))
    (hS : r.okV P (fussOrte P z.kopf.f) →
      (P.requires g).orte ++ (P.ensures g).orte ⊆ fussOrte P z.kopf.f)
    (hrho : r.okV P (fussOrte P z.kopf.f) → ∀ σ : World D,
      GleichAuf (fussOrte P z.kopf.f) σ W → rhoF (σ.lese Λ os) = rhoF (W.lese Λ os))
    {lc : Bool} {Γc : Ctx} {Λc : List (Res D)} (ρc : Env D Γc)
    (rc : GRest D (vertragVon D z.kopf.f) lc Γc Λc)
    (hrc : r.okV P (fussOrte P z.kopf.f) → rc.okV P (fussOrte P z.kopf.f))
    (hlogik : ∀ (O' : Orakel D) R σ (e : Logik D), GleichAuf (fussOrte P z.kopf.f) σ W →
      R g (σ.lese Λ os) (rhoF (σ.lese Λ os)) = .logik e → semV O' passes R r σ ρ = .logik e)
    (hweiter : ∀ (O' : Orakel D) R σ, GleichAuf (fussOrte P z.kopf.f) σ W →
      FortV passes ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩ g
        (semV O' passes R r σ ρ) R O' (R g (σ.lese Λ os) (rhoF (σ.lese Λ os)))) :
    FadenV P O passes
      ⟨⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩ :: z.stapel,
        ⟨g, rhoF (W.lese Λ os), W.lese Λ os,
          ⟨false, D.params g, Signatur.anfang D (D.signatur g), rhoF (W.lese Λ os),
            .ende (P.rumpf g)⟩⟩,
        (W.lese Λ os).spur,
        RufEreignisF.eintritt g (rhoF (W.lese Λ os)) (W.lese Λ os) :: z.log⟩
      (W.lese Λ os) ∧
    ReqAmEintritt P g (W.lese Λ os) (rhoF (W.lese Λ os)) := by
  obtain ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hka, hg, hok, heq⟩, hSt⟩ := hF
  have hok' : r.okV P (fussOrte P z.kopf.f) := by rw [hr] at hok; exact hok
  have heq' : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D),
      PasstV R H → PasstA O' HA → ZeigerGleich O O' →
      (zErg (execEnd (V := vertragVon D z.kopf.f) O' passes R (P.rumpf z.kopf.f) z.kopf.s0
        z.kopf.rho)).folgt (semV O' passes R r σ ρ) := by
    intro R O' hR hA hz
    have := heq R O' hR hA hz
    rw [hr] at this
    exact this
  have hctr := hS hok'
  have hgκ : GleichAuf (fussOrte P z.kopf.f) (σ.lese Λ os) (W.lese Λ os) := hg.lese Λ Λ os os
  have hρk : rhoF (σ.lese Λ os) = rhoF (W.lese Λ os) := hrho hok' σ hg
  have hreqκ := pushV_req hO hK hreq hf hv hfa hra r heq' g (σ.lese Λ os) (rhoF (σ.lese Λ os))
    (fun O' R e h => hlogik O' R σ e hg h)
  rw [hρk] at hreqκ
  have hctrκ : GleichAuf ((P.requires g).orte ++ (P.ensures g).orte) (σ.lese Λ os)
      (W.lese Λ os) := GleichAuf.mono (fun _ h => hctr h) hgκ
  have hreq0 := req_transfer hreqκ
    (GleichAuf.mono (fun _ h => List.mem_append_left _ h) hctrκ)
  refine ⟨⟨⟨[], [], W.lese Λ os, hreq0, funkV_nil, vertraegeOkV_nil P, kurzV_nil _,
    funkA_nil, rahmenA_nil, kurzA_nil _,
    GleichAuf.refl _ _, ⟨hFrag g, fuss_rumpf P g⟩, fun R O' _ _ _ => ZErg.folgt_refl _⟩,
    ⟨H, HA, σ.lese Λ os, hreq, hf, hv, kurzV_mono hk (lese_laenge _ _ _), hfa, hra,
      kurzA_mono hka (lese_laenge _ _ _), hrc hok', hreqκ, hctrκ, ?_⟩, hSt⟩, hreq0⟩
  intro R O' hR hA hz
  have hw := hweiter O' R σ hg
  rw [hρk] at hw
  exact fortV_mono (F := ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩)
    (heq' R O' hR hA hz) hw

end Schritte

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
      σ.spur.length ≤ σ'.spur.length := by
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
  have hlen : σ.spur.length ≤ ((σ.lese Λ args.orte).fragt (.inl a)).spur.length :=
    Nat.le_trans (lese_laenge _ _ _) (Nat.le_succ _)
  refine ⟨⟨H, HA ++ [⟨a, (σ.lese Λ args.orte).fragt (.inl a),
      evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ,
      (axWelt e0 a ((σ.lese Λ args.orte).fragt (.inl a)) xm.1, xm.2)⟩],
    axWelt e0 a ((σ.lese Λ args.orte).fragt (.inl a)) xm.1, hreq, hf, hv,
    kurzV_mono hk (Nat.le_trans hlen (Nat.le_succ _)), funkA_append hfa hka _ hlen, ?_, ?_, ?_,
    hok hok', ?_⟩, hS⟩
  · intro a' σk ρk x hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hra a' σk ρk x hm
    · rw [List.mem_singleton] at hm
      cases hm
      exact axWelt_rahmen e0 a _ _
  · intro e hm
    rcases List.mem_append.mp hm with hm | hm
    · exact Nat.lt_of_lt_of_le (hka e hm) (Nat.le_trans hlen (Nat.le_succ _))
    · rw [List.mem_singleton] at hm
      subst hm
      exact Nat.lt_succ_self _
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
