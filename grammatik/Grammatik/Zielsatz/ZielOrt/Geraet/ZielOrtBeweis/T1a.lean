/-
  File:      Grammatik/ZielOrtBeweis.lean
  Subject:   `ziel_ort` -- contracts hold at their place on every machine of
             the repaired concurrent call machine G, from the user's
             sequential obligations, the hardware assumption and decidable
             program facts.

  The proof is a REPLAY. Every frame of every thread carries a sequential
  run of its function's body, started at the frame's entry world:

  * the sequential world `σ` of the head frame agrees with the machine
    world on the frame's footprint (`GleichAuf (fussOrte P f) σ W`): the
    frame's own steps are sequential steps at `σ` (leaf locality, the
    residue step lemmas of `ZielOrtSem.lean`), and steps of OTHER threads
    never touch the footprint (the rely: every footprint carrier is guarded
    by a signature lock the frame holds for its whole life
    (`rufG_haelt_signatur`), exclusive across threads (`exklusivG`), or
    written by no function);
  * the calls the frame made are RECORDED with the machine's answers
    (`Eintrag`), each answer at a fresh trace position of the sequential
    world, so the record is a function of the call key and defines a
    contract-respecting handler (`rufAus`); the sequential run of the body
    with ANY handler that repeats the record reaches the frame's current
    residue (`KopfOk`), a suspended frame the pending call (`WarteOk`);
  * at a return, `KoerperGut` (the body triple) gives `ensures` in the
    sequential world, hence in the machine's (agreement on the footprint,
    which contains the `ensures` carriers); at a call, `KoerperGut`'s gated
    conjunct (no failed `requires`) gives the callee's `requires` in the
    sequential world, hence in the machine's (the callee's contract carriers
    are in the caller's footprint).
-/
module
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.T1
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtSem
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}
theorem logOk_eintritt {P : Programm D} {log : List (RufEreignisF D)} (h : LogOk P log)
    {g : D.Fn} {rho : Env D (D.params g)} {s0 : World D} (hr : ReqAmEintritt P g s0 rho) :
    LogOk P (RufEreignisF.eintritt g rho s0 :: log) := by
  intro ev hev
  rcases List.mem_cons.mp hev with rfl | hev
  · refine ⟨fun g' rho' s0' he => ?_, fun _ _ _ _ _ he => by cases he⟩
    cases he
    exact hr
  · exact h ev hev

theorem logOk_rueck {P : Programm D} {log : List (RufEreignisF D)} (h : LogOk P log)
    {g : D.Fn} {rho : Env D (D.params g)} {v : ErgVal D (D.erg g)} {s0 s1 : World D}
    (he : EnsAmRueck P g s0 s1 rho v) :
    LogOk P (RufEreignisF.rueck g rho v s0 s1 :: log) := by
  intro ev hev
  rcases List.mem_cons.mp hev with rfl | hev
  · refine ⟨fun _ _ _ h' => (by cases h'), fun g' rho' v' s0' s1' h' => ?_⟩
    cases h'
    exact he
  · exact h ev hev

section Hilfen

variable {P : Programm D} {O : Orakel D} {passes : Nat}

theorem kopf_okZ {F : RufRahmenG D} {W : World D} (h : KopfOk P O passes F W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D F.f) l Γ Λ} (hr : F.rest = ⟨l, Γ, Λ, ρ, r⟩) :
    r.okZ P (fussOrte P F.f) := by
  obtain ⟨_, _, _, _, _, _, _, hok, _⟩ := h
  -- Transport the whole packet; its projections have dependent indices.
  exact (congrArg (fun c : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D),
    Env D Γ × GRest D (vertragVon D F.f) l Γ Λ =>
      c.2.2.2.2.okZ P (fussOrte P F.f)) hr).mp hok

/-- **A head-local step** keeps the replay: the stack and the key are
    kept, the residue moves by a sequential step at the sequential world. -/
theorem fadenOk_lokal {z : RufFadenG D} {W W' : World D} (hF : FadenOk P O passes z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    {l' : Bool} {Γ' : Ctx} {Λ' : List (Res D)} (ρ' : Env D Γ')
    (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (spur' : List (Ereignis D))
    (hstep : ∀ σ : World D, GleichAuf (fussOrte P z.kopf.f) σ W →
      r.okZ P (fussOrte P z.kopf.f) →
      ∃ σ', σ.spur.length ≤ σ'.spur.length ∧ GleichAuf (fussOrte P z.kopf.f) σ' W' ∧
        r'.okZ P (fussOrte P z.kopf.f) ∧
        ∀ R, (semZ O passes R r' σ' ρ').gleich (semZ O passes R r σ ρ)) :
    FadenOk P O passes
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩ W' := by
  have hok' := kopf_okZ hF.1 hr
  obtain ⟨⟨H, σ, hreq, hf, hv, hk, hg, _, heq⟩, hS⟩ := hF
  have heq' : ∀ R, Passt R H →
      (zErg (execEnd (V := vertragVon D z.kopf.f) O passes R (P.rumpf z.kopf.f) z.kopf.s0
        z.kopf.rho)).gleich (semZ O passes R r σ ρ) := by
    intro R hR
    exact ZErg.gleich_trans (heq R hR) (ZErg.gleich_of_eq
      (congrArg (fun c : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D),
        Env D Γ × GRest D (vertragVon D z.kopf.f) l Γ Λ =>
          semZ O passes R c.2.2.2.2 σ c.2.2.2.1) hr))
  obtain ⟨σ', hl, hg', hok'', hsem⟩ := hstep σ hg hok'
  exact ⟨⟨H, σ', hreq, hf, hv, kurzH_mono hk hl, hg', hok'',
    fun R hR => ZErg.gleich_trans (heq' R hR) (ZErg.gleich_symm (hsem R))⟩, hS⟩

/-- Memory moved outside the head's footprint keeps the replay. -/
theorem fadenOk_speicher {z : RufFadenG D} {W W' : World D} (hF : FadenOk P O passes z W)
    (hw : ∀ c ∈ fussOrte P z.kopf.f, TraegerGleich W'.speicher W.speicher c) :
    FadenOk P O passes z W' := by
  obtain ⟨⟨H, σ, hreq, hf, hv, hk, hg, hok, heq⟩, hS⟩ := hF
  refine ⟨⟨H, σ, hreq, hf, hv, hk, ⟨fun t ht => ?_, fun g hg' => ?_⟩, hok, heq⟩, hS⟩
  · exact (hg.1 t ht).trans (hw (.inl t) ht).symm
  · exact (hg.2 g hg').trans (hw (.inr g) hg').symm

theorem lese_laenge (σ : World D) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    σ.spur.length ≤ (σ.lese Λ os).spur.length :=
  spur_laenge_erw (Erw.lese σ Λ os)

theorem fuss_rumpf (P : Programm D) (f : D.Fn) : endblockOrteP P (P.rumpf f) ⊆ fussOrte P f :=
  fun _ ho => List.mem_append_left _ (List.mem_append_right _ ho)

theorem fuss_ens (P : Programm D) (f : D.Fn) : (P.ensures f).orte ⊆ fussOrte P f :=
  fun _ ho => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ho))

theorem fuss_req (P : Programm D) (f : D.Fn) : (P.requires f).orte ⊆ fussOrte P f :=
  fun _ ho => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ho))

/-- The carriers of an owed invariant are in the footprint. -/
theorem fuss_inv (P : Programm D) (f : D.Fn) {i : D.Inv} (hi : i ∈ D.invs)
    (hs : schuldet f i = true) : (P.invariante i).orte ⊆ fussOrte P f :=
  fun _ ho => List.mem_append_right _
    (List.mem_flatMap.mpr ⟨i, List.mem_filter.mpr ⟨hi, hs⟩, ho⟩)

end Hilfen
/-! ## 4. Calls and returns of the replay -/

/-- The answer world a return records: the machine's memory at the return,
    one trace event past the call key (a fresh position: the record stays a
    function of the key). -/
def antwortWelt (e0 : Ereignis D) (s1 κ : World D) : World D := ⟨s1.slots, s1.globs, e0 :: κ.spur⟩

section Rufe

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **The return leg.** At a return of the head frame, the body's
    sequential run with the recorded handler returns the same value in a
    world agreeing with the machine's on the footprint; `KoerperGut` gives
    `ensures` there, hence at the machine's return world. -/
theorem pop_ens (hK : ∀ f, KoerperGut P O passes f) {G : RufRahmenG D} {W : World D}
    (hG : KopfOk P O passes G W) {lr : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D G.f) lr Γ Λ} (hr : G.rest = ⟨lr, Γ, Λ, ρ, r⟩)
    (e : ErgExpr D Γ Λ (vertragVon D G.f).erg) (he : e.orte ⊆ fussOrte P G.f)
    (hsem : ∀ R σ, semZ O passes R r σ ρ =
      .zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)) :
    EnsAmRueck P G.f G.s0 (W.lese Λ e.orte) G.rho
      (evalErg (W.lese Λ e.orte) e (W.lese Λ e.orte) ρ) := by
  obtain ⟨H, σ, hreq, hf, hv, _, hg, _, heq⟩ := hG
  have h1 := heq (rufAus H) (rufAus_passt hf)
  have hrest := congrArg (fun c : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D),
    Env D Γ × GRest D (vertragVon D G.f) l Γ Λ =>
      semZ O passes (rufAus H) c.2.2.2.2 σ c.2.2.2.1) hr
  have h1 := ZErg.gleich_trans h1 (ZErg.gleich_of_eq hrest)
  rw [hsem] at h1
  obtain ⟨σ'', hex, hsg⟩ := zErg_gleich_zurueck h1
  have hE := (hK G.f (rufAus H) (rufAus_respektiert hv) (rufAus_ohneVorbedingung H) G.s0 G.rho
    hreq).1 σ'' _ hex
  have hgl : GleichAuf (fussOrte P G.f) (σ.lese Λ e.orte) (W.lese Λ e.orte) :=
    hg.lese Λ Λ e.orte e.orte
  rw [evalErg_gleichAuf e (fun _ h => he h) hgl ρ] at hE
  exact ens_transfer hE (GleichAuf.refl _ _)
    (GleichAuf.mono (fun _ h => fuss_ens P G.f h) ((gleichAuf_SG hsg).trans hgl))

/-- **The caller resumes.** After the callee `G` returned `v` in the
    machine world `s1` (with `ensures` there), the suspended frame `F`
    records the answer (the machine's memory, a fresh trace position) and
    becomes a replayed head frame with the continuation `r'` chosen by the
    pop (`hwahl`). -/
theorem pop_kopf (e0 : Ereignis D) {F : RufRahmenG D}
    {G : Σ f : D.Fn, Env D (D.params f) × World D}
    (hW : WarteOk P O passes F G) (s1 : World D) (v : ErgVal D (D.erg G.1))
    (hens : EnsAmRueck P G.1 G.2.2 s1 G.2.1 v)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ' : Env D Γ) (r' : GRest D (vertragVon D F.f) l Γ Λ)
    (hok' : F.rest.2.2.2.2.okZ P (fussOrte P F.f) → r'.okZ P (fussOrte P F.f))
    (hwahl : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (σa : World D)
      (X : ZErg (vertragVon D F.f)),
      (F.wartend = false → X.gleich (semZ O passes R F.rest.2.2.2.2 σa F.rest.2.2.2.1)) →
      (∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
          (restb : Block D (vertragVon D F.f) l (τ :: Γ) Λ Λ')
          (k : GRest D (vertragVon D F.f) l Γ Λ') (ρc : Env D Γ),
        F.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩ → ∀ he : D.erg G.1 = some τ,
        X.gleich (semZ O passes R (.dann restb (.schrumpf k)) σa (.cons (ergWert he v) ρc))) →
      X.gleich (semZ O passes R r' σa ρ'))
    (W' : World D) (hW' : W'.slots = s1.slots ∧ W'.globs = s1.globs) :
    KopfOk P O passes ⟨F.f, F.rho, F.s0, ⟨l, Γ, Λ, ρ', r'⟩⟩ W' := by
  obtain ⟨H, κ, hreq, hf, hv, hk, hok, hreqκ, hglκ, hcont⟩ := hW
  have hmem : (⟨G.1, κ, G.2.1, antwortWelt e0 s1 κ, v⟩ : Eintrag D) ∈
      H ++ [⟨G.1, κ, G.2.1, antwortWelt e0 s1 κ, v⟩] :=
    List.mem_append_right _ List.mem_cons_self
  refine ⟨H ++ [⟨G.1, κ, G.2.1, antwortWelt e0 s1 κ, v⟩], antwortWelt e0 s1 κ, hreq,
    funk_append hf hk _ (Nat.le_refl _), ?_, ?_, ?_, hok' hok, ?_⟩
  · intro g σ ρ σa w hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hv g σ ρ σa w hm
    · rw [List.mem_singleton] at hm
      cases hm
      refine ⟨hreqκ, ens_transfer hens ?_ ?_⟩
      · exact GleichAuf.mono (fun _ h => List.mem_append_right _ h) hglκ.symm
      · exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  · intro e hm
    rcases List.mem_append.mp hm with hm | hm
    · exact Nat.lt_succ_of_lt (hk e hm)
    · rw [List.mem_singleton] at hm
      subst hm
      exact Nat.lt_succ_self _
  · exact ⟨fun t _ => congrFun hW'.1.symm t, fun g _ => congrFun hW'.2.symm g⟩
  · intro R hR
    have hans := hR _ _ _ _ _ hmem
    obtain ⟨c1, c2⟩ := hcont R (passt_append hR) _ v hans
    exact hwahl R _ _ c1 c2

/-- **The call leg.** At a call of the head frame, the recorded handler
    gated by `requires` (`torRuf`) repeats the record; if the callee's
    `requires` failed at the sequential key world, the body's run with it
    would end in `logik (vorbedingung g)`, which `KoerperGut`'s caller duty
    excludes. So `requires` holds at the key world -- and at the machine's
    entry world, which agrees with it on the callee's contract carriers. -/
theorem push_req (hK : ∀ f, KoerperGut P O passes f) {F : RufRahmenG D}
    {H : List (Eintrag D)} {σ : World D}
    (hreq : ReqAmEintritt P F.f F.s0 F.rho) (hf : Funk H) (hv : VertraegeOk P H)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    (r : GRest D (vertragVon D F.f) l Γ Λ)
    (heq : ∀ R, Passt R H →
      (zErg (execEnd (V := vertragVon D F.f) O passes R (P.rumpf F.f) F.s0 F.rho)).gleich
        (semZ O passes R r σ ρ))
    (g : D.Fn) (κ : World D) (ρk : Env D (D.params g))
    (hlogik : ∀ R (e : Logik D), R g κ ρk = .logik e → semZ O passes R r σ ρ = .logik e) :
    ReqAmEintritt P g κ ρk := by
  cases hq : wahr? (eval κ (P.requires g) κ ρk) with
  | true => exact hq
  | false =>
      exfalso
      have htor : torRuf P (rufAus H) g κ ρk = .logik (.vorbedingung g) := by
        simp only [torRuf, hq]
        rfl
      have h1 := heq _ (torRuf_passt (rufAus_passt hf) hv)
      rw [hlogik _ _ htor] at h1
      have hex := zErg_gleich_logik h1
      exact (hK F.f (rufAus H) (rufAus_respektiert hv) (rufAus_ohneVorbedingung H) F.s0 F.rho
        hreq).2 g hex

end Rufe

end Gabbro.Grammatik
