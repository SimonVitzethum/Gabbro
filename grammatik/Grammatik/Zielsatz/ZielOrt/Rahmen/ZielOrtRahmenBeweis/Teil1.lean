module
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmenBeweis.Teil1Basis
import all Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmenBeweis.Teil1Basis

public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmenSem
public import Grammatik.Logik.Vertraege.AxiomVertrag

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}
/-! ## 2. The steps of the replay -/

section Schritte

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D}

theorem kopfR_okG {F : RufRahmenG D} {W : World D} (h : KopfR P O passes Q F W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D F.f) l Γ Λ} (hr : F.rest = ⟨l, Γ, Λ, ρ, r⟩) :
    r.okG P (fussOrteG P F.f) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hok, _⟩ := h
  rw [hr] at hok
  exact hok

/-- **A head-local step without a new record** keeps the replay: the
    residue moves by a step of the frame semantics whose new prediction
    refines the old one. -/
theorem fadenR_lokalQ {z : RufFadenG D} {W W' : World D} (hF : FadenR P O passes Q z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    {l' : Bool} {Γ' : Ctx} {Λ' : List (Res D)} (ρ' : Env D Γ')
    (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (spur' : List (Ereignis D))
    (hstep : ∀ σ : World D, GleichAuf (fussOrteG P z.kopf.f) σ W →
      r.okG P (fussOrteG P z.kopf.f) →
      ∃ σ', σ.spur.length ≤ σ'.spur.length ∧ GleichAuf (fussOrteG P z.kopf.f) σ' W' ∧
        r'.okG P (fussOrteG P z.kopf.f) ∧
        ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D),
          GleichRS O O' → (semV O' passes R r σ ρ).folgt (semV O' passes R r' σ' ρ')) :
    FadenR P O passes Q
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩ W' := by
  obtain ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hg, hok, heq⟩, hS⟩ := hF
  have hok' : r.okG P (fussOrteG P z.kopf.f) := by rw [hr] at hok; exact hok
  obtain ⟨σ', hl, hg', hok'', hsem⟩ := hstep σ hg hok'
  refine ⟨⟨H, HA, σ', hreq, hf, hv, kurzV_mono hk hl, hfa, hra, hqa, kurzA_mono hka hl, hg', hok'',
    fun R O' hR hA hQ => ?_⟩, hS⟩
  have h1 := heq R O' hR hA hQ
  rw [hr] at h1
  exact ZErg.folgt_trans h1 (hsem R O' hQ)

/-- `fadenR_lokalQ` for a step whose frame semantics holds for every
    sequential oracle. -/
theorem fadenR_lokal {z : RufFadenG D} {W W' : World D} (hF : FadenR P O passes Q z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    {l' : Bool} {Γ' : Ctx} {Λ' : List (Res D)} (ρ' : Env D Γ')
    (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (spur' : List (Ereignis D))
    (hstep : ∀ σ : World D, GleichAuf (fussOrteG P z.kopf.f) σ W →
      r.okG P (fussOrteG P z.kopf.f) →
      ∃ σ', σ.spur.length ≤ σ'.spur.length ∧ GleichAuf (fussOrteG P z.kopf.f) σ' W' ∧
        r'.okG P (fussOrteG P z.kopf.f) ∧
        ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D),
          (semV O' passes R r σ ρ).folgt (semV O' passes R r' σ' ρ')) :
    FadenR P O passes Q
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩ W' :=
  fadenR_lokalQ hF hr ρ' r' spur' fun σ hg hok => by
    obtain ⟨σ', hl, hg', hok', hsem⟩ := hstep σ hg hok
    exact ⟨σ', hl, hg', hok', fun R O' _ => hsem R O'⟩

/-- Memory moved outside the head's footprint keeps the replay. -/
theorem fadenR_speicher {z : RufFadenG D} {W W' : World D} (hF : FadenR P O passes Q z W)
    (hw : ∀ c ∈ fussOrteG P z.kopf.f, TraegerGleich W'.speicher W.speicher c) :
    FadenR P O passes Q z W' := by
  obtain ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hg, hok, heq⟩, hS⟩ := hF
  refine ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, ⟨fun t ht => ?_, fun g hg' => ?_⟩, hok,
    heq⟩, hS⟩
  · exact (hg.1 t ht).trans (hw (.inl t) ht).symm
  · exact (hg.2 g hg').trans (hw (.inr g) hg').symm

/-- **The return leg.** -/
theorem popR_ens (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hK : ∀ f, KoerperGutRQ P passes Q f) {G : RufRahmenG D}
    {W : World D} (hG : KopfR P O passes Q G W) {lr : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {r : GRest D (vertragVon D G.f) lr Γ Λ} (hr : G.rest = ⟨lr, Γ, Λ, ρ, r⟩)
    (e : ErgExpr D Γ Λ (vertragVon D G.f).erg) (he : e.orte ⊆ fussOrteG P G.f)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (σ : World D), (semV O' passes R r σ ρ).gleich
        (.zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ))) :
    EnsAmRueck P G.f G.s0 (W.lese Λ e.orte) G.rho
      (evalErg (W.lese Λ e.orte) e (W.lese Λ e.orte) ρ) := by
  obtain ⟨H, HA, σ, hreq, hf, hv, _, hfa, hra, hqa, _, hg, _, heq⟩ := hG
  have h1 := heq (rufAusV H) (orakelAus O HA) (rufAusV_passt hf) (orakelAus_passt O hfa)
    (gleichRS_orakelAus O HA)
  rw [hr] at h1
  simp only at h1
  have h2 := ZErg.folgt_zurueck (ZErg.folgt_trans h1 (ZErg.folgt_of_gleich (hsem _ _ σ)))
  obtain ⟨σ'', hex, hsg⟩ := zErg_gleich_zurueck h2
  have hE := (hK G.f (orakelAus O HA) (orakelAus_rahmen hO hra) (regLokal_orakelAus hRL HA)
    (orakelAus_vertrag hQ hqa) (rufAusV H)
    (rufAusV_rahmen hv) (rufAusV_ohneVorbedingung hv.1) G.s0 G.rho hreq).1 σ'' _ hex
  have hgl : GleichAuf (fussOrteG P G.f) (σ.lese Λ e.orte) (W.lese Λ e.orte) :=
    hg.lese Λ Λ e.orte e.orte
  rw [evalErg_gleichAuf e (fun _ h => he h) hgl ρ] at hE
  exact ens_transfer hE (GleichAuf.refl _ _)
    (GleichAuf.mono (fun _ h => fuss_ensG P G.f h) ((gleichAuf_SG hsg).trans hgl))

/-- **The call leg.** -/
theorem pushR_req (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hK : ∀ f, KoerperGutRQ P passes Q f) {F : RufRahmenG D}
    {H : List (EintragV D)} {HA : List (AxEintrag D)} {σ : World D}
    (hreq : ReqAmEintritt P F.f F.s0 F.rho) (hf : FunkV H) (hv : VertraegeOkR P H)
    (hfa : FunkA HA) (hra : RahmenA HA) (hqa : VertragA O.zeiger Q HA)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    (r : GRest D (vertragVon D F.f) l Γ Λ)
    (heq : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D),
      PasstV R H → PasstA O' HA → GleichRS O O' →
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
      have h1 := heq _ (orakelAus O HA) (torRuf_passtV (rufAusV_passt hf) hv.1)
        (orakelAus_passt O hfa) (gleichRS_orakelAus O HA)
      rw [hlogik _ _ _ htor] at h1
      have hex := zErg_gleich_logik (ZErg.folgt_logik h1)
      exact (hK F.f (orakelAus O HA) (orakelAus_rahmen hO hra) (regLokal_orakelAus hRL HA)
        (orakelAus_vertrag hQ hqa) (rufAusV H)
        (rufAusV_rahmen hv) (rufAusV_ohneVorbedingung hv.1) F.s0 F.rho hreq).2 g hex

/-- **The caller resumes** after its pending call to `G` was answered by
    `mk` (a normal answer, whose `ensures` holds at the machine's return
    world `s1`, or a reason): the answer is recorded at the pending key with
    the answer world `rahmenWelt` -- the callee's declared write carriers
    from the machine, every other carrier from the key world, a lock-neutral
    fresh trace position -- and the frame becomes a replayed head with the
    continuation `r'` chosen by the pop. `hRah` is the machine's frame fact
    (`rufG_rahmen`): the return world agrees with the callee's entry world on
    the caller's footprint outside the callee's declared writes. -/
theorem popR_kopf (e0 : Ereignis D) {F : RufRahmenG D}
    {G : Σ f : D.Fn, Env D (D.params f) × World D}
    (hW : WarteR P O passes Q F G) (s1 : World D) (mk : World D → RufAusgang G.1)
    (hmk : (∃ v, (∀ σa, mk σa = .ok σa v) ∧ EnsAmRueck P G.1 G.2.2 s1 G.2.1 v) ∨
      (∃ r, ∀ σa, mk σa = .why σa r))
    (hRah : GleichOhne G.1 (fussOrteG P F.f) G.2.2 s1)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ' : Env D Γ) (r' : GRest D (vertragVon D F.f) l Γ Λ)
    (hok' : F.rest.2.2.2.2.okG P (fussOrteG P F.f) → r'.okG P (fussOrteG P F.f))
    (hwahl : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
      (σa : World D) (X : ZErg (vertragVon D F.f)),
      FortV passes F G.1 X R O' (mk σa) → X.folgt (semV O' passes R r' σa ρ'))
    (W' : World D) (hW' : W'.slots = s1.slots ∧ W'.globs = s1.globs) :
    KopfR P O passes Q ⟨F.f, F.rho, F.s0, ⟨l, Γ, Λ, ρ', r'⟩⟩ W' := by
  obtain ⟨H, HA, κ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hok, hreqκ, ⟨hglκ, hsub, hfussκ⟩, hcont⟩ :=
    hW
  have hσa : GleichAuf (fussOrteG P F.f) (rahmenWelt e0 G.1 κ s1) s1 :=
    rahmenWelt_gleichAuf e0 G.1 hfussκ hRah
  have hlen := rahmenWelt_laenge e0 G.1 κ s1
  have hmem : (⟨G.1, κ, G.2.1, mk (rahmenWelt e0 G.1 κ s1)⟩ : EintragV D) ∈
      H ++ [⟨G.1, κ, G.2.1, mk (rahmenWelt e0 G.1 κ s1)⟩] :=
    List.mem_append_right _ List.mem_cons_self
  refine ⟨H ++ [⟨G.1, κ, G.2.1, mk (rahmenWelt e0 G.1 κ s1)⟩], HA, rahmenWelt e0 G.1 κ s1, hreq,
    funkV_append hf hk _ (Nat.le_refl _), ⟨?_, ?_⟩, ?_, hfa, hra, hqa,
    kurzA_mono hka (Nat.le_of_lt hlen), ?_, hok' hok, ?_⟩
  · intro g σ ρ a hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hv.1 g σ ρ a hm
    · rw [List.mem_singleton] at hm
      cases hm
      refine ⟨hreqκ, ?_, ?_⟩
      · intro σa w hw
        rcases hmk with ⟨v, hv', hens⟩ | ⟨rr, hr'⟩
        · rw [hv'] at hw
          cases hw
          refine ens_transfer hens ?_ ?_
          · exact GleichAuf.mono (fun _ h => List.mem_append_right _ h) hglκ.symm
          · exact (GleichAuf.mono (fun _ h => hsub (List.mem_append_right _ h)) hσa).symm
        · rw [hr'] at hw
          cases hw
      · intro e he
        rcases hmk with ⟨v, hv', _⟩ | ⟨rr, hr'⟩
        · rw [hv'] at he; cases he
        · rw [hr'] at he; cases he
  · intro g σ ρ a hm σ' w hw
    rcases List.mem_append.mp hm with hm | hm
    · exact hv.2 g σ ρ a hm σ' w hw
    · rw [List.mem_singleton] at hm
      cases hm
      have e : σ' = rahmenWelt e0 G.1 κ s1 := by
        rcases hmk with ⟨v, hv', _⟩ | ⟨rr, hr'⟩
        · rw [hv'] at hw; cases hw; rfl
        · rw [hr'] at hw; cases hw
      subst e
      exact ⟨rahmenWelt_rahmen e0 G.1 κ s1, rahmenWelt_offen e0 G.1 κ s1⟩
  · intro e hm
    rcases List.mem_append.mp hm with hm | hm
    · exact Nat.lt_trans (hk e hm) hlen
    · rw [List.mem_singleton] at hm
      subst hm
      exact hlen
  · exact ⟨fun t ht => (hσa.1 t ht).trans (congrFun hW'.1.symm t),
      fun g hg => (hσa.2 g hg).trans (congrFun hW'.2.symm g)⟩
  · intro R O' hR hA hQ
    have hans := hR _ _ _ _ hmem
    have hc := hcont R O' (passtV_append hR) hA hQ
    rw [hans] at hc
    exact hwahl R O' _ _ hc

/-- **A push keeps the replay.** The head frame calls `g` with `args`; it
    becomes a suspended frame with the continuation `rc`, and the callee's
    frame becomes a fresh replayed head. The callee's `requires` holds at
    the machine's entry world (`pushR_req`), for the log. -/
theorem pushR_ok (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hK : ∀ f, KoerperGutRQ P passes Q f)
    (hFrag : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (fussOrteG P f)) = true)
    {z : RufFadenG D} {W : World D} (hF : FadenR P O passes Q z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (g : D.Fn) (args : Args D Γ Λ (D.params g))
    (hS : r.okG P (fussOrteG P z.kopf.f) → args.orte ⊆ fussOrteG P z.kopf.f ∧
      (P.requires g).orte ++ (P.ensures g).orte ⊆ fussOrteG P z.kopf.f)
    {lc : Bool} {Γc : Ctx} {Λc : List (Res D)} (ρc : Env D Γc)
    (rc : GRest D (vertragVon D z.kopf.f) lc Γc Λc)
    (hrc : r.okG P (fussOrteG P z.kopf.f) → rc.okG P (fussOrteG P z.kopf.f))
    (hlogik : ∀ (O' : Orakel D) R σ (e : Logik D),
      R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
        .logik e → semV O' passes R r σ ρ = .logik e)
    (hweiter : ∀ (O' : Orakel D) R σ,
      FortV passes ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩ g
        (semV O' passes R r σ ρ) R O'
        (R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ))) :
    FadenR P O passes Q
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
  obtain ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hg, hok, heq⟩, hSt⟩ := hF
  have hok' : r.okG P (fussOrteG P z.kopf.f) := by rw [hr] at hok; exact hok
  have heq' : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D),
      PasstV R H → PasstA O' HA → GleichRS O O' →
      (zErg (execEnd (V := vertragVon D z.kopf.f) O' passes R (P.rumpf z.kopf.f) z.kopf.s0
        z.kopf.rho)).folgt (semV O' passes R r σ ρ) := by
    intro R O' hR hA hQ
    have := heq R O' hR hA hQ
    rw [hr] at this
    exact this
  obtain ⟨hargs, hctr⟩ := hS hok'
  have hgκ : GleichAuf (fussOrteG P z.kopf.f) (σ.lese Λ args.orte) (W.lese Λ args.orte) :=
    hg.lese Λ Λ args.orte args.orte
  have hρk : evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ =
      evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ :=
    evalArgs_gleichAuf args (fun _ h => hargs h) hgκ ρ
  have hreqκ := pushR_req hO hRL hQ hK hreq hf hv hfa hra hqa r heq' g (σ.lese Λ args.orte)
    (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
    (fun O' R e h => hlogik O' R σ e h)
  rw [hρk] at hreqκ
  have hctrκ : GleichAuf ((P.requires g).orte ++ (P.ensures g).orte) (σ.lese Λ args.orte)
      (W.lese Λ args.orte) := GleichAuf.mono (fun _ h => hctr h) hgκ
  have hreq0 := req_transfer hreqκ
    (GleichAuf.mono (fun _ h => List.mem_append_left _ h) hctrκ)
  refine ⟨⟨⟨[], [], W.lese Λ args.orte, hreq0, funkV_nil, vertraegeOkR_nil P, kurzV_nil _,
    funkA_nil, rahmenA_nil, vertragA_nil _ Q, kurzA_nil _,
    GleichAuf.refl _ _, ⟨hFrag g, fuss_rumpfG P g⟩, fun R O' _ _ _ => ZErg.folgt_refl _⟩,
    ⟨H, HA, σ.lese Λ args.orte, hreq, hf, hv, kurzV_mono hk (lese_laenge _ _ _), hfa, hra, hqa,
      kurzA_mono hka (lese_laenge _ _ _), hrc hok', hreqκ, ⟨hctrκ, hctr, hgκ⟩, ?_⟩, hSt⟩, hreq0⟩
  intro R O' hR hA hQ
  have hw := hweiter O' R σ
  rw [hρk] at hw
  exact fortV_mono (F := ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩)
    (heq' R O' hR hA hQ) hw

/-- **A push through a read set `os` and a parameter function `rhoF`** --
    the shape of an indirect call, whose callee `g` the pointer read at the
    key names (the sequential side only needs it at worlds agreeing with the
    machine world on the footprint, `hlogik`, `hweiter`). -/
theorem pushR_gen (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hK : ∀ f, KoerperGutRQ P passes Q f)
    (hFrag : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (fussOrteG P f)) = true)
    {z : RufFadenG D} {W : World D} (hF : FadenR P O passes Q z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (os : List (D.Tab ⊕ D.Glob)) (g : D.Fn) (rhoF : World D → Env D (D.params g))
    (hS : r.okG P (fussOrteG P z.kopf.f) →
      (P.requires g).orte ++ (P.ensures g).orte ⊆ fussOrteG P z.kopf.f)
    (hrho : r.okG P (fussOrteG P z.kopf.f) → ∀ σ : World D,
      GleichAuf (fussOrteG P z.kopf.f) σ W → rhoF (σ.lese Λ os) = rhoF (W.lese Λ os))
    {lc : Bool} {Γc : Ctx} {Λc : List (Res D)} (ρc : Env D Γc)
    (rc : GRest D (vertragVon D z.kopf.f) lc Γc Λc)
    (hrc : r.okG P (fussOrteG P z.kopf.f) → rc.okG P (fussOrteG P z.kopf.f))
    (hlogik : ∀ (O' : Orakel D) R σ (e : Logik D), GleichAuf (fussOrteG P z.kopf.f) σ W →
      R g (σ.lese Λ os) (rhoF (σ.lese Λ os)) = .logik e → semV O' passes R r σ ρ = .logik e)
    (hweiter : ∀ (O' : Orakel D) R σ, GleichAuf (fussOrteG P z.kopf.f) σ W →
      FortV passes ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩ g
        (semV O' passes R r σ ρ) R O' (R g (σ.lese Λ os) (rhoF (σ.lese Λ os)))) :
    FadenR P O passes Q
      ⟨⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩ :: z.stapel,
        ⟨g, rhoF (W.lese Λ os), W.lese Λ os,
          ⟨false, D.params g, Signatur.anfang D (D.signatur g), rhoF (W.lese Λ os),
            .ende (P.rumpf g)⟩⟩,
        (W.lese Λ os).spur,
        RufEreignisF.eintritt g (rhoF (W.lese Λ os)) (W.lese Λ os) :: z.log⟩
      (W.lese Λ os) ∧
    ReqAmEintritt P g (W.lese Λ os) (rhoF (W.lese Λ os)) := by
  obtain ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hg, hok, heq⟩, hSt⟩ := hF
  have hok' : r.okG P (fussOrteG P z.kopf.f) := by rw [hr] at hok; exact hok
  have heq' : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D),
      PasstV R H → PasstA O' HA → GleichRS O O' →
      (zErg (execEnd (V := vertragVon D z.kopf.f) O' passes R (P.rumpf z.kopf.f) z.kopf.s0
        z.kopf.rho)).folgt (semV O' passes R r σ ρ) := by
    intro R O' hR hA hQ
    have := heq R O' hR hA hQ
    rw [hr] at this
    exact this
  have hctr := hS hok'
  have hgκ : GleichAuf (fussOrteG P z.kopf.f) (σ.lese Λ os) (W.lese Λ os) := hg.lese Λ Λ os os
  have hρk : rhoF (σ.lese Λ os) = rhoF (W.lese Λ os) := hrho hok' σ hg
  have hreqκ := pushR_req hO hRL hQ hK hreq hf hv hfa hra hqa r heq' g (σ.lese Λ os) (rhoF (σ.lese Λ os))
    (fun O' R e h => hlogik O' R σ e hg h)
  rw [hρk] at hreqκ
  have hctrκ : GleichAuf ((P.requires g).orte ++ (P.ensures g).orte) (σ.lese Λ os)
      (W.lese Λ os) := GleichAuf.mono (fun _ h => hctr h) hgκ
  have hreq0 := req_transfer hreqκ
    (GleichAuf.mono (fun _ h => List.mem_append_left _ h) hctrκ)
  refine ⟨⟨⟨[], [], W.lese Λ os, hreq0, funkV_nil, vertraegeOkR_nil P, kurzV_nil _,
    funkA_nil, rahmenA_nil, vertragA_nil _ Q, kurzA_nil _,
    GleichAuf.refl _ _, ⟨hFrag g, fuss_rumpfG P g⟩, fun R O' _ _ _ => ZErg.folgt_refl _⟩,
    ⟨H, HA, σ.lese Λ os, hreq, hf, hv, kurzV_mono hk (lese_laenge _ _ _), hfa, hra, hqa,
      kurzA_mono hka (lese_laenge _ _ _), hrc hok', hreqκ, ⟨hctrκ, hctr, hgκ⟩, ?_⟩, hSt⟩, hreq0⟩
  intro R O' hR hA hQ
  have hw := hweiter O' R σ hg
  rw [hρk] at hw
  exact fortV_mono (F := ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩)
    (heq' R O' hR hA hQ) hw

end Schritte

/-! ## 3. The steps of the replay that record an answer -/

end Gabbro.Grammatik
