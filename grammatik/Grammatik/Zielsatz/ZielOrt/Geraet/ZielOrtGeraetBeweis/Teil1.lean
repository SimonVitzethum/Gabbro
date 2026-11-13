module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetBeweis.Teil1Basis
import all Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetBeweis.Teil1Basis

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetSem

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}
section Schritte

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **The caller resumes** after its pending call to `G` was answered by
    `mk` (a normal answer, whose `ensures` holds at the machine's return
    world `s1`, or a reason): the answer is recorded at the pending key with
    the machine's memory and a fresh trace position, and the frame becomes a
    replayed head with the continuation `r'` chosen by the pop. -/
theorem popG_kopf (e0 : Ereignis D) {F : RufRahmenG D}
    {G : Σ f : D.Fn, Env D (D.params f) × World D}
    (hW : WarteG P O passes F G) (s1 : World D) (mk : World D → RufAusgang G.1)
    (hmk : (∃ v, (∀ σa, mk σa = .ok σa v) ∧ EnsAmRueck P G.1 G.2.2 s1 G.2.1 v) ∨
      (∃ r, ∀ σa, mk σa = .why σa r))
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ' : Env D Γ) (r' : GRest D (vertragVon D F.f) l Γ Λ)
    (hok' : F.rest.2.2.2.2.okG P (fussOrteG P F.f) → r'.okG P (fussOrteG P F.f))
    (hwahl : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
      (σa : World D) (X : ZErg (vertragVon D F.f)),
      FortV passes F G.1 X R O' (mk σa) → X.folgt (semV O' passes R r' σa ρ'))
    (W' : World D) (hW' : W'.slots = s1.slots ∧ W'.globs = s1.globs) :
    KopfG P O passes ⟨F.f, F.rho, F.s0, ⟨l, Γ, Λ, ρ', r'⟩⟩ W' := by
  obtain ⟨H, HA, κ, hreq, hf, hv, hk, hfa, hra, hka, hok, hreqκ, hglκ, hcont⟩ := hW
  have hmem : (⟨G.1, κ, G.2.1, mk (antwortWelt e0 s1 κ)⟩ : EintragV D) ∈
      H ++ [⟨G.1, κ, G.2.1, mk (antwortWelt e0 s1 κ)⟩] :=
    List.mem_append_right _ List.mem_cons_self
  refine ⟨H ++ [⟨G.1, κ, G.2.1, mk (antwortWelt e0 s1 κ)⟩], HA, antwortWelt e0 s1 κ, hreq,
    funkV_append hf hk _ (Nat.le_refl _), ?_, ?_, hfa, hra,
    kurzA_mono hka (antwortWelt_rang_le _ _ _), ?_, hok' hok, ?_⟩
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
    · exact Nat.lt_of_lt_of_le (hk e hm) (antwortWelt_rang_le _ _ _)
    · rw [List.mem_singleton] at hm
      subst hm
      exact antwortWelt_rang_lt _ _ _
  · exact ⟨fun t _ => congrFun hW'.1.symm t, fun g _ => congrFun hW'.2.symm g⟩
  · intro R O' hR hA hQ
    have hans := hR _ _ _ _ hmem
    have hc := hcont R O' (passtV_append hR) hA hQ
    rw [hans] at hc
    exact hwahl R O' _ _ hc

/-- **A push keeps the replay.** The head frame calls `g` with `args`; it
    becomes a suspended frame with the continuation `rc`, and the callee's
    frame becomes a fresh replayed head. The callee's `requires` holds at
    the machine's entry world (`pushG_req`), for the log. -/
theorem pushG_ok (hO : GutO O) (hRL : RegLokal O) (hK : ∀ f, KoerperGutG P passes f)
    (hFrag : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (fussOrteG P f)) = true)
    {z : RufFadenG D} {W : World D} (hF : FadenG P O passes z W)
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
    FadenG P O passes
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
  have hreqκ := pushG_req hO hRL hK hreq hf hv hfa hra r heq' g (σ.lese Λ args.orte)
    (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
    (fun O' R e h => hlogik O' R σ e h)
  rw [hρk] at hreqκ
  have hctrκ : GleichAuf ((P.requires g).orte ++ (P.ensures g).orte) (σ.lese Λ args.orte)
      (W.lese Λ args.orte) := GleichAuf.mono (fun _ h => hctr h) hgκ
  have hreq0 := req_transfer hreqκ
    (GleichAuf.mono (fun _ h => List.mem_append_left _ h) hctrκ)
  refine ⟨⟨⟨[], [], W.lese Λ args.orte, hreq0, funkV_nil, vertraegeOkV_nil P, kurzV_nil _,
    funkA_nil, rahmenA_nil, kurzA_nil _,
    GleichAuf.refl _ _, ⟨hFrag g, fuss_rumpfG P g⟩, fun R O' _ _ _ => ZErg.folgt_refl _⟩,
    ⟨H, HA, σ.lese Λ args.orte, hreq, hf, hv, kurzV_mono hk (lese_laenge _ _ _), hfa, hra,
      kurzA_mono hka (lese_laenge _ _ _), hrc hok', hreqκ, hctrκ, ?_⟩, hSt⟩, hreq0⟩
  intro R O' hR hA hQ
  have hw := hweiter O' R σ
  rw [hρk] at hw
  exact fortV_mono (F := ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩)
    (heq' R O' hR hA hQ) hw

/-- **A push through a read set `os` and a parameter function `rhoF`** --
    the shape of an indirect call, whose callee `g` the pointer read at the
    key names (the sequential side only needs it at worlds agreeing with the
    machine world on the footprint, `hlogik`, `hweiter`). -/
theorem pushG_gen (hO : GutO O) (hRL : RegLokal O) (hK : ∀ f, KoerperGutG P passes f)
    (hFrag : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (fussOrteG P f)) = true)
    {z : RufFadenG D} {W : World D} (hF : FadenG P O passes z W)
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
    FadenG P O passes
      ⟨⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩ :: z.stapel,
        ⟨g, rhoF (W.lese Λ os), W.lese Λ os,
          ⟨false, D.params g, Signatur.anfang D (D.signatur g), rhoF (W.lese Λ os),
            .ende (P.rumpf g)⟩⟩,
        (W.lese Λ os).spur,
        RufEreignisF.eintritt g (rhoF (W.lese Λ os)) (W.lese Λ os) :: z.log⟩
      (W.lese Λ os) ∧
    ReqAmEintritt P g (W.lese Λ os) (rhoF (W.lese Λ os)) := by
  obtain ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hka, hg, hok, heq⟩, hSt⟩ := hF
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
  have hreqκ := pushG_req hO hRL hK hreq hf hv hfa hra r heq' g (σ.lese Λ os) (rhoF (σ.lese Λ os))
    (fun O' R e h => hlogik O' R σ e hg h)
  rw [hρk] at hreqκ
  have hctrκ : GleichAuf ((P.requires g).orte ++ (P.ensures g).orte) (σ.lese Λ os)
      (W.lese Λ os) := GleichAuf.mono (fun _ h => hctr h) hgκ
  have hreq0 := req_transfer hreqκ
    (GleichAuf.mono (fun _ h => List.mem_append_left _ h) hctrκ)
  refine ⟨⟨⟨[], [], W.lese Λ os, hreq0, funkV_nil, vertraegeOkV_nil P, kurzV_nil _,
    funkA_nil, rahmenA_nil, kurzA_nil _,
    GleichAuf.refl _ _, ⟨hFrag g, fuss_rumpfG P g⟩, fun R O' _ _ _ => ZErg.folgt_refl _⟩,
    ⟨H, HA, σ.lese Λ os, hreq, hf, hv, kurzV_mono hk (lese_laenge _ _ _), hfa, hra,
      kurzA_mono hka (lese_laenge _ _ _), hrc hok', hreqκ, hctrκ, ?_⟩, hSt⟩, hreq0⟩
  intro R O' hR hA hQ
  have hw := hweiter O' R σ hg
  rw [hρk] at hw
  exact fortV_mono (F := ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩)
    (heq' R O' hR hA hQ) hw

end Schritte

/-! ## 3. The steps of the replay that record an answer -/

section Schritte2

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **An axiom step keeps the replay.** The answer of the machine's oracle
    (`xm`, in the axiom's frame around the machine's call world) is recorded
    at the sequential key, with the answer world `axWelt`: the declared
    carriers from the machine, the rest from the key world, a fresh trace
    position. -/
theorem fadenG_ax (e0 : Ereignis D) {z : RufFadenG D} {W : World D} (hF : FadenG P O passes z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    {l' : Bool} {Γ' : Ctx} {Λ' : List (Res D)} (ρ' : Env D Γ')
    (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (spur' : List (Ereignis D))
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
    (hok : r.okG P (fussOrteG P z.kopf.f) → r'.okG P (fussOrteG P z.kopf.f))
    (xm : World D × Int) (hxm : Rahmen (D.aschreibt a) (D.agschreibt a) (W.lese Λ args.orte) xm.1)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (σ : World D), ZeigerGleich O O' →
      O'.wirkt a ((σ.lese Λ args.orte).fragt (.inl a)) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
        (axWelt e0 a ((σ.lese Λ args.orte).fragt (.inl a)) xm.1, xm.2) →
      (semV O' passes R r σ ρ).folgt
        (semV O' passes R r' (axWelt e0 a ((σ.lese Λ args.orte).fragt (.inl a)) xm.1) ρ')) :
    FadenG P O passes
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩
      (xm.1.speicher.welt spur') := by
  obtain ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hka, hg, hok0, heq⟩, hS⟩ := hF
  have hok' : r.okG P (fussOrteG P z.kopf.f) := by rw [hr] at hok0; exact hok0
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
  · intro R O' hR hA hQ
    have h1 := heq R O' hR (passtA_append hA) hQ
    rw [hr] at h1
    exact ZErg.folgt_trans h1 (hsem O' R σ hQ.2.2 (hA _ _ _ _ (List.mem_append_right _ List.mem_cons_self)))

end Schritte2
end Gabbro.Grammatik
