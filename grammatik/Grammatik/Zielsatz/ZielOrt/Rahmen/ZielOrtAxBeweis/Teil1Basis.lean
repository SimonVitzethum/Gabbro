module

public import Grammatik.Logik.Vertraege.AxiomVertrag

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 3. The replay invariants -/

section Inv

variable (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)

/-- **The replay of a head frame** `F` whose thread world is `W`: records of
    its calls `H` and its axiom calls `HA` (functions of their keys, keys
    below the sequential trace, call answers respecting the callees'
    contracts, axiom answers inside their frames), a sequential world `σ`
    agreeing with `W` on the footprint, the residue in the fragment; and
    for ANY handler and ANY oracle repeating the records, the residue run
    from `σ` predicts the body's result. -/
def KopfA (F : RufRahmenG D) (W : World D) : Prop :=
  ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (σ : World D),
    ReqAmEintritt P F.f F.s0 F.rho ∧ FunkV H ∧ VertraegeOkV P H ∧ KurzV σ.spur.length H ∧
    FunkA HA ∧ RahmenA HA ∧ VertragA O.zeiger Q HA ∧ KurzA σ.spur.length HA ∧
    GleichAuf (fussOrte P F.f) σ W ∧ F.rest.2.2.2.2.okV P (fussOrte P F.f) ∧
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D),
      PasstV R H → PasstA O' HA → ZeigerGleich O O' →
      (zErg (execEnd (V := vertragVon D F.f) O' passes R (P.rumpf F.f) F.s0 F.rho)).folgt
        (semV O' passes R F.rest.2.2.2.2 σ F.rest.2.2.2.1)

/-- **The replay of a suspended frame** `F` waiting for the callee with key
    `G`: records, the sequential key world `κ` of the pending call (the
    callee's `requires` holds there; it agrees with the callee's machine
    entry world on the callee's contract carriers), and for any handler and
    oracle repeating the records, the continuation after the handler's
    answer to the pending call predicts the body's result. -/
def WarteA (F : RufRahmenG D) (G : Σ f : D.Fn, Env D (D.params f) × World D) : Prop :=
  ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (κ : World D),
    ReqAmEintritt P F.f F.s0 F.rho ∧ FunkV H ∧ VertraegeOkV P H ∧ KurzV κ.spur.length H ∧
    FunkA HA ∧ RahmenA HA ∧ VertragA O.zeiger Q HA ∧ KurzA κ.spur.length HA ∧
    F.rest.2.2.2.2.okV P (fussOrte P F.f) ∧
    ReqAmEintritt P G.1 κ G.2.1 ∧
    GleichAuf ((P.requires G.1).orte ++ (P.ensures G.1).orte) κ G.2.2 ∧
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D),
      PasstV R H → PasstA O' HA → ZeigerGleich O O' →
      FortV passes F G.1
        (zErg (execEnd (V := vertragVon D F.f) O' passes R (P.rumpf F.f) F.s0 F.rho)) R O'
        (R G.1 κ G.2.1)

def StapelA : (Σ f : D.Fn, Env D (D.params f) × World D) → List (RufRahmenG D) → Prop
  | _, [] => True
  | G, F :: rest => WarteA P O passes Q F G ∧ StapelA (RufSchluesselG F) rest

def FadenA (z : RufFadenG D) (W : World D) : Prop :=
  KopfA P O passes Q z.kopf W ∧ StapelA P O passes Q (RufSchluesselG z.kopf) z.stapel

def ZielInvA (M : RufMaschineG D) : Prop :=
  (∀ t, FadenA P O passes Q (M.faeden t) (M.weltVon t)) ∧ ∀ t, LogOk P (M.faeden t).log

end Inv

/-! ## 4. The steps of the replay -/

section Schritte

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D}

theorem kopfA_okV {F : RufRahmenG D} {W : World D} (h : KopfA P O passes Q F W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D F.f) l Γ Λ} (hr : F.rest = ⟨l, Γ, Λ, ρ, r⟩) :
    r.okV P (fussOrte P F.f) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hok, _⟩ := h
  rw [hr] at hok
  exact hok

/-- **A head-local step without a new record** keeps the replay: the
    residue moves by a step of the frame semantics whose new prediction
    refines the old one. -/
theorem fadenA_lokal {z : RufFadenG D} {W W' : World D} (hF : FadenA P O passes Q z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    {l' : Bool} {Γ' : Ctx} {Λ' : List (Res D)} (ρ' : Env D Γ')
    (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (spur' : List (Ereignis D))
    (hstep : ∀ σ : World D, GleichAuf (fussOrte P z.kopf.f) σ W →
      r.okV P (fussOrte P z.kopf.f) →
      ∃ σ', σ.spur.length ≤ σ'.spur.length ∧ GleichAuf (fussOrte P z.kopf.f) σ' W' ∧
        r'.okV P (fussOrte P z.kopf.f) ∧
        ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D),
          (semV O' passes R r σ ρ).folgt (semV O' passes R r' σ' ρ')) :
    FadenA P O passes Q
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩ W' := by
  obtain ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hg, hok, heq⟩, hS⟩ := hF
  have hok' : r.okV P (fussOrte P z.kopf.f) := by rw [hr] at hok; exact hok
  obtain ⟨σ', hl, hg', hok'', hsem⟩ := hstep σ hg hok'
  refine ⟨⟨H, HA, σ', hreq, hf, hv, kurzV_mono hk hl, hfa, hra, hqa, kurzA_mono hka hl, hg', hok'',
    fun R O' hR hA hz => ?_⟩, hS⟩
  have h1 := heq R O' hR hA hz
  rw [hr] at h1
  exact ZErg.folgt_trans h1 (hsem R O')

/-- Memory moved outside the head's footprint keeps the replay. -/
theorem fadenA_speicher {z : RufFadenG D} {W W' : World D} (hF : FadenA P O passes Q z W)
    (hw : ∀ c ∈ fussOrte P z.kopf.f, TraegerGleich W'.speicher W.speicher c) :
    FadenA P O passes Q z W' := by
  obtain ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hg, hok, heq⟩, hS⟩ := hF
  refine ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, ⟨fun t ht => ?_, fun g hg' => ?_⟩, hok,
    heq⟩, hS⟩
  · exact (hg.1 t ht).trans (hw (.inl t) ht).symm
  · exact (hg.2 g hg').trans (hw (.inr g) hg').symm

/-- **The return leg.** -/
theorem popA_ens (hO : GutO O) (hQ : AxVertragO Q O) (hK : ∀ f, KoerperGutA P passes Q f) {G : RufRahmenG D}
    {W : World D} (hG : KopfA P O passes Q G W) {lr : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {r : GRest D (vertragVon D G.f) lr Γ Λ} (hr : G.rest = ⟨lr, Γ, Λ, ρ, r⟩)
    (e : ErgExpr D Γ Λ (vertragVon D G.f).erg) (he : e.orte ⊆ fussOrte P G.f)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (σ : World D), (semV O' passes R r σ ρ).gleich
        (.zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ))) :
    EnsAmRueck P G.f G.s0 (W.lese Λ e.orte) G.rho
      (evalErg (W.lese Λ e.orte) e (W.lese Λ e.orte) ρ) := by
  obtain ⟨H, HA, σ, hreq, hf, hv, _, hfa, hra, hqa, _, hg, _, heq⟩ := hG
  have h1 := heq (rufAusV H) (orakelAus O HA) (rufAusV_passt hf) (orakelAus_passt O hfa) rfl
  rw [hr] at h1
  simp only at h1
  have h2 := ZErg.folgt_zurueck (ZErg.folgt_trans h1 (ZErg.folgt_of_gleich (hsem _ _ σ)))
  obtain ⟨σ'', hex, hsg⟩ := zErg_gleich_zurueck h2
  have hE := (hK G.f (orakelAus O HA) (orakelAus_rahmen hO hra) (orakelAus_vertrag hQ hqa) (rufAusV H)
    (rufAusV_respektiert hv) (rufAusV_ohneVorbedingung hv) G.s0 G.rho hreq).1 σ'' _ hex
  have hgl : GleichAuf (fussOrte P G.f) (σ.lese Λ e.orte) (W.lese Λ e.orte) :=
    hg.lese Λ Λ e.orte e.orte
  rw [evalErg_gleichAuf e (fun _ h => he h) hgl ρ] at hE
  exact ens_transfer hE (GleichAuf.refl _ _)
    (GleichAuf.mono (fun _ h => fuss_ens P G.f h) ((gleichAuf_SG hsg).trans hgl))

/-- **The call leg.** -/
theorem pushA_req (hO : GutO O) (hQ : AxVertragO Q O) (hK : ∀ f, KoerperGutA P passes Q f) {F : RufRahmenG D}
    {H : List (EintragV D)} {HA : List (AxEintrag D)} {σ : World D}
    (hreq : ReqAmEintritt P F.f F.s0 F.rho) (hf : FunkV H) (hv : VertraegeOkV P H)
    (hfa : FunkA HA) (hra : RahmenA HA) (hqa : VertragA O.zeiger Q HA)
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
      exact (hK F.f (orakelAus O HA) (orakelAus_rahmen hO hra) (orakelAus_vertrag hQ hqa) (rufAusV H)
        (rufAusV_respektiert hv) (rufAusV_ohneVorbedingung hv) F.s0 F.rho hreq).2 g hex


end Schritte
end Gabbro.Grammatik
