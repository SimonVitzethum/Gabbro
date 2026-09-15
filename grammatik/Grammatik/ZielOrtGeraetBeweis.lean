/-
  File:      Grammatik/ZielOrtGeraetBeweis.lean
  Subject:   The replay of `ziel_ort_voll` (`ZielOrtVollBeweis.lean`) for the
             widened fragment: the sequential oracles of the replay give the
             machine's register and visibility answers (`GleichRS`), the
             footprint is the widened one (`fussOrteG`), the residues are in
             the widened fragment (`GRest.okG`), and the user obligation is
             `KoerperGutG` (every frame-respecting, register-local oracle).

  The invariants `KopfG`/`WarteG`/`StapelG`/`FadenG`/`ZielInvG` are those of
  `ZielOrtVollBeweis.lean` with three changes: the machine oracle `O` is a
  parameter, the replayed sequential oracles `O'` are those with `O`'s
  register and visibility answers (`GleichRS O O'`), and footprint and
  fragment are the widened ones. The steps are the same; the record oracle
  `orakelAus O HA` has `O`'s register and visibility answers by
  construction, and is register-local when `O` is (`regLokal_orakelAus`).
-/
import Grammatik.ZielOrtGeraetSem

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The replay invariants -/

section Inv

variable (P : Programm D) (O : Orakel D) (passes : Nat)

/-- **The replay of a head frame** `F` whose thread world is `W` (as
    `KopfV`): the sequential oracles are those that repeat the recorded
    axiom answers AND give the machine oracle's register and visibility
    answers. -/
def KopfG (F : RufRahmenG D) (W : World D) : Prop :=
  ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (σ : World D),
    ReqAmEintritt P F.f F.s0 F.rho ∧ FunkV H ∧ VertraegeOkV P H ∧ KurzV σ.spur.length H ∧
    FunkA HA ∧ RahmenA HA ∧ KurzA σ.spur.length HA ∧
    GleichAuf (fussOrteG P F.f) σ W ∧ F.rest.2.2.2.2.okG P (fussOrteG P F.f) ∧
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D),
      PasstV R H → PasstA O' HA → GleichRS O O' →
      (zErg (execEnd (V := vertragVon D F.f) O' passes R (P.rumpf F.f) F.s0 F.rho)).folgt
        (semV O' passes R F.rest.2.2.2.2 σ F.rest.2.2.2.1)

/-- **The replay of a suspended frame** (as `WarteV`), over the same class
    of sequential oracles. -/
def WarteG (F : RufRahmenG D) (G : Σ f : D.Fn, Env D (D.params f) × World D) : Prop :=
  ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (κ : World D),
    ReqAmEintritt P F.f F.s0 F.rho ∧ FunkV H ∧ VertraegeOkV P H ∧ KurzV κ.spur.length H ∧
    FunkA HA ∧ RahmenA HA ∧ KurzA κ.spur.length HA ∧
    F.rest.2.2.2.2.okG P (fussOrteG P F.f) ∧
    ReqAmEintritt P G.1 κ G.2.1 ∧
    GleichAuf ((P.requires G.1).orte ++ (P.ensures G.1).orte) κ G.2.2 ∧
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D),
      PasstV R H → PasstA O' HA → GleichRS O O' →
      FortV passes F G.1
        (zErg (execEnd (V := vertragVon D F.f) O' passes R (P.rumpf F.f) F.s0 F.rho)) R O'
        (R G.1 κ G.2.1)

def StapelG : (Σ f : D.Fn, Env D (D.params f) × World D) → List (RufRahmenG D) → Prop
  | _, [] => True
  | G, F :: rest => WarteG P O passes F G ∧ StapelG (RufSchluesselG F) rest

def FadenG (z : RufFadenG D) (W : World D) : Prop :=
  KopfG P O passes z.kopf W ∧ StapelG P O passes (RufSchluesselG z.kopf) z.stapel

def ZielInvG (M : RufMaschineG D) : Prop :=
  (∀ t, FadenG P O passes (M.faeden t) (M.weltVon t)) ∧ ∀ t, LogOk P (M.faeden t).log

end Inv

/-! ## 2. The steps of the replay -/

section Schritte

variable {P : Programm D} {O : Orakel D} {passes : Nat}

theorem kopfG_okG {F : RufRahmenG D} {W : World D} (h : KopfG P O passes F W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D F.f) l Γ Λ} (hr : F.rest = ⟨l, Γ, Λ, ρ, r⟩) :
    r.okG P (fussOrteG P F.f) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hok, _⟩ := h
  rw [hr] at hok
  exact hok

/-- **A head-local step without a new record** keeps the replay: the
    residue moves by a step of the frame semantics whose new prediction
    refines the old one. -/
theorem fadenG_lokalQ {z : RufFadenG D} {W W' : World D} (hF : FadenG P O passes z W)
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
    FadenG P O passes
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩ W' := by
  obtain ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hka, hg, hok, heq⟩, hS⟩ := hF
  have hok' : r.okG P (fussOrteG P z.kopf.f) := by rw [hr] at hok; exact hok
  obtain ⟨σ', hl, hg', hok'', hsem⟩ := hstep σ hg hok'
  refine ⟨⟨H, HA, σ', hreq, hf, hv, kurzV_mono hk hl, hfa, hra, kurzA_mono hka hl, hg', hok'',
    fun R O' hR hA hQ => ?_⟩, hS⟩
  have h1 := heq R O' hR hA hQ
  rw [hr] at h1
  exact ZErg.folgt_trans h1 (hsem R O' hQ)

/-- `fadenG_lokalQ` for a step whose frame semantics holds for every
    sequential oracle. -/
theorem fadenG_lokal {z : RufFadenG D} {W W' : World D} (hF : FadenG P O passes z W)
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
    FadenG P O passes
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩ W' :=
  fadenG_lokalQ hF hr ρ' r' spur' fun σ hg hok => by
    obtain ⟨σ', hl, hg', hok', hsem⟩ := hstep σ hg hok
    exact ⟨σ', hl, hg', hok', fun R O' _ => hsem R O'⟩

/-- Memory moved outside the head's footprint keeps the replay. -/
theorem fadenG_speicher {z : RufFadenG D} {W W' : World D} (hF : FadenG P O passes z W)
    (hw : ∀ c ∈ fussOrteG P z.kopf.f, TraegerGleich W'.speicher W.speicher c) :
    FadenG P O passes z W' := by
  obtain ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hka, hg, hok, heq⟩, hS⟩ := hF
  refine ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hka, ⟨fun t ht => ?_, fun g hg' => ?_⟩, hok,
    heq⟩, hS⟩
  · exact (hg.1 t ht).trans (hw (.inl t) ht).symm
  · exact (hg.2 g hg').trans (hw (.inr g) hg').symm

/-- **The return leg.** -/
theorem popG_ens (hO : GutO O) (hRL : RegLokal O) (hK : ∀ f, KoerperGutG P passes f) {G : RufRahmenG D}
    {W : World D} (hG : KopfG P O passes G W) {lr : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {r : GRest D (vertragVon D G.f) lr Γ Λ} (hr : G.rest = ⟨lr, Γ, Λ, ρ, r⟩)
    (e : ErgExpr D Γ Λ (vertragVon D G.f).erg) (he : e.orte ⊆ fussOrteG P G.f)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (σ : World D), (semV O' passes R r σ ρ).gleich
        (.zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ))) :
    EnsAmRueck P G.f G.s0 (W.lese Λ e.orte) G.rho
      (evalErg (W.lese Λ e.orte) e (W.lese Λ e.orte) ρ) := by
  obtain ⟨H, HA, σ, hreq, hf, hv, _, hfa, hra, _, hg, _, heq⟩ := hG
  have h1 := heq (rufAusV H) (orakelAus O HA) (rufAusV_passt hf) (orakelAus_passt O hfa)
    (gleichRS_orakelAus O HA)
  rw [hr] at h1
  simp only at h1
  have h2 := ZErg.folgt_zurueck (ZErg.folgt_trans h1 (ZErg.folgt_of_gleich (hsem _ _ σ)))
  obtain ⟨σ'', hex, hsg⟩ := zErg_gleich_zurueck h2
  have hE := (hK G.f (orakelAus O HA) (orakelAus_rahmen hO hra) (regLokal_orakelAus hRL HA) (rufAusV H)
    (rufAusV_respektiert hv) (rufAusV_ohneVorbedingung hv) G.s0 G.rho hreq).1 σ'' _ hex
  have hgl : GleichAuf (fussOrteG P G.f) (σ.lese Λ e.orte) (W.lese Λ e.orte) :=
    hg.lese Λ Λ e.orte e.orte
  rw [evalErg_gleichAuf e (fun _ h => he h) hgl ρ] at hE
  exact ens_transfer hE (GleichAuf.refl _ _)
    (GleichAuf.mono (fun _ h => fuss_ensG P G.f h) ((gleichAuf_SG hsg).trans hgl))

/-- **The call leg.** -/
theorem pushG_req (hO : GutO O) (hRL : RegLokal O) (hK : ∀ f, KoerperGutG P passes f) {F : RufRahmenG D}
    {H : List (EintragV D)} {HA : List (AxEintrag D)} {σ : World D}
    (hreq : ReqAmEintritt P F.f F.s0 F.rho) (hf : FunkV H) (hv : VertraegeOkV P H)
    (hfa : FunkA HA) (hra : RahmenA HA)
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
      have h1 := heq _ (orakelAus O HA) (torRuf_passtV (rufAusV_passt hf) hv)
        (orakelAus_passt O hfa) (gleichRS_orakelAus O HA)
      rw [hlogik _ _ _ htor] at h1
      have hex := zErg_gleich_logik (ZErg.folgt_logik h1)
      exact (hK F.f (orakelAus O HA) (orakelAus_rahmen hO hra) (regLokal_orakelAus hRL HA) (rufAusV H)
        (rufAusV_respektiert hv) (rufAusV_ohneVorbedingung hv) F.s0 F.rho hreq).2 g hex

/-- **The caller resumes** after its pending call to `G` was answered by
    `mk` (a normal answer, whose `ensures` holds at the machine's return
    world `s1`, or a reason): the answer is recorded at the pending key with
    the machine's memory and a fresh trace position, and the frame becomes a
    replayed head with the continuation `r'` chosen by the pop. -/
theorem popG_kopf (e0 : Ereignis D) {F : RufRahmenG D}
    {G : Σ f : D.Fn, Env D (D.params f) × World D}
    (hW : WarteG P O passes F G) (s1 : World D) (mk : World D → RufAusgang G.1)
    (hmk : (∃ v, (∀ σa, mk σa = .ok σa v) ∧ EnsAmRueck P G.1 G.2.2 s1 G.2.1 v) ∨
      (∃ r, ∀ σa, mk σa = .grund σa r))
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
      O'.wirkt a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
        (axWelt e0 a (σ.lese Λ args.orte) xm.1, xm.2) →
      (semV O' passes R r σ ρ).folgt
        (semV O' passes R r' (axWelt e0 a (σ.lese Λ args.orte) xm.1) ρ')) :
    FadenG P O passes
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩
      (xm.1.speicher.welt spur') := by
  obtain ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hka, hg, hok0, heq⟩, hS⟩ := hF
  have hok' : r.okG P (fussOrteG P z.kopf.f) := by rw [hr] at hok0; exact hok0
  have hlen : σ.spur.length ≤ (σ.lese Λ args.orte).spur.length := lese_laenge _ _ _
  refine ⟨⟨H, HA ++ [⟨a, σ.lese Λ args.orte,
      evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ,
      (axWelt e0 a (σ.lese Λ args.orte) xm.1, xm.2)⟩],
    axWelt e0 a (σ.lese Λ args.orte) xm.1, hreq, hf, hv,
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
  · have h1 := axWelt_gleichAuf e0 a (hg.lese Λ Λ args.orte args.orte) hxm
    exact ⟨fun t ht => h1.1 t ht, fun g hg' => h1.2 g hg'⟩
  · intro R O' hR hA hQ
    have h1 := heq R O' hR (passtA_append hA) hQ
    rw [hr] at h1
    exact ZErg.folgt_trans h1 (hsem O' R σ hQ.2.2 (hA _ _ _ _ (List.mem_append_right _ List.mem_cons_self)))

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
          have hfr := (hO a (W.lese Λ args.orte)
            (evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ')).1
          rw [← e1] at hfr
          refine fadenG_ax e0 hF hr ρ' K σ'.spur a args (fun h' => (hok h').2)
            (σ', (O.wirkt a (W.lese Λ args.orte)
              (evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ')).2) hfr ?_
          intro O' R σ hz hw
          rw [hsem]
          apply ZErg.folgt_of_eq
          simp only [execStmt, axiomAntwort, hw]
          simp only [(show O'.zeiger = O.zeiger from hz), hu]
          rfl
      | _ => simp [Stmt.istAxiom] at hax

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
