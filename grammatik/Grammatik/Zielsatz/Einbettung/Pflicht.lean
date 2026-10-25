import Grammatik.Zielsatz.Einbettung.Koerper

/-!
  File:      Grammatik/Zielsatz/Einbettung/Pflicht.lean
  Subject:   The contracts of `D` beside their images, the map from the keys, and the induced
             handlers in the classes of the user obligation (stage E3, part 1).

  * `req_E`, `ens_E` -- a `requires`/`ensures` of `D` holds exactly when its image does, on worlds
    that carry the same image memory.
  * `phiAus` -- a map from `D`-worlds to `D'`-worlds that repeats functional keys and carries every
    `D`-memory (`phiAus_passt`, `phiAus_treu`).
  * the induced handlers are in the classes `KoerperGutSA` quantifies over: the call handler
    respects the contracts and frames of `P` (`rufΦ_rahmen`) and blames no caller
    (`rufΦ_ohneVorbedingung`) or nothing at all (`rufΦ_ohneLogik`) when the `D'`-handler does not;
    the lock move is in `HavocOk`, the atomic environment in `HavocA`, the oracle respects the
    axiom frames, is register-local and meets the axiom ensures.
-/

namespace Gabbro.Grammatik.Einbettung

open Gabbro.Grammatik

variable {D D' : Deklaration}

theorem castE_castE {D₀ : Deklaration} {Γ₁ Γ₂ Γ₃ : Ctx} (h : Γ₁ = Γ₂) (h' : Γ₂ = Γ₃) (ρ : Env D₀ Γ₁) :
    castE h' (castE h ρ) = castE (h.trans h') ρ := by subst h; subst h'; rfl

theorem castE_self {D₀ : Deklaration} {Γ : Ctx} (h : Γ = Γ) (ρ : Env D₀ Γ) : castE h ρ = ρ := rfl

theorem castV_castV {D₀ : Deklaration} {e₁ e₂ e₃ : Option Ty} (h : e₁ = e₂) (h' : e₂ = e₃)
    (v : ErgVal D₀ e₁) : castV h' (castV h v) = castV (h.trans h') v := by subst h; subst h'; rfl

theorem castV_self {D₀ : Deklaration} {e : Option Ty} (h : e = e) (v : ErgVal D₀ e) : castV h v = v := rfl

theorem eval_umΛ {D₀ : Deklaration} {Γ : Ctx} {Λ Λ' : List (Res D₀)} {τ : Ty} (h : Λ = Λ')
    (e : Expr D₀ Γ Λ τ) (σ₀ σ : World D₀) (ρ : Env D₀ Γ) :
    eval σ₀ (Expr.umΛ h e) σ ρ = eval σ₀ e σ ρ := by subst h; rfl

namespace Einbettung

variable (E : Einbettung D D')

/-! ## Environments back in `D` -/

/-- An environment of a pointer-free scope, back in `D`. -/
def envZ : {Γ : Ctx} → (∀ τ ∈ Γ, τ.zeigerfrei = true) → Env D' (Γ.map E.tyE) → Env D Γ
  | [], _, .nil => .nil
  | τ :: _, h, .cons v ρ =>
      .cons (E.valZ τ (h τ (List.mem_cons.mpr (Or.inl rfl))) v)
        (envZ (fun τ' hτ' => h τ' (List.mem_cons.mpr (Or.inr hτ'))) ρ)

theorem envE_envZ : ∀ {Γ : Ctx} (h : ∀ τ ∈ Γ, τ.zeigerfrei = true) (ρ' : Env D' (Γ.map E.tyE)),
    E.envE (E.envZ h ρ') = ρ'
  | [], _, .nil => rfl
  | _ :: _, h, .cons v ρ => by
      show Env.cons _ _ = _
      rw [E.valE_valZ, envE_envZ _ ρ]

variable (hZ : ZeigerfreiD D) (hS : E.SigTreu)

/-- The actual parameters of an image function, back in `D`. -/
def parZ (g : D.Fn) (ρ' : Env D' (D'.params (E.fn g))) : Env D (D.params g) :=
  E.envZ (hZ.params g) (castE (paramsE hS g).symm ρ')

theorem paramsUm_parZ (g : D.Fn) (ρ' : Env D' (D'.params (E.fn g))) :
    E.paramsUm hS g (E.parZ hZ hS g ρ') = ρ' := by
  simp only [paramsUm, parZ, envE_envZ, castE_castE]
  rfl

/-! ## The map from the keys -/

/-- **A map repeating the keys**: a key's `D'`-world, else the `D`-memory around `ctx`. -/
noncomputable def phiAus (M : List (World D × World D')) (ctx : Speicher D') : World D → World D' :=
  fun σ =>
    haveI := Classical.propDecidable (∃ p ∈ M, p.1 = σ)
    if h : ∃ p ∈ M, p.1 = σ then (Classical.choose h).2 else (E.speicherE ctx σ.speicher).welt []

theorem phiAus_passt {M : List (World D × World D')} (hk : E.KeyOk M) (ctx : Speicher D') :
    Passt (E.phiAus M ctx) M := by
  intro p hp
  have hex : ∃ q ∈ M, q.1 = p.1 := ⟨p, hp, rfl⟩
  simp only [phiAus, dif_pos hex]
  obtain ⟨hq, he⟩ := Classical.choose_spec hex
  exact hk.2 _ hq p hp he

theorem phiAus_treu {M : List (World D × World D')} (hk : E.KeyOk M) (ctx : Speicher D') (σ : World D) :
    E.Treu σ.speicher (E.phiAus M ctx σ) := by
  unfold phiAus
  split
  · rename_i hex
    obtain ⟨hq, he⟩ := Classical.choose_spec hex
    have := hk.1 _ hq
    rw [he] at this
    exact this
  · exact E.treu_speicherE ctx σ.speicher []

/-! ## Contracts -/

theorem ergEnv_E {e e' : Option Ty} (he : e.map E.tyE = e') {Γ Γ' : Ctx} (hΓ : Γ.map E.tyE = Γ')
    (hc : (ErgCtx Γ e).map E.tyE = ErgCtx Γ' e') (v : ErgVal D e) (ρ : Env D Γ) :
    castE hc.symm (ergEnv e' (castV he (E.ergE e v)) (castE hΓ (E.envE ρ))) = E.envE (ergEnv e v ρ) := by
  subst he; subst hΓ
  cases e <;> rfl


section Vertraege

variable {P : Programm D} {P' : Programm D'} (hF : E.Fortsetzung hS P P')
include hF

theorem req_E {σ : World D} {σ' : World D'} (h : E.Treu σ.speicher σ') (g : D.Fn)
    (ρ : Env D (D.params g)) :
    wahr? (eval σ' (P'.requires (E.fn g)) σ' (E.paramsUm hS g ρ)) = wahr? (eval σ (P.requires g) σ ρ) := by
  rw [hF.requires]
  unfold requiresE
  rw [eval_umΓ, eval_umΛ]
  simp only [paramsUm, castE_castE, castE_self]
  rw [E.eval_exE h h]
  rfl

theorem ens_E {σ₀ σ : World D} {σ₀' σ' : World D'} (h₀ : E.Treu σ₀.speicher σ₀')
    (h : E.Treu σ.speicher σ') (g : D.Fn) (ρ : Env D (D.params g)) (v : ErgVal D (D.erg g)) :
    wahr? (eval σ₀' (P'.ensures (E.fn g)) σ' (ergEnv (D'.erg (E.fn g)) (castV (ergE_fn hS g) (E.ergE _ v))
        (E.paramsUm hS g ρ))) =
      wahr? (eval σ₀ (P.ensures g) σ (ergEnv (D.erg g) v ρ)) := by
  rw [hF.ensures]
  unfold ensuresE
  rw [eval_umΓ, eval_umΛ]
  simp only [paramsUm]
  rw [E.ergEnv_E (ergE_fn hS g) (paramsE hS g) (by rw [E.ergCtxE, paramsE hS g, ergE_fn hS g]),
    E.eval_exE h₀ h]
  rfl

end Vertraege


/-! ## Answers -/

theorem antwortR_ok {pad : List (Ereignis D)} {g : D.Fn} {σ : World D}
    {a : RufAusgang (D := D') (E.fn g)} {σa : World D} {v : ErgVal D (D.erg g)}
    (h : E.antwortR hZ hS pad g σ a = .ok σa v) :
    ∃ W v', a = .ok W v' ∧ σa = E.antwortWelt hZ pad σ W ∧
      v = E.ergZ (D.erg g) (hZ.erg g) (castV (ergE_fn hS g).symm v') := by
  cases a with
  | ok W v' =>
      simp only [antwortR, RufAusgang.ok.injEq] at h
      exact ⟨W, v', rfl, h.1.symm, h.2.symm⟩
  | why W r => simp only [antwortR, reduceCtorEq] at h
  | logik e => simp only [antwortR, reduceCtorEq] at h
  | hardware e => simp only [antwortR, reduceCtorEq] at h

theorem antwortR_logik {pad : List (Ereignis D)} {g : D.Fn} {σ : World D}
    {a : RufAusgang (D := D') (E.fn g)} {e : Logik D} (h : E.antwortR hZ hS pad g σ a = .logik e) :
    ∃ e', a = .logik e' ∧ e = E.logikZ e' := by
  cases a with
  | ok W v' => simp only [antwortR, reduceCtorEq] at h
  | why W r => simp only [antwortR, reduceCtorEq] at h
  | logik e' =>
      simp only [antwortR, RufAusgang.logik.injEq] at h
      exact ⟨e', rfl, h.symm⟩
  | hardware e => simp only [antwortR, reduceCtorEq] at h

theorem castV_ergE_ergZ (g : D.Fn) (v' : ErgVal D' (D'.erg (E.fn g))) :
    castV (ergE_fn hS g) (E.ergE _ (E.ergZ (D.erg g) (hZ.erg g) (castV (ergE_fn hS g).symm v'))) = v' := by
  rw [E.ergE_ergZ, castV_castV]; rfl

theorem logikZ_vorb {e' : Logik D'} {g : D.Fn} (h : E.logikZ e' = .vorbedingung g) :
    e' = .vorbedingung (E.fn g) := by
  cases e' with
  | vorbedingung g' =>
      cases hz : E.fnZ g' with
      | none => simp only [logikZ, hz, reduceCtorEq] at h
      | some g₀ =>
          simp only [logikZ, hz, Logik.vorbedingung.injEq] at h
          subst h
          rw [E.fn_fnZ g' _ hz]
  | _ => simp only [logikZ, reduceCtorEq] at h

theorem speicherZ_slots {W W' : World D'} {t : D.Tab} (hz : ZeigerfreiD D)
    (h : W.slots (E.tab t) = W'.slots (E.tab t)) :
    (E.speicherZ hz W.speicher).slots t = (E.speicherZ hz W'.speicher).slots t := by
  funext k f
  show E.valZ _ _ (castW _ (W.slots (E.tab t) k (E.feld t f))) = E.valZ _ _ (castW _ (W'.slots (E.tab t) k (E.feld t f)))
  rw [h]

theorem speicherZ_globs {W W' : World D'} {g : D.Glob} (hz : ZeigerfreiD D)
    (h : W.globs (E.glob g) = W'.globs (E.glob g)) :
    (E.speicherZ hz W.speicher).globs g = (E.speicherZ hz W'.speicher).globs g := by
  show E.valZ _ _ (castW _ (W.globs (E.glob g))) = E.valZ _ _ (castW _ (W'.globs (E.glob g)))
  rw [h]

/-- Two `D'`-worlds beside `D`-memories that agree on a table agree on its image. -/
theorem bild_slots {s₁ s₂ : Speicher D} {a b : World D'} (ha : E.Treu s₁ a) (hb : E.Treu s₂ b) {t : D.Tab}
    (h : s₁.slots t = s₂.slots t) : a.slots (E.tab t) = b.slots (E.tab t) := by
  funext k f'
  have key : ∀ f : D.Feld t, a.slots (E.tab t) k (E.feld t f) = b.slots (E.tab t) k (E.feld t f) :=
    fun f => castW_inj (E.typ t f) ((ha.1 t k f).trans (by rw [h]; exact (hb.1 t k f).symm))
  exact (E.feld_feldZ t f') ▸ key (E.feldZ t f')

theorem bild_globs {s₁ s₂ : Speicher D} {a b : World D'} (ha : E.Treu s₁ a) (hb : E.Treu s₂ b) {g : D.Glob}
    (h : s₁.globs g = s₂.globs g) : a.globs (E.glob g) = b.globs (E.glob g) :=
  castW_inj (E.gtyp g) ((ha.2 g).trans (by rw [h]; exact (hb.2 g).symm))

/-! ## The induced handlers are in the classes -/

section Klassen

variable {P : Programm D} {P' : Programm D'} (hF : E.Fortsetzung hS P P')
  {pad : List (Ereignis D)} (hp : PadOk pad) {Φ : World D → World D'}
  (hΦ : ∀ σ, E.Treu σ.speicher (Φ σ))

include hF hp hΦ in
/-- **The induced call handler respects the contracts and frames of `P`.** -/
theorem rufΦ_rahmen {R' : ∀ f : D'.Fn, World D' → Env D' (D'.params f) → RufAusgang f}
    (hR' : RespektiertRahmen P' R') : RespektiertRahmen P (E.rufΦ hZ hS pad Φ R') := by
  refine ⟨fun g σ ρ hreq σa v hok => ?_, fun g σ ρ σa v hok => ?_⟩
  · obtain ⟨W, v', ha, rfl, rfl⟩ := E.antwortR_ok hZ hS hok
    have hreq' : ReqAmEintritt P' (E.fn g) (Φ σ) (E.paramsUm hS g ρ) := by
      unfold ReqAmEintritt; rw [E.req_E hS hF (hΦ σ)]; exact hreq
    have := hR'.1 (E.fn g) (Φ σ) (E.paramsUm hS g ρ) hreq' W v' ha
    unfold EnsAmRueck at this ⊢
    rw [← E.castV_ergE_ergZ hZ hS g v', E.ens_E hS hF (hΦ σ) (E.treu_antwortWelt hZ pad σ W)] at this
    exact this
  · obtain ⟨W, v', ha, rfl, rfl⟩ := E.antwortR_ok hZ hS hok
    obtain ⟨hr1, hr2⟩ := hR'.2 (E.fn g) (Φ σ) (E.paramsUm hS g ρ) W v' ha
    refine ⟨⟨fun t ht k f => ?_, fun g' hg => ?_⟩, E.antwortWelt_offen hZ hp σ W⟩
    · have hw : D'.schreibt (E.fn g) (E.tab t) = false := by
        unfold Deklaration.schreibt; rw [hS.signatur]; simp only [sigE, E.tabZ_tab]; exact ht
      have e := hr1.1 (E.tab t) hw
      have e' : W.slots (E.tab t) = (Φ σ).slots (E.tab t) := funext fun k => funext fun f => e k f
      show (E.speicherZ hZ W.speicher).slots t k f = σ.slots t k f
      rw [E.speicherZ_slots hZ e', E.speicherZ_treu hZ (hΦ σ)]; rfl
    · have hw : D'.gschreibt (E.fn g) (E.glob g') = false := by
        unfold Deklaration.gschreibt; rw [hS.signatur]; simp only [sigE, E.globZ_glob]; exact hg
      have e := hr1.2 (E.glob g') hw
      show (E.speicherZ hZ W.speicher).globs g' = σ.globs g'
      rw [E.speicherZ_globs hZ e, E.speicherZ_treu hZ (hΦ σ)]; rfl

/-- The induced call handler blames no caller when the `D'`-handler does not. -/
theorem rufΦ_ohneVorbedingung {R' : ∀ f : D'.Fn, World D' → Env D' (D'.params f) → RufAusgang f}
    (hR' : OhneVorbedingung R') : OhneVorbedingung (E.rufΦ hZ hS pad Φ R') := by
  intro g σ ρ e h g' he
  obtain ⟨e', ha, rfl⟩ := E.antwortR_logik hZ hS h
  exact hR' (E.fn g) _ _ e' ha (E.fn g') (E.logikZ_vorb he)

/-- The induced call handler answers no `logik` outcome when the `D'`-handler does not. -/
theorem rufΦ_ohneLogik {R' : ∀ f : D'.Fn, World D' → Env D' (D'.params f) → RufAusgang f}
    (hR' : OhneLogik R') : OhneLogik (E.rufΦ hZ hS pad Φ R') := by
  intro g σ ρ e h
  obtain ⟨e', ha, rfl⟩ := E.antwortR_logik hZ hS h
  exact hR' (E.fn g) _ _ e' ha

include hF hΦ in
/-- **The gate commutes with the induction**: gating the `D'`-handler at the image contracts is
    gating the induced handler at the contracts of `P`. -/
theorem rufΦ_torRuf (R' : ∀ f : D'.Fn, World D' → Env D' (D'.params f) → RufAusgang f) :
    E.rufΦ hZ hS pad Φ (torRuf P' R') = torRuf P (E.rufΦ hZ hS pad Φ R') := by
  funext g σ ρ
  simp only [rufΦ, torRuf]
  rw [E.req_E hS hF (hΦ σ)]
  split
  · rfl
  · simp only [antwortR, E.logikZ_vorbedingung]

include hΦ in
/-- The induced lock move is in the class. -/
theorem umweltΦ_ok (S : SperrInv D) {S' : SperrInv D'} (hSL : ∀ L (s s' : Speicher D), (∀ c ∈ S.orte L, TraegerGleich s s' c) → S.inv L s = S.inv L s')
    (hSi : ∀ L s', S'.inv (E.lock L) s' = S.inv L (E.speicherZ hZ s')) {U' : Umwelt D'}
    (hU' : HavocOk S' U') : HavocOk S (E.umweltΦ hZ Φ S U') := by
  intro L σ
  refine ⟨rfl, fun c hc => mischU_aussen S L σ _ c hc, ?_⟩
  show S.inv L (mischU S L σ _).speicher = true
  rw [hSL L _ (E.speicherZ hZ (U' (E.lock L) (Φ σ)).speicher) (fun c hc => mischU_innen S L σ _ c hc),
    ← hSi]
  exact (hU' (E.lock L) (Φ σ)).2.2

/-- The induced atomic environment is in the class. -/
theorem aumweltΦ_ok (T : D.Tab ⊕ D.Glob → Prop) (A' : AUmwelt D') : HavocA T (E.aumweltΦ hZ Φ T A') :=
  fun X σ => ⟨mischT_spur T X σ _, fun _ hc => mischT_aussen σ _ hc⟩

include hΦ in
/-- The induced oracle respects the axiom frames. -/
theorem orakelΦ_rahmen {O' : Orakel D'} (hO' : RahmenO O') : RahmenO (E.orakelΦ hZ pad Φ O') := by
  intro a σ ρ
  obtain ⟨hr1, hr2⟩ := hO' (E.ax a) (Φ σ) (E.aparamsUm a ρ)
  refine ⟨fun t ht k f => ?_, fun g hg => ?_⟩
  · have hw : D'.aschreibt (E.ax a) (E.tab t) = false := by rw [E.aschreibt, E.tabZ_tab]; exact ht
    have e' : (O'.wirkt (E.ax a) (Φ σ) (E.aparamsUm a ρ)).1.slots (E.tab t) = (Φ σ).slots (E.tab t) :=
      funext fun k => funext fun f => hr1 (E.tab t) hw k f
    show (E.speicherZ hZ _).slots t k f = σ.slots t k f
    rw [E.speicherZ_slots hZ e', E.speicherZ_treu hZ (hΦ σ)]; rfl
  · have hw : D'.agschreibt (E.ax a) (E.glob g) = false := by rw [E.agschreibt, E.globZ_glob]; exact hg
    have e := hr2 (E.glob g) hw
    show (E.speicherZ hZ _).globs g = σ.globs g
    rw [E.speicherZ_globs hZ e, E.speicherZ_treu hZ (hΦ σ)]; rfl

include hΦ in
/-- The induced oracle is register-local. -/
theorem orakelΦ_regLokal {O' : Orakel D'} (hRL : RegLokal O') : RegLokal (E.orakelΦ hZ pad Φ O') := by
  refine ⟨fun r σ₁ σ₂ hg => ?_, fun g σ₁ σ₂ hg => ?_⟩
  · show O'.regLies (E.reg r) (Φ σ₁) = O'.regLies (E.reg r) (Φ σ₂)
    apply hRL.1
    rw [E.rtraeger]
    refine ⟨fun t' ht' => ?_, fun g' hg' => ?_⟩
    · obtain ⟨c, hc, he⟩ := List.mem_map.mp ht'
      rcases c with t | g
      · simp only [Sum.map_inl, Sum.inl.injEq] at he
        subst he
        exact E.bild_slots (hΦ σ₁) (hΦ σ₂) (hg.1 t hc)
      · simp only [Sum.map_inr, reduceCtorEq] at he
    · obtain ⟨c, hc, he⟩ := List.mem_map.mp hg'
      rcases c with t | g
      · simp only [Sum.map_inl, reduceCtorEq] at he
      · simp only [Sum.map_inr, Sum.inr.injEq] at he
        subst he
        exact E.bild_globs (hΦ σ₁) (hΦ σ₂) (hg.2 g hc)
  · show O'.sichtbar (E.glob g) (Φ σ₁) = O'.sichtbar (E.glob g) (Φ σ₂)
    apply hRL.2
    refine ⟨fun t' ht' => by simp at ht', fun g' hg' => ?_⟩
    rw [List.mem_singleton] at hg'
    cases hg'
    exact E.bild_globs (hΦ σ₁) (hΦ σ₂) (hg.2 g (List.mem_singleton.mpr rfl))

/-- The induced oracle meets the axiom ensures of `D`, when the `D'`-oracle meets their images. -/
theorem orakelΦ_axVertrag {O' : Orakel D'} {Q : AxEns D} {Q' : AxEns D'} (hQ' : AxVertragO Q' O')
    (hQ : ∀ a (W' : World D') (v : ErgVal D (D.aerg a)),
      Q' (E.ax a) W' (castV (E.aerg a).symm (E.ergE _ v)) = Q a ((E.speicherZ hZ W'.speicher).welt []) v)
    (hQL : AxEnsLokal Q) : AxVertragO Q (E.orakelΦ hZ pad Φ O') := by
  intro a σ ρ v hv
  have hw := E.axiom_wert hZ (fun _ => Option.none) O'.zeiger a
    (O'.wirkt (E.ax a) (Φ σ) (E.aparamsUm a ρ)).2 (E.aerg a)
  have hv' : einpassenErg (fun _ => Option.none) (D.aerg a) (O'.wirkt (E.ax a) (Φ σ) (E.aparamsUm a ρ)).2 =
      some v := hv
  rw [hv', Option.map_some] at hw
  have hq := hQ' (E.ax a) (Φ σ) (E.aparamsUm a ρ) _ hw
  rw [hQ] at hq
  show Q a (E.antwortWelt hZ pad σ _) v = true
  rw [← hq]
  exact hQL a _ _ v (fun _ _ => rfl) (fun _ _ => rfl)

end Klassen

end Einbettung

end Gabbro.Grammatik.Einbettung
