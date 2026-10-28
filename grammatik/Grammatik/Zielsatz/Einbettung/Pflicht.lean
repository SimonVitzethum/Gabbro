import Grammatik.Zielsatz.Einbettung.Koerper

/-!
  File:      Grammatik/Zielsatz/Einbettung/Pflicht.lean
  Subject:   The contracts of `D` beside their images, the map from the keys, and the induced
             handlers in the classes of the user obligation (stage E3, part 1).

  * `req_E`, `ens_E` -- a `requires`/`ensures` of `D` holds exactly when its image does, on worlds
    and environments beside each other.
  * `RueckVertrag` -- a function of `D'` outside the image that conforms to a signature keeps the
    frames and the contract of the signature's head (stage E4); `konform_vertrag` gives the same
    for every callee that may stand where `D` calls `g`.
  * `phiAus` -- a map from `D`-worlds to `D'`-worlds that repeats functional keys (main, atomic
    and call keys) and carries every `D`-memory (`phiAus_passt`, `phiAus_treu`).
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

variable (E : Einbettung D D') (hZ : E.Rueck)

/-! ## Environments back in `D` -/

/-- An environment of `D'` back in `D`, value by value (`valZ`). -/
def envZ : {Γ : Ctx} → Env D' (Γ.map E.tyE) → Env D Γ
  | [], .nil => .nil
  | τ :: _, .cons v ρ => .cons (E.valZ hZ τ v) (envZ ρ)

theorem envR_envZ : ∀ {Γ : Ctx} (ρ' : Env D' (Γ.map E.tyE)), E.EnvR hZ (E.envZ hZ ρ') ρ'
  | [], .nil => trivial
  | _ :: _, .cons v ρ => ⟨⟨rfl, E.vrel_valZ hZ _ v⟩, envR_envZ ρ⟩

variable (hS : E.SigTreu)

/-- The actual parameters of an image function, back in `D`. -/
def parZ (g : D.Fn) (ρ' : Env D' (D'.params (E.fn g))) : Env D (D.params g) :=
  E.envZ hZ (castE (paramsE hS g).symm ρ')

theorem envR_parZ (g : D.Fn) (ρ' : Env D' (D'.params (E.fn g))) : E.EnvR hZ (E.parZ hZ hS g ρ') ρ' :=
  (E.envR_um hZ (paramsE hS g).symm _ _).mp (E.envR_envZ hZ _)

/-! ## The map from the keys -/

/-- A map repeating a list of keys: a key's `D'`-world, else the `D`-memory around `ctx`. -/
noncomputable def phiListe (L : List (World D × World D')) (ctx : Speicher D') : World D → World D' :=
  fun σ =>
    haveI := Classical.propDecidable (∃ p ∈ L, p.1 = σ)
    if h : ∃ p ∈ L, p.1 = σ then (Classical.choose h).2 else (E.speicherE ctx σ.speicher).welt []

theorem phiListe_passt {L : List (World D × World D')} (hf : ∀ p ∈ L, ∀ q ∈ L, p.1 = q.1 → p.2 = q.2)
    (ctx : Speicher D') : ∀ p ∈ L, E.phiListe L ctx p.1 = p.2 := by
  intro p hp
  have hex : ∃ q ∈ L, q.1 = p.1 := ⟨p, hp, rfl⟩
  simp only [phiListe, dif_pos hex]
  obtain ⟨hq, he⟩ := Classical.choose_spec hex
  exact hf _ hq p hp he

theorem phiListe_treu {L : List (World D × World D')} (ht : ∀ p ∈ L, E.Treu hZ p.1.speicher p.2)
    (ctx : Speicher D') (σ : World D) : E.Treu hZ σ.speicher (E.phiListe L ctx σ) := by
  unfold phiListe
  split
  · rename_i hex
    obtain ⟨hq, he⟩ := Classical.choose_spec hex
    have := ht _ hq
    rw [he] at this
    exact this
  · exact E.treu_speicherE hZ ctx σ.speicher []

/-- A map repeating a list of call keys: a key's callee and arguments, else none. -/
noncomputable def phiRuf {X : Type} (L : List (World D × X)) : World D → Option X :=
  fun σ =>
    haveI := Classical.propDecidable (∃ p ∈ L, p.1 = σ)
    if h : ∃ p ∈ L, p.1 = σ then some (Classical.choose h).2 else none

theorem phiRuf_passt {X : Type} {L : List (World D × X)} (hf : ∀ p ∈ L, ∀ q ∈ L, p.1 = q.1 → p.2 = q.2) :
    ∀ p ∈ L, phiRuf L p.1 = some p.2 := by
  intro p hp
  have hex : ∃ q ∈ L, q.1 = p.1 := ⟨p, hp, rfl⟩
  simp only [phiRuf, dif_pos hex]
  obtain ⟨hq, he⟩ := Classical.choose_spec hex
  rw [hf _ hq p hp he]

/-- **The maps repeating the keys.** -/
noncomputable def phiAus (M : Keys D D') (ctx : Speicher D') : Phi D D' :=
  ⟨E.phiListe M.haupt ctx, E.phiListe M.atom ctx, phiRuf M.ruf⟩

theorem phiAus_passt {M : Keys D D'} (hk : E.KeyOk hZ M) (ctx : Speicher D') : Passt (E.phiAus M ctx) M :=
  ⟨E.phiListe_passt hk.2.1 ctx, E.phiListe_passt hk.2.2.2.1 ctx, phiRuf_passt hk.2.2.2.2⟩

theorem phiAus_treu {M : Keys D D'} (hk : E.KeyOk hZ M) (ctx : Speicher D') (σ : World D) :
    E.Treu hZ σ.speicher ((E.phiAus M ctx).haupt σ) :=
  E.phiListe_treu hZ hk.1 ctx σ

/-! ## Contracts -/

/-- A condition beside its image, in environments beside each other, has the same truth. -/
theorem wahr_rel {σ₀ σ : World D} {σ₀' σ' : World D'} (h₀ : E.Treu hZ σ₀.speicher σ₀')
    (h : E.Treu hZ σ.speicher σ') {Γ : Ctx} {Λ : List (Res D)} (c : Expr D Γ Λ .bool) (ρ : Env D Γ)
    (ρ' : Env D' (Γ.map E.tyE)) (hρ : E.EnvR hZ ρ ρ') :
    wahr? (eval σ₀' (exE E c) σ' ρ') = wahr? (eval σ₀ c σ ρ) := by
  have hv := E.eval_exE hZ h₀ h c ρ ρ' hρ
  simp only [VRel] at hv
  rw [hv]; rfl

theorem ergEnv_R {e e' : Option Ty} (he : e' = e.map E.tyE) {Γ Γ' : Ctx} (v : ErgVal D e)
    (v' : ErgVal D' e') (ρ : Env D Γ) (ρ' : Env D' Γ') (hv : E.ErgRel hZ e v (castV he v'))
    (hρ : E.EnvR hZ ρ ρ') : E.EnvR hZ (ergEnv e v ρ) (ergEnv e' v' ρ') := by
  subst he
  cases e with
  | none => exact hρ
  | some τ => exact ⟨⟨rfl, hv⟩, hρ⟩

section Vertraege

variable {P : Programm D} {P' : Programm D'} (hF : E.Fortsetzung hS P P')
include hF

theorem req_E {σ : World D} {σ' : World D'} (h : E.Treu hZ σ.speicher σ') (g : D.Fn)
    (ρ : Env D (D.params g)) (ρ' : Env D' (D'.params (E.fn g))) (hρ : E.EnvR hZ ρ ρ') :
    wahr? (eval σ' (P'.requires (E.fn g)) σ' ρ') = wahr? (eval σ (P.requires g) σ ρ) := by
  rw [hF.requires]
  unfold requiresE
  rw [eval_umΓ, eval_umΛ]
  exact E.wahr_rel hZ h h _ _ _ ((E.envR_um hZ _ _ _).mpr hρ)

theorem ens_E {σ₀ σ : World D} {σ₀' σ' : World D'} (h₀ : E.Treu hZ σ₀.speicher σ₀')
    (h : E.Treu hZ σ.speicher σ') (g : D.Fn) (ρ : Env D (D.params g)) (ρ' : Env D' (D'.params (E.fn g)))
    (hρ : E.EnvR hZ ρ ρ') (v : ErgVal D (D.erg g)) (v' : ErgVal D' (D'.erg (E.fn g)))
    (hv : E.ErgRel hZ (D.erg g) v (castV (ergE_fn hS g).symm v')) :
    wahr? (eval σ₀' (P'.ensures (E.fn g)) σ' (ergEnv (D'.erg (E.fn g)) v' ρ')) =
      wahr? (eval σ₀ (P.ensures g) σ (ergEnv (D.erg g) v ρ)) := by
  rw [hF.ensures]
  unfold ensuresE
  rw [eval_umΓ, eval_umΛ]
  exact E.wahr_rel hZ h₀ h _ _ _ ((E.envR_um hZ _ _ _).mpr
    (E.ergEnv_R hZ (ergE_fn hS g).symm v v' ρ ρ' hv hρ))

end Vertraege

/-! ## Callees outside the image -/

/-- **A conforming callee outside the image keeps the head's frames and contract** (stage E4):
    it writes only the images of what the head may write, its `requires` holds exactly where the
    head's does, and its `ensures` gives the head's on the restricted answer. -/
def RueckVertrag (pad : List (Ereignis D)) (P : Programm D) (P' : Programm D') : Prop :=
  ∀ (n : Nat) (g : D.Fn) (f' : D'.Fn) (hz : E.fnZ f' = none) (hr : hZ.rep n = some g)
    (hp : D'.passt f' (E.num n) = true),
    (∀ t, D.schreibt g t = false → D'.schreibt f' (E.tab t) = false) ∧
    (∀ x, D.gschreibt g x = false → D'.gschreibt f' (E.glob x) = false) ∧
    ∀ (σ : World D) (σ' : World D') (ρ : Env D (D.params g)) (a' : Env D' (D'.params f')),
      E.Treu hZ σ.speicher σ' → E.EnvR hZ ρ a' →
      wahr? (eval σ' (P'.requires f') σ' a') = wahr? (eval σ (P.requires g) σ ρ) ∧
      ∀ (W : World D') (v' : ErgVal D' (D'.erg f')),
        EnsAmRueck P' f' σ' W a' v' →
        EnsAmRueck P g σ (E.antwortWelt hZ pad σ W) ρ
          (E.ergZ hZ (D.erg g)
            (castV (konform_sig hS (show E.Konform hZ g f' from Or.inr ⟨n, hz, hr, hp⟩)).2.1 v'))

/-- **Every callee that may stand where `D` calls `g` keeps `g`'s frames and contract.** -/
theorem konform_vertrag {pad : List (Ereignis D)} {P : Programm D} {P' : Programm D'}
    (hF : E.Fortsetzung hS P P') (hV : E.RueckVertrag hZ hS pad P P') {g : D.Fn} {f' : D'.Fn}
    (hk : E.Konform hZ g f') {σ : World D} {σ' : World D'} (h : E.Treu hZ σ.speicher σ')
    {ρ : Env D (D.params g)} {a' : Env D' (D'.params f')} (hr : E.EnvR hZ ρ a') :
    wahr? (eval σ' (P'.requires f') σ' a') = wahr? (eval σ (P.requires g) σ ρ) ∧
    (∀ (W : World D') (v' : ErgVal D' (D'.erg f')), EnsAmRueck P' f' σ' W a' v' →
      EnsAmRueck P g σ (E.antwortWelt hZ pad σ W) ρ
        (E.ergZ hZ (D.erg g) (castV (konform_sig hS hk).2.1 v'))) ∧
    (∀ t, D.schreibt g t = false → D'.schreibt f' (E.tab t) = false) ∧
    (∀ x, D.gschreibt g x = false → D'.gschreibt f' (E.glob x) = false) := by
  rcases hk with rfl | ⟨n, hz, hrep, hp⟩
  · refine ⟨E.req_E hZ hS hF h g ρ a' hr, fun W v' he => ?_, fun t ht => ?_, fun x hx => ?_⟩
    · unfold EnsAmRueck at he ⊢
      rw [E.ens_E hZ hS hF h (E.treu_antwortWelt hZ pad σ W) g ρ a' hr _ v'
        (E.ergRel_ergZ hZ _ _)] at he
      exact he
    · unfold Deklaration.schreibt; rw [hS.signatur]; simp only [sigE, E.tabZ_tab]; exact ht
    · unfold Deklaration.gschreibt; rw [hS.signatur]; simp only [sigE, E.globZ_glob]; exact hx
  · obtain ⟨hw, hgw, hv⟩ := hV n g f' hz hrep hp
    obtain ⟨hq, hens⟩ := hv σ σ' ρ a' h hr
    exact ⟨hq, hens, hw, hgw⟩

/-! ## Answers -/

theorem antwortR_ok {pad : List (Ereignis D)} {g : D.Fn} {σ : World D} {f' : D'.Fn}
    {he : D'.erg f' = (D.erg g).map E.tyE} {hr : D'.gruende f' = D.gruende g}
    {a : RufAusgang f'} {σa : World D} {v : ErgVal D (D.erg g)}
    (h : E.antwortR hZ pad g σ he hr a = .ok σa v) :
    ∃ W v', a = .ok W v' ∧ σa = E.antwortWelt hZ pad σ W ∧ v = E.ergZ hZ (D.erg g) (castV he v') := by
  cases a with
  | ok W v' =>
      simp only [antwortR, RufAusgang.ok.injEq] at h
      exact ⟨W, v', rfl, h.1.symm, h.2.symm⟩
  | why W r => simp only [antwortR, reduceCtorEq] at h
  | logik e => simp only [antwortR, reduceCtorEq] at h
  | hardware e => simp only [antwortR, reduceCtorEq] at h

theorem antwortR_logik {pad : List (Ereignis D)} {g : D.Fn} {σ : World D} {f' : D'.Fn}
    {he : D'.erg f' = (D.erg g).map E.tyE} {hr : D'.gruende f' = D.gruende g}
    {a : RufAusgang f'} {e : Logik D} (h : E.antwortR hZ pad g σ he hr a = .logik e) :
    ∃ e', a = .logik e' ∧ e = logikZ g e' := by
  cases a with
  | ok W v' => simp only [antwortR, reduceCtorEq] at h
  | why W r => simp only [antwortR, reduceCtorEq] at h
  | logik e' =>
      simp only [antwortR, RufAusgang.logik.injEq] at h
      exact ⟨e', rfl, h.symm⟩
  | hardware e => simp only [antwortR, reduceCtorEq] at h

theorem logikZ_vorb {g g'' : D.Fn} {e' : Logik D'} (h : logikZ g e' = .vorbedingung g'') :
    ∃ g₀, e' = .vorbedingung g₀ := by
  cases e' <;> first | exact ⟨_, rfl⟩ | (simp only [logikZ, reduceCtorEq] at h)

/-- **The induced call handler at `g`** answers as some `D'`-callee that may stand for `g`, with
    arguments beside `g`'s, whatever the `D'`-handler. -/
theorem rufΦ_fall (pad : List (Ereignis D)) (Φ : Phi D D') (g : D.Fn) (σ : World D)
    (ρ : Env D (D.params g)) :
    ∃ (f' : D'.Fn) (a' : Env D' (D'.params f')) (hk : E.Konform hZ g f'), E.EnvR hZ ρ a' ∧
      ∀ R' : ∀ f : D'.Fn, World D' → Env D' (D'.params f) → RufAusgang f,
        E.rufΦ hZ hS pad Φ R' g σ ρ =
          E.antwortR hZ pad g σ (konform_sig hS hk).2.1 (konform_sig hS hk).2.2 (R' f' (Φ.haupt σ) a') := by
  have bild : E.EnvR hZ ρ (E.paramsUm hS g ρ) :=
    (E.envR_um hZ (paramsE hS g) _ _).mpr (E.envR_envE hZ ρ)
  unfold rufΦ
  cases hr : Φ.ruf σ with
  | none => exact ⟨E.fn g, E.paramsUm hS g ρ, Or.inl rfl, bild, fun R' => rfl⟩
  | some x =>
      obtain ⟨f', a'⟩ := x
      by_cases hc : E.EnvR hZ ρ a' ∧ E.Konform hZ g f'
      · exact ⟨f', a', hc.2, hc.1, fun R' => by simp only [dif_pos hc]⟩
      · exact ⟨E.fn g, E.paramsUm hS g ρ, Or.inl rfl, bild, fun R' => by simp only [dif_neg hc]⟩

theorem speicherZ_slots {W W' : World D'} {t : D.Tab}
    (h : W.slots (E.tab t) = W'.slots (E.tab t)) :
    (E.speicherZ hZ W.speicher).slots t = (E.speicherZ hZ W'.speicher).slots t := by
  funext k f
  show E.valZ hZ _ (castW _ (W.slots (E.tab t) k (E.feld t f))) =
    E.valZ hZ _ (castW _ (W'.slots (E.tab t) k (E.feld t f)))
  rw [h]

theorem speicherZ_globs {W W' : World D'} {g : D.Glob}
    (h : W.globs (E.glob g) = W'.globs (E.glob g)) :
    (E.speicherZ hZ W.speicher).globs g = (E.speicherZ hZ W'.speicher).globs g := by
  show E.valZ hZ _ (castW _ (W.globs (E.glob g))) = E.valZ hZ _ (castW _ (W'.globs (E.glob g)))
  rw [h]

/-- Two `D'`-worlds beside `D`-memories that agree on a pointer-free table agree on its image. -/
theorem bild_slots {s₁ s₂ : Speicher D} {a b : World D'} (ha : E.Treu hZ s₁ a) (hb : E.Treu hZ s₂ b)
    {t : D.Tab} (hf : ∀ f, (D.typ t f).zeigerfrei = true) (h : s₁.slots t = s₂.slots t) :
    a.slots (E.tab t) = b.slots (E.tab t) := by
  funext k f'
  have key : ∀ f : D.Feld t, a.slots (E.tab t) k (E.feld t f) = b.slots (E.tab t) k (E.feld t f) :=
    fun f => castW_inj (E.typ t f) (((E.vrel_frei hZ _ (hf f) _ _).mp (ha.1 t k f)).trans
      (by rw [h]; exact ((E.vrel_frei hZ _ (hf f) _ _).mp (hb.1 t k f)).symm))
  exact (E.feld_feldZ t f') ▸ key (E.feldZ t f')

theorem bild_globs {s₁ s₂ : Speicher D} {a b : World D'} (ha : E.Treu hZ s₁ a) (hb : E.Treu hZ s₂ b)
    {g : D.Glob} (hf : (D.gtyp g).zeigerfrei = true) (h : s₁.globs g = s₂.globs g) :
    a.globs (E.glob g) = b.globs (E.glob g) :=
  castW_inj (E.gtyp g) (((E.vrel_frei hZ _ hf _ _).mp (ha.2 g)).trans
    (by rw [h]; exact ((E.vrel_frei hZ _ hf _ _).mp (hb.2 g)).symm))

/-! ## The induced handlers are in the classes -/

section Klassen

variable {P : Programm D} {P' : Programm D'} (hF : E.Fortsetzung hS P P')
  {pad : List (Ereignis D)} (hp : PadOk pad) (hV : E.RueckVertrag hZ hS pad P P') {Φ : Phi D D'}
  (hΦ : ∀ σ, E.Treu hZ σ.speicher (Φ.haupt σ))

include hF hp hV hΦ in
/-- **The induced call handler respects the contracts and frames of `P`.** -/
theorem rufΦ_rahmen {R' : ∀ f : D'.Fn, World D' → Env D' (D'.params f) → RufAusgang f}
    (hR' : RespektiertRahmen P' R') : RespektiertRahmen P (E.rufΦ hZ hS pad Φ R') := by
  refine ⟨fun g σ ρ hreq σa v hok => ?_, fun g σ ρ σa v hok => ?_⟩
  · obtain ⟨f', a', hk, hr, hfall⟩ := E.rufΦ_fall hZ hS pad Φ g σ ρ
    rw [hfall] at hok
    obtain ⟨W, v', ha, rfl, rfl⟩ := E.antwortR_ok hZ hok
    obtain ⟨hq, hens, -, -⟩ := E.konform_vertrag hZ hS hF hV hk (hΦ σ) hr
    have hreq' : ReqAmEintritt P' f' (Φ.haupt σ) a' := by
      unfold ReqAmEintritt; rw [hq]; exact hreq
    exact hens W v' (hR'.1 f' (Φ.haupt σ) a' hreq' W v' ha)
  · obtain ⟨f', a', hk, hr, hfall⟩ := E.rufΦ_fall hZ hS pad Φ g σ ρ
    rw [hfall] at hok
    obtain ⟨W, v', ha, rfl, rfl⟩ := E.antwortR_ok hZ hok
    obtain ⟨-, -, hwt, hwg⟩ := E.konform_vertrag hZ hS hF hV hk (hΦ σ) hr
    obtain ⟨hr1, -⟩ := hR'.2 f' (Φ.haupt σ) a' W v' ha
    refine ⟨⟨fun t ht k f => ?_, fun g' hg => ?_⟩, E.antwortWelt_offen hZ hp σ W⟩
    · have e := hr1.1 (E.tab t) (hwt t ht)
      have e' : W.slots (E.tab t) = (Φ.haupt σ).slots (E.tab t) := funext fun k => funext fun f => e k f
      show (E.speicherZ hZ W.speicher).slots t k f = σ.slots t k f
      rw [E.speicherZ_slots hZ e', E.speicherZ_treu (hΦ σ)]; rfl
    · have e := hr1.2 (E.glob g') (hwg g' hg)
      show (E.speicherZ hZ W.speicher).globs g' = σ.globs g'
      rw [E.speicherZ_globs hZ e, E.speicherZ_treu (hΦ σ)]; rfl

/-- The induced call handler blames no caller when the `D'`-handler does not. -/
theorem rufΦ_ohneVorbedingung {R' : ∀ f : D'.Fn, World D' → Env D' (D'.params f) → RufAusgang f}
    (hR' : OhneVorbedingung R') : OhneVorbedingung (E.rufΦ hZ hS pad Φ R') := by
  intro g σ ρ e h g' he
  obtain ⟨f', a', hk, -, hfall⟩ := E.rufΦ_fall hZ hS pad Φ g σ ρ
  rw [hfall] at h
  obtain ⟨e', ha, rfl⟩ := E.antwortR_logik hZ h
  obtain ⟨g₀, rfl⟩ := logikZ_vorb he
  exact hR' f' _ _ _ ha g₀ rfl

/-- The induced call handler answers no `logik` outcome when the `D'`-handler does not. -/
theorem rufΦ_ohneLogik {R' : ∀ f : D'.Fn, World D' → Env D' (D'.params f) → RufAusgang f}
    (hR' : OhneLogik R') : OhneLogik (E.rufΦ hZ hS pad Φ R') := by
  intro g σ ρ e h
  obtain ⟨f', a', hk, -, hfall⟩ := E.rufΦ_fall hZ hS pad Φ g σ ρ
  rw [hfall] at h
  obtain ⟨e', ha, rfl⟩ := E.antwortR_logik hZ h
  exact hR' f' _ _ e' ha

include hF hV hΦ in
/-- **The gate commutes with the induction**: gating the `D'`-handler at the contracts of `P'` is
    gating the induced handler at the contracts of `P`. -/
theorem rufΦ_torRuf (R' : ∀ f : D'.Fn, World D' → Env D' (D'.params f) → RufAusgang f) :
    E.rufΦ hZ hS pad Φ (torRuf P' R') = torRuf P (E.rufΦ hZ hS pad Φ R') := by
  funext g σ ρ
  obtain ⟨f', a', hk, hr, hfall⟩ := E.rufΦ_fall hZ hS pad Φ g σ ρ
  have hq := (E.konform_vertrag hZ hS hF hV hk (hΦ σ) hr).1
  simp only [torRuf, hfall, hq]
  split
  · rfl
  · simp only [antwortR, logikZ]

include hΦ in
/-- The induced lock move is in the class. -/
theorem umweltΦ_ok (S : SperrInv D) {S' : SperrInv D'} (hSL : ∀ L (s s' : Speicher D), (∀ c ∈ S.orte L, TraegerGleich s s' c) → S.inv L s = S.inv L s')
    (hSi : ∀ L s', S'.inv (E.lock L) s' = S.inv L (E.speicherZ hZ s')) {U' : Umwelt D'}
    (hU' : HavocOk S' U') : HavocOk S (E.umweltΦ hZ Φ S U') := by
  intro L σ
  refine ⟨rfl, fun c hc => mischU_aussen S L σ _ c hc, ?_⟩
  show S.inv L (mischU S L σ _).speicher = true
  rw [hSL L _ (E.speicherZ hZ (U' (E.lock L) (Φ.haupt σ)).speicher) (fun c hc => mischU_innen S L σ _ c hc),
    ← hSi]
  exact (hU' (E.lock L) (Φ.haupt σ)).2.2

/-- The induced atomic environment is in the class. -/
theorem aumweltΦ_ok (T : D.Tab ⊕ D.Glob → Prop) (A' : AUmwelt D') : HavocA T (E.aumweltΦ hZ Φ T A') :=
  fun X σ => ⟨mischT_spur T X σ _, fun _ hc => mischT_aussen σ _ hc⟩

include hΦ in
/-- The induced oracle respects the axiom frames. -/
theorem orakelΦ_rahmen {O' : Orakel D'} (hO' : RahmenO O') : RahmenO (E.orakelΦ hZ pad Φ O') := by
  intro a σ ρ
  obtain ⟨hr1, hr2⟩ := hO' (E.ax a) (Φ.haupt σ) (E.aparamsUm a ρ)
  refine ⟨fun t ht k f => ?_, fun g hg => ?_⟩
  · have hw : D'.aschreibt (E.ax a) (E.tab t) = false := by rw [E.aschreibt, E.tabZ_tab]; exact ht
    have e' : (O'.wirkt (E.ax a) (Φ.haupt σ) (E.aparamsUm a ρ)).1.slots (E.tab t) = (Φ.haupt σ).slots (E.tab t) :=
      funext fun k => funext fun f => hr1 (E.tab t) hw k f
    show (E.speicherZ hZ _).slots t k f = σ.slots t k f
    rw [E.speicherZ_slots hZ e', E.speicherZ_treu (hΦ σ)]; rfl
  · have hw : D'.agschreibt (E.ax a) (E.glob g) = false := by rw [E.agschreibt, E.globZ_glob]; exact hg
    have e := hr2 (E.glob g) hw
    show (E.speicherZ hZ _).globs g = σ.globs g
    rw [E.speicherZ_globs hZ e, E.speicherZ_treu (hΦ σ)]; rfl

include hΦ in
/-- The induced oracle is register-local: the carriers of a register hold no function pointer
    (`AntwortFrei.regFrei`), and the visibility of a pointer-carrying global is constant. -/
theorem orakelΦ_regLokal {O' : Orakel D'} (hRL : RegLokal O') : RegLokal (E.orakelΦ hZ pad Φ O') := by
  refine ⟨fun r σ₁ σ₂ hg => ?_, fun g σ₁ σ₂ hg => ?_⟩
  · show O'.regLies (E.reg r) (Φ.haupt σ₁) = O'.regLies (E.reg r) (Φ.haupt σ₂)
    apply hRL.1
    rw [E.rtraeger]
    refine ⟨fun t' ht' => ?_, fun g' hg' => ?_⟩
    · obtain ⟨c, hc, he⟩ := List.mem_map.mp ht'
      rcases c with t | g
      · simp only [Sum.map_inl, Sum.inl.injEq] at he
        subst he
        exact E.bild_slots hZ (hΦ σ₁) (hΦ σ₂) (hZ.frei.regFrei r t hc) (hg.1 t hc)
      · simp only [Sum.map_inr, reduceCtorEq] at he
    · obtain ⟨c, hc, he⟩ := List.mem_map.mp hg'
      rcases c with t | g
      · simp only [Sum.map_inl, reduceCtorEq] at he
      · simp only [Sum.map_inr, Sum.inr.injEq] at he
        subst he
        exact E.bild_globs hZ (hΦ σ₁) (hΦ σ₂) (hZ.frei.regFreiG r g hc) (hg.2 g hc)
  · show (if (D.gtyp g).zeigerfrei = true then O'.sichtbar (E.glob g) (Φ.haupt σ₁) else true) =
      (if (D.gtyp g).zeigerfrei = true then O'.sichtbar (E.glob g) (Φ.haupt σ₂) else true)
    by_cases hz : (D.gtyp g).zeigerfrei = true
    · simp only [hz, if_true]
      apply hRL.2
      refine ⟨fun t' ht' => by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at ht', fun g' hg' => ?_⟩
      rw [List.mem_singleton] at hg'
      cases hg'
      exact E.bild_globs hZ (hΦ σ₁) (hΦ σ₂) hz (hg.2 g (List.mem_singleton.mpr rfl))
    · simp only [hz, Bool.false_eq_true, ↓reduceIte]

/-- The induced oracle meets the axiom ensures of `D`, when the `D'`-oracle meets their images. -/
theorem orakelΦ_axVertrag {O' : Orakel D'} {Q : AxEns D} {Q' : AxEns D'} (hQ' : AxVertragO Q' O')
    (hQ : ∀ a (W' : World D') (v : ErgVal D (D.aerg a)),
      Q' (E.ax a) W' (castV (E.aerg a).symm (E.ergE _ v)) = Q a ((E.speicherZ hZ W'.speicher).welt []) v)
    (hQL : AxEnsLokal Q) : AxVertragO Q (E.orakelΦ hZ pad Φ O') := by
  intro a σ ρ v hv
  have hw := E.axiom_wert hZ (fun _ => Option.none) O'.zeiger a
    (O'.wirkt (E.ax a) (Φ.haupt σ) (E.aparamsUm a ρ)).2 (E.aerg a)
  have hv' : einpassenErg (fun _ => Option.none) (D.aerg a) (O'.wirkt (E.ax a) (Φ.haupt σ) (E.aparamsUm a ρ)).2 =
      some v := hv
  rw [hv', Option.map_some] at hw
  have hq := hQ' (E.ax a) (Φ.haupt σ) (E.aparamsUm a ρ) _ hw
  rw [hQ] at hq
  show Q a (E.antwortWelt hZ pad σ _) v = true
  rw [← hq]
  exact hQL a _ _ v (fun _ _ => rfl) (fun _ _ => rfl)

end Klassen

end Einbettung

end Gabbro.Grammatik.Einbettung
