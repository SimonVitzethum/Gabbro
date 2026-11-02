module
public import Grammatik.Speichermodell.Atomar.AtomarReplay.T2.Teil1Basis

public import Grammatik.Speichermodell.Atomar.AtomarReplay.T1

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

section Schritte

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} {m : Mass D} {zyk : D.Fn → D.Fn → Bool}
/-- **The call leg** (as `pushS_req`), for a caller whose record repeats `HX`. -/
theorem pushSA_req (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hS : SperrInvOk S)
    {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f) {F : RufRahmenG D}
    {H : List (EintragV D)} {HA : List (AxEintrag D)} {HU : List (UEintrag D)}
    {HX : List (XEintrag D)} {σ : World D}
    (hreq : ReqAmEintritt P F.f F.s0 F.rho) (hf : FunkV H) (hv : VertraegeOkR P H)
    (hfa : FunkA HA) (hra : RahmenA HA) (hqa : VertragA O.zeiger Q HA) (hfu : FunkU HU)
    (hiu : InvU S HU) (hfx : FunkX HX)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    (r : GRest D (vertragVon D F.f) l Γ Λ)
    (heq : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
      (U : Umwelt D) (A : AUmwelt D), PasstV R H → PasstA O' HA → PasstU S U HU →
      PasstX Tg A HX → HavocA Tg A → GleichRS O O' →
      (zErgG (execEndHA (V := vertragVon D F.f) S O' U A passes R (P.rumpf F.f) F.s0 F.rho)).folgt
        (semHA S O' U A passes R r σ ρ))
    (g : D.Fn) (κ : World D) (ρk : Env D (D.params g))
    (hlogik : ∀ (O' : Orakel D) (U : Umwelt D) (A : AUmwelt D) R (e : Logik D),
      PasstX Tg A HX → HavocA Tg A → R g κ ρk = .logik e →
      semHA S O' U A passes R r σ ρ = .logik e) :
    ReqAmEintritt P g κ ρk := by
  cases hq : wahr? (eval κ (P.requires g) κ ρk) with
  | true => exact hq
  | false =>
      exfalso
      have htor : torRuf P (rufAusV H) g κ ρk = .logik (.vorbedingung g) := by
        simp only [torRuf, hq]
        rfl
      have hPX := umweltAusA_passt Tg hfx
      have hHA := umweltAusA_ok Tg HX
      have h1 := heq _ (orakelAus O HA) (umweltAus S sp HU) (umweltAusA Tg HX)
        (torRuf_passtV (rufAusV_passt hf) hv.1) (orakelAus_passt O hfa) (umweltAus_passt S sp hfu)
        hPX hHA (gleichRS_orakelAus O HA)
      rw [hlogik _ _ _ _ _ hPX hHA htor] at h1
      have hex := zErgG_gleich_logik (ZErgG.folgt_logik h1)
      exact ((hK F.f).1 (orakelAus O HA) (orakelAus_rahmen hO hra) (regLokal_orakelAus hRL HA)
        (orakelAus_vertrag hQ hqa) (umweltAus S sp HU) (umweltAus_ok hS hsp hiu)
        (umweltAusA Tg HX) hHA (rufAusV H) (rufAusV_rahmen hv) (rufAusV_ohneVorbedingung hv.1)
        F.s0 F.rho hreq).2 g hex

/-- **The measure leg** (T4, as `pushSA_req`): a call into the caller's own cycle has a smaller measure than the
    caller's entry. Were it not so, the measure gate would answer `abstieg` there, the replay would carry that to
    the caller's body, and the user's duty `MassPflicht` excludes it. -/
theorem pushSA_mass (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hS : SperrInvOk S)
    {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hM : ∀ f, MassPflicht P passes Q S Tg m zyk f) {F : RufRahmenG D}
    {H : List (EintragV D)} {HA : List (AxEintrag D)} {HU : List (UEintrag D)}
    {HX : List (XEintrag D)} {σ : World D}
    (hreq : ReqAmEintritt P F.f F.s0 F.rho) (hf : FunkV H) (hv : VertraegeOkR P H)
    (hm : MassOkV m (zyk F.f) (m.wert F.f F.s0 F.rho) H)
    (hfa : FunkA HA) (hra : RahmenA HA) (hqa : VertragA O.zeiger Q HA) (hfu : FunkU HU)
    (hiu : InvU S HU) (hfx : FunkX HX)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    (r : GRest D (vertragVon D F.f) l Γ Λ)
    (heq : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
      (U : Umwelt D) (A : AUmwelt D), PasstV R H → PasstA O' HA → PasstU S U HU →
      PasstX Tg A HX → HavocA Tg A → GleichRS O O' →
      (zErgG (execEndHA (V := vertragVon D F.f) S O' U A passes R (P.rumpf F.f) F.s0 F.rho)).folgt
        (semHA S O' U A passes R r σ ρ))
    (g : D.Fn) (κ : World D) (ρk : Env D (D.params g))
    (hlogik : ∀ (O' : Orakel D) (U : Umwelt D) (A : AUmwelt D) R (e : Logik D),
      PasstX Tg A HX → HavocA Tg A → R g κ ρk = .logik e →
      semHA S O' U A passes R r σ ρ = .logik e)
    (hz : zyk F.f g = true) :
    lexLt (m.wert g κ ρk) (m.wert F.f F.s0 F.rho) = true := by
  cases hlt : lexLt (m.wert g κ ρk) (m.wert F.f F.s0 F.rho) with
  | true => rfl
  | false =>
      exfalso
      have htor : massTor m (zyk F.f) (m.wert F.f F.s0 F.rho) (rufAusM H) g κ ρk = .logik (.abstieg g) := by
        simp only [massTor, hz, hlt, Bool.not_false, Bool.and_self, ↓reduceIte]
      have hPX := umweltAusA_passt Tg hfx
      have hHA := umweltAusA_ok Tg HX
      have h1 := heq _ (orakelAus O HA) (umweltAus S sp HU) (umweltAusA Tg HX)
        (massTor_passtV (rufAusM_passt hf) hm) (orakelAus_passt O hfa) (umweltAus_passt S sp hfu)
        hPX hHA (gleichRS_orakelAus O HA)
      rw [hlogik _ _ _ _ _ hPX hHA htor] at h1
      have hex := zErgG_gleich_logik (ZErgG.folgt_logik h1)
      exact hM F.f (orakelAus O HA) (orakelAus_rahmen hO hra) (regLokal_orakelAus hRL HA)
        (orakelAus_vertrag hQ hqa) (umweltAus S sp HU) (umweltAus_ok hS hsp hiu)
        (umweltAusA Tg HX) hHA (rufAusM H) (rufAusM_rahmen hv) (rufAusM_ohneAbstieg hv) (rufAusM_ohneVorbedingung hv)
        F.s0 F.rho hreq g hz hex

/-- **A returning head justifies its answer** (no event, as `popS_begr_ok`). -/
theorem popSA_begr_ok (hE : ¬ Nonempty (Ereignis D)) {G : RufRahmenG D} {W : World D}
    (hG : KopfSA P O passes Q S lok Tg m zyk G W) {lr : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {r : GRest D (vertragVon D G.f) lr Γ Λ} (hr : G.rest = ⟨lr, Γ, Λ, ρ, r⟩)
    (e : ErgExpr D Γ Λ (vertragVon D G.f).erg)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (A : AUmwelt D) (σ : World D), (semHA S O' U A passes R r σ ρ).gleich
        (.zurueck (leseA A σ Λ e.orte) (evalErg (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ))) :
    BegruendetA P O passes S
      ⟨G.f, G.s0, G.rho, .ok G.s0 (evalErg (W.lese Λ e.orte) e (W.lese Λ e.orte) ρ)⟩ := by
  obtain ⟨H, HA, HU, HX, σ, _, hf, _, _, hk, _, _, _, hka, _, _, _, _, _, _, heq⟩ := hG
  obtain rfl : σ = W := welt_eq hE σ W
  refine .mk _ _ _ _ H hf (hk.2 hE) (fun R U A hR => ?_)
  have h1 := heq R O U A hR (hka.2 hE) (passtU_leer hE S U HU) (passtX_leer hE Tg A HX)
    (havocA_leer hE Tg A) ⟨rfl, rfl, rfl⟩
  rw [hr] at h1
  simp only at h1
  have h2 := ZErgG.folgt_zurueck (ZErgG.folgt_trans h1 (ZErgG.folgt_of_gleich (hsem _ _ _ A σ)))
  obtain ⟨σ'', hex, _⟩ := zErgG_gleich_zurueck h2
  have e1 : leseA A σ Λ e.orte = σ.lese Λ e.orte := welt_eq hE _ _
  rw [e1] at hex
  exact ⟨σ'', hex⟩

/-- The same for a head at a REASON return. -/
theorem popSA_begr_grund (hE : ¬ Nonempty (Ereignis D)) {G : RufRahmenG D} {W : World D}
    (hG : KopfSA P O passes Q S lok Tg m zyk G W) {lr : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {r : GRest D (vertragVon D G.f) lr Γ Λ} (hr : G.rest = ⟨lr, Γ, Λ, ρ, r⟩)
    (rg : Fin (vertragVon D G.f).gruende)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (A : AUmwelt D) (σ : World D),
      (semHA S O' U A passes R r σ ρ).gleich (.why σ rg)) :
    BegruendetA P O passes S ⟨G.f, G.s0, G.rho, .why G.s0 rg⟩ := by
  obtain ⟨H, HA, HU, HX, σ, _, hf, _, _, hk, _, _, _, hka, _, _, _, _, _, _, heq⟩ := hG
  refine .mk _ _ _ _ H hf (hk.2 hE) (fun R U A hR => ?_)
  have h1 := heq R O U A hR (hka.2 hE) (passtU_leer hE S U HU) (passtX_leer hE Tg A HX)
    (havocA_leer hE Tg A) ⟨rfl, rfl, rfl⟩
  rw [hr] at h1
  simp only at h1
  have h2 := ZErgG.folgt_grund (ZErgG.folgt_trans h1 (ZErgG.folgt_of_gleich (hsem _ _ _ A σ)))
  obtain ⟨σ'', hex, _⟩ := zErgG_gleich_grund h2
  exact ⟨σ'', hex⟩

/-- **The caller resumes** (as `popS_kopf`). -/
theorem popSA_kopf {F : RufRahmenG D}
    {G : Σ f : D.Fn, Env D (D.params f) × World D}
    (hW : WarteSA P O passes Q S lok Tg m zyk F G) (s1 : World D) (mk : World D → RufAusgang G.1)
    (hmk : (∃ v, (∀ σa, mk σa = .ok σa v) ∧ EnsAmRueck P G.1 G.2.2 s1 G.2.1 v) ∨
      (∃ r, ∀ σa, mk σa = .why σa r))
    (hb : ¬ Nonempty (Ereignis D) → BegruendetA P O passes S ⟨G.1, G.2.2, G.2.1, mk G.2.2⟩)
    (hRah : GleichOhne G.1 (stabilS P S lok F.f F.rest.2.2.1) G.2.2 s1)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ' : Env D Γ) (r' : GRest D (vertragVon D F.f) l Γ Λ)
    (hΛ : ∀ L, Res.held L ∈ Λ → Res.held L ∈ F.rest.2.2.1)
    (hok' : F.rest.2.2.2.2.okS P (fussOrteG P F.f) (sicher P lok F.f) →
      r'.okS P (fussOrteG P F.f) (sicher P lok F.f))
    (hwahl : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
      (U : Umwelt D) (A : AUmwelt D) (σa : World D) (X : ZErgG (vertragVon D F.f)),
      FortSA passes S F G.1 X R O' U A (mk σa) → X.folgt (semHA S O' U A passes R r' σa ρ'))
    (W' : World D) (hW' : W'.slots = s1.slots ∧ W'.globs = s1.globs) :
    KopfSA P O passes Q S lok Tg m zyk ⟨F.f, F.rho, F.s0, ⟨l, Γ, Λ, ρ', r'⟩⟩ W' := by
  obtain ⟨H, HA, HU, HX, κ, hreq, hf, hv, hm, hk, hfa, hra, hqa, hka, hfu, hiu, hku, ⟨hfx, hkx⟩, hok,
    hreqκ, hmκ, ⟨hglκ, hsub, hfussκ⟩, hcont⟩ := hW
  have hσa : GleichAuf (stabilS P S lok F.f F.rest.2.2.1) (rahmenWeltF G.1 κ s1) s1 :=
    rahmenWeltF_gleichAuf G.1 hfussκ hRah
  have hlen := rahmenWeltF_laenge G.1 κ s1
  have hlt : Nonempty (Ereignis D) → κ.spur.length < (rahmenWeltF G.1 κ s1).spur.length :=
    fun hN => frischSpur_laenge hN κ.spur
  have hbe : ¬ Nonempty (Ereignis D) →
      BegruendetA P O passes S ⟨G.1, κ, G.2.1, mk (rahmenWeltF G.1 κ s1)⟩ := by
    intro hN
    rw [welt_eq hN (rahmenWeltF G.1 κ s1) G.2.2, welt_eq hN κ G.2.2]
    exact hb hN
  have hmem : (⟨G.1, κ, G.2.1, mk (rahmenWeltF G.1 κ s1)⟩ : EintragV D) ∈
      H ++ [⟨G.1, κ, G.2.1, mk (rahmenWeltF G.1 κ s1)⟩] :=
    List.mem_append_right _ List.mem_cons_self
  refine ⟨H ++ [⟨G.1, κ, G.2.1, mk (rahmenWeltF G.1 κ s1)⟩], HA, HU, HX, rahmenWeltF G.1 κ s1,
    hreq, funkV_appendBA hf hk _ (fun _ => Nat.le_refl _) hbe, ⟨?_, ?_⟩, ?_, ?_, hfa, hra, hqa,
    kurzAB_mono hka hlen, hfu, hiu, kurzUB_mono hku hlen, ⟨hfx, kurzX_mono hkx hlen⟩, ?_,
    hok' hok, ?_⟩
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
      have e : σ' = rahmenWeltF G.1 κ s1 := by
        rcases hmk with ⟨v, hv', _⟩ | ⟨rr, hr'⟩
        · rw [hv'] at hw; cases hw; rfl
        · rw [hr'] at hw; cases hw
      subst e
      exact ⟨rahmenWeltF_rahmen G.1 κ s1, rahmenWeltF_offen G.1 κ s1⟩
  · intro g σ ρ a hm' hz
    rcases List.mem_append.mp hm' with hm' | hm'
    · exact hm g σ ρ a hm' hz
    · rw [List.mem_singleton] at hm'
      cases hm'
      exact hmκ hz
  · refine ⟨fun hN e hm => ?_, fun hN e hm => ?_⟩
    · rcases List.mem_append.mp hm with hm | hm
      · exact Nat.lt_trans (hk.1 hN e hm) (hlt hN)
      · rw [List.mem_singleton] at hm
        subst hm
        exact hlt hN
    · rcases List.mem_append.mp hm with hm | hm
      · exact hk.2 hN e hm
      · rw [List.mem_singleton] at hm
        subst hm
        exact hbe hN
  · refine GleichAuf.mono (fun _ h => stabilS_mono hΛ h) ?_
    exact ⟨fun t ht => (hσa.1 t ht).trans (congrFun hW'.1.symm t),
      fun g hg => (hσa.2 g hg).trans (congrFun hW'.2.symm g)⟩
  · intro R O' U A hR hA hU hX hHA hQ
    have hans := hR _ _ _ _ hmem
    have hc := hcont R O' U A (passtV_append hR) hA hU hX hHA hQ
    rw [hans] at hc
    exact hwahl R O' U A _ _ hc


end Schritte
end Gabbro.Grammatik
