/- Part 2 of 3 of `AtomarReplay` (split by instrumente/teile/lean-teilen.py; the umbrella `AtomarReplay.lean` imports all parts). -/
import Grammatik.Speichermodell.Atomar.AtomarReplay.T1

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Schritte

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop}

theorem kopfSA_okS {F : RufRahmenG D} {W : World D} (h : KopfSA P O passes Q S lok Tg F W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D F.f) l Γ Λ} (hr : F.rest = ⟨l, Γ, Λ, ρ, r⟩) :
    r.okS P (fussOrteG P F.f) (sicher P lok F.f) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hok, _⟩ := h
  rw [hr] at hok
  exact hok

/-- **A head-local step** (as `fadenS_lokalQ`): the step may extend the record of atomic reads
    (a read of a shared atomic), and its residue semantics is followed for every environment
    repeating the extended record. -/
theorem fadenSA_lokalQ {z : RufFadenG D} {W W' : World D}
    (hF : FadenSA P O passes Q S lok Tg z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    {l' : Bool} {Γ' : Ctx} {Λ' : List (Res D)} (ρ' : Env D Γ')
    (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (spur' : List (Ereignis D))
    (hstep : ∀ (σ : World D) (HX : List (XEintrag D)), FunkX HX → KurzX σ.spur.length HX →
      GleichAuf (stabilS P S lok z.kopf.f Λ) σ W →
      r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      ∃ (σ' : World D) (HX' : List (XEintrag D)), FunkX HX' ∧ KurzX σ'.spur.length HX' ∧
        (∀ e ∈ HX, e ∈ HX') ∧
        σ.spur.length ≤ σ'.spur.length ∧ GleichAuf (stabilS P S lok z.kopf.f Λ') σ' W' ∧
        r'.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) ∧
        ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
          (U : Umwelt D) (A : AUmwelt D), PasstX Tg A HX' → HavocA Tg A → GleichRS O O' →
          (semHA S O' U A passes R r σ ρ).folgt (semHA S O' U A passes R r' σ' ρ')) :
    FadenSA P O passes Q S lok Tg
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩ W' := by
  obtain ⟨⟨H, HA, HU, HX, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hfu, hiu, hku, ⟨hfx, hkx⟩, hg,
    hok, heq⟩, hS⟩ := hF
  have hok' : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) := by rw [hr] at hok; exact hok
  have hg0 : GleichAuf (stabilS P S lok z.kopf.f Λ) σ W := by rw [hr] at hg; exact hg
  obtain ⟨σ', HX', hfx', hkx', hsub, hl, hg', hok'', hsem⟩ := hstep σ HX hfx hkx hg0 hok'
  refine ⟨⟨H, HA, HU, HX', σ', hreq, hf, hv, kurzVBA_mono hk hl, hfa, hra, hqa, kurzAB_mono hka hl,
    hfu, hiu, kurzUB_mono hku hl, ⟨hfx', hkx'⟩, hg', hok'', fun R O' U A hR hA hU hX hHA hQ => ?_⟩,
    hS⟩
  have h1 := heq R O' U A hR hA hU (passtX_teil hsub hX) hHA hQ
  rw [hr] at h1
  exact ZErgG.folgt_trans h1 (hsem R O' U A hX hHA hQ)

/-- A head-local step with no read of a shared atomic and a semantics that holds for every
    oracle and environment (the record stays). -/
theorem fadenSA_lokal {z : RufFadenG D} {W W' : World D}
    (hF : FadenSA P O passes Q S lok Tg z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    {l' : Bool} {Γ' : Ctx} {Λ' : List (Res D)} (ρ' : Env D Γ')
    (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (spur' : List (Ereignis D))
    (hstep : ∀ σ : World D, GleichAuf (stabilS P S lok z.kopf.f Λ) σ W →
      r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      σ.spur.length = σ.spur.length ∧ GleichAuf (stabilS P S lok z.kopf.f Λ') σ W' ∧
        r'.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) ∧
        ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
          (U : Umwelt D) (A : AUmwelt D),
          (semHA S O' U A passes R r σ ρ).folgt (semHA S O' U A passes R r' σ ρ')) :
    FadenSA P O passes Q S lok Tg
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩ W' :=
  fadenSA_lokalQ hF hr ρ' r' spur' fun σ HX hfx hkx hg hok => by
    obtain ⟨_, hg', hok', hsem⟩ := hstep σ hg hok
    exact ⟨σ, HX, hfx, hkx, fun _ h => h, Nat.le_refl _, hg', hok',
      fun R O' U A _ _ _ => hsem R O' U A⟩

/-- **A head-local step that READS the list `X`** (every carrier of it stable or a shared
    atomic): the read is recorded, the sequential world after it holds the machine's presented
    values at the read shared atomics (`mischT`), and the step continues from there. -/
theorem fadenSA_lese {z : RufFadenG D} {W W' : World D}
    (hF : FadenSA P O passes Q S lok Tg z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    {l' : Bool} {Γ' : Ctx} {Λ' : List (Res D)} (ρ' : Env D Γ')
    (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (spur' : List (Ereignis D))
    (Λr : List (Res D)) (X : List (D.Tab ⊕ D.Glob))
    (hX : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      ∀ c ∈ X, c ∈ stabilS P S lok z.kopf.f Λ ∨ Tg c)
    (hstep : ∀ σ : World D, GleichAuf (stabilS P S lok z.kopf.f Λ ++ X) σ (W.lese Λr X) →
      r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      ∃ σ' : World D, σ.spur.length ≤ σ'.spur.length ∧
        GleichAuf (stabilS P S lok z.kopf.f Λ') σ' W' ∧
        r'.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) ∧
        ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
          (U : Umwelt D) (A : AUmwelt D) (σ0 : World D), GleichRS O O' →
          GleichAuf (stabilS P S lok z.kopf.f Λ) σ0 W → leseA A σ0 Λr X = σ →
          (semHA S O' U A passes R r σ0 ρ).folgt (semHA S O' U A passes R r' σ' ρ')) :
    FadenSA P O passes Q S lok Tg
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩ W' := by
  refine fadenSA_lokalQ hF hr ρ' r' spur' fun σ HX hfx hkx hg hok => ?_
  obtain ⟨HX', hfx', hkx', hsub, hrec⟩ := lese_schritt Tg hfx hkx Λr X W.speicher
  have hgX := mischT_gleichAuf hg (hX hok) Λr Λr
  obtain ⟨σ', hl, hg', hok', hsem⟩ := hstep _ hgX hok
  refine ⟨σ', HX', hfx', kurzX_mono hkx' hl, hsub, Nat.le_trans (lese_laenge σ Λr X) hl, hg', hok',
    fun R O' U A hPX hHA hQ => hsem R O' U A σ hQ hg (hrec A hPX hHA)⟩

/-- Memory moved outside the head's stable carriers keeps the replay. -/
theorem fadenSA_speicher {z : RufFadenG D} {W W' : World D}
    (hF : FadenSA P O passes Q S lok Tg z W)
    (hw : ∀ c ∈ stabilS P S lok z.kopf.f z.kopf.rest.2.2.1,
      TraegerGleich W'.speicher W.speicher c) :
    FadenSA P O passes Q S lok Tg z W' := by
  obtain ⟨⟨H, HA, HU, HX, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hfu, hiu, hku, hx, hg, hok,
    heq⟩, hS⟩ := hF
  refine ⟨⟨H, HA, HU, HX, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hfu, hiu, hku, hx,
    ⟨fun t ht => ?_, fun g hg' => ?_⟩, hok, heq⟩, hS⟩
  · exact (hg.1 t ht).trans (hw (.inl t) ht).symm
  · exact (hg.2 g hg').trans (hw (.inr g) hg').symm

/-- **The return leg** (as `popS_ens`): the returned expression may read shared atomics; the
    read is answered by a record made here. -/
theorem popSA_ens (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hS : SperrInvOk S)
    {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f) {G : RufRahmenG D}
    {W : World D} (hG : KopfSA P O passes Q S lok Tg G W) {lr : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {ρ : Env D Γ} {r : GRest D (vertragVon D G.f) lr Γ Λ}
    (hr : G.rest = ⟨lr, Γ, Λ, ρ, r⟩)
    (e : ErgExpr D Γ Λ (vertragVon D G.f).erg)
    (he : ∀ c ∈ e.orte, c ∈ stabilS P S lok G.f Λ ∨ Tg c)
    (hens : (P.ensures G.f).orte ⊆ stabilS P S lok G.f Λ)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (A : AUmwelt D) (σ : World D), (semHA S O' U A passes R r σ ρ).gleich
        (.zurueck (leseA A σ Λ e.orte) (evalErg (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ))) :
    EnsAmRueck P G.f G.s0 (W.lese Λ e.orte) G.rho
      (evalErg (W.lese Λ e.orte) e (W.lese Λ e.orte) ρ) := by
  obtain ⟨H, HA, HU, HX, σ, hreq, hf, hv, _, hfa, hra, hqa, _, hfu, hiu, _, ⟨hfx, hkx⟩, hg, _,
    heq⟩ := hG
  obtain ⟨HX', hfx', _, hsub, hrec⟩ := lese_schritt Tg hfx hkx Λ e.orte W.speicher
  have hPX := umweltAusA_passt Tg hfx'
  have hHA := umweltAusA_ok Tg HX'
  have h1 := heq (rufAusV H) (orakelAus O HA) (umweltAus S sp HU) (umweltAusA Tg HX')
    (rufAusV_passt hf) (orakelAus_passt O hfa) (umweltAus_passt S sp hfu) (passtX_teil hsub hPX)
    hHA (gleichRS_orakelAus O HA)
  rw [hr] at h1 hg
  simp only at h1 hg
  have h2 := ZErgG.folgt_zurueck (ZErgG.folgt_trans h1
    (ZErgG.folgt_of_gleich (hsem _ _ _ (umweltAusA Tg HX') σ)))
  obtain ⟨σ'', hex, hsg⟩ := zErgG_gleich_zurueck h2
  have hE := ((hK G.f).1 (orakelAus O HA) (orakelAus_rahmen hO hra) (regLokal_orakelAus hRL HA)
    (orakelAus_vertrag hQ hqa) (umweltAus S sp HU) (umweltAus_ok hS hsp hiu) (umweltAusA Tg HX')
    hHA (rufAusV H) (rufAusV_rahmen hv) (rufAusV_ohneVorbedingung hv.1) G.s0 G.rho hreq).1 σ'' _ hex
  rw [hrec _ hPX hHA] at hE hsg
  have hgl := mischT_gleichAuf hg he Λ Λ
  rw [evalErg_gleichAuf e (fun _ h => List.mem_append_right _ h) hgl ρ] at hE
  exact ens_transfer hE (GleichAuf.refl _ _)
    (GleichAuf.mono (fun _ h => List.mem_append_left _ (hens h)) ((gleichAuf_SG hsg).trans hgl))

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

/-- **A returning head justifies its answer** (no event, as `popS_begr_ok`). -/
theorem popSA_begr_ok (hE : ¬ Nonempty (Ereignis D)) {G : RufRahmenG D} {W : World D}
    (hG : KopfSA P O passes Q S lok Tg G W) {lr : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {r : GRest D (vertragVon D G.f) lr Γ Λ} (hr : G.rest = ⟨lr, Γ, Λ, ρ, r⟩)
    (e : ErgExpr D Γ Λ (vertragVon D G.f).erg)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (A : AUmwelt D) (σ : World D), (semHA S O' U A passes R r σ ρ).gleich
        (.zurueck (leseA A σ Λ e.orte) (evalErg (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ))) :
    BegruendetA P O passes S
      ⟨G.f, G.s0, G.rho, .ok G.s0 (evalErg (W.lese Λ e.orte) e (W.lese Λ e.orte) ρ)⟩ := by
  obtain ⟨H, HA, HU, HX, σ, _, hf, _, hk, _, _, _, hka, _, _, _, _, _, _, heq⟩ := hG
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
    (hG : KopfSA P O passes Q S lok Tg G W) {lr : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {r : GRest D (vertragVon D G.f) lr Γ Λ} (hr : G.rest = ⟨lr, Γ, Λ, ρ, r⟩)
    (rg : Fin (vertragVon D G.f).gruende)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (A : AUmwelt D) (σ : World D),
      (semHA S O' U A passes R r σ ρ).gleich (.why σ rg)) :
    BegruendetA P O passes S ⟨G.f, G.s0, G.rho, .why G.s0 rg⟩ := by
  obtain ⟨H, HA, HU, HX, σ, _, hf, _, hk, _, _, _, hka, _, _, _, _, _, _, heq⟩ := hG
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
    (hW : WarteSA P O passes Q S lok Tg F G) (s1 : World D) (mk : World D → RufAusgang G.1)
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
    KopfSA P O passes Q S lok Tg ⟨F.f, F.rho, F.s0, ⟨l, Γ, Λ, ρ', r'⟩⟩ W' := by
  obtain ⟨H, HA, HU, HX, κ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hfu, hiu, hku, ⟨hfx, hkx⟩, hok,
    hreqκ, ⟨hglκ, hsub, hfussκ⟩, hcont⟩ := hW
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
    hreq, funkV_appendBA hf hk _ (fun _ => Nat.le_refl _) hbe, ⟨?_, ?_⟩, ?_, hfa, hra, hqa,
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


/-- **A push through a read set `os`** (as `pushS_gen`): the read is recorded; the callee's key
    world is the sequential world after the read (it agrees with the machine's entry world on
    the caller's stable carriers and on `os`). -/
theorem pushSA_gen (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hS : SperrInvOk S)
    {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    {z : RufFadenG D} {W : World D} (hF : FadenSA P O passes Q S lok Tg z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (os : List (D.Tab ⊕ D.Glob)) (g : D.Fn) (rhoF : World D → Env D (D.params g))
    (hX : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      ∀ c ∈ os, c ∈ stabilS P S lok z.kopf.f Λ ∨ Tg c)
    (hSt : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      (P.requires g).orte ++ (P.ensures g).orte ⊆ stabilS P S lok z.kopf.f Λ)
    (hrho : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) → ∀ σ : World D,
      GleichAuf (stabilS P S lok z.kopf.f Λ ++ os) σ (W.lese Λ os) → rhoF σ = rhoF (W.lese Λ os))
    {lc : Bool} {Γc : Ctx} {Λc : List (Res D)} (ρc : Env D Γc)
    (rc : GRest D (vertragVon D z.kopf.f) lc Γc Λc)
    (hΛc : ∀ L, Res.held L ∈ Λc ↔ Res.held L ∈ Λ)
    (hrc : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      rc.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f))
    (hlogik : ∀ (O' : Orakel D) (U : Umwelt D) (A : AUmwelt D) R (σ0 κ : World D) (e : Logik D),
      GleichAuf (stabilS P S lok z.kopf.f Λ ++ os) κ (W.lese Λ os) →
      leseA A σ0 Λ os = κ → R g κ (rhoF κ) = .logik e → semHA S O' U A passes R r σ0 ρ = .logik e)
    (hweiter : ∀ (O' : Orakel D) (U : Umwelt D) (A : AUmwelt D) R (σ0 κ : World D),
      GleichAuf (stabilS P S lok z.kopf.f Λ ++ os) κ (W.lese Λ os) →
      leseA A σ0 Λ os = κ →
      FortSA passes S ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩ g
        (semHA S O' U A passes R r σ0 ρ) R O' U A (R g κ (rhoF κ))) :
    FadenSA P O passes Q S lok Tg
      ⟨⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩ :: z.stapel,
        ⟨g, rhoF (W.lese Λ os), W.lese Λ os,
          ⟨false, D.params g, Signatur.anfang D (D.signatur g), rhoF (W.lese Λ os),
            .ende (P.rumpf g)⟩⟩,
        (W.lese Λ os).spur,
        RufEreignisF.eintritt g (rhoF (W.lese Λ os)) (W.lese Λ os) :: z.log⟩
      (W.lese Λ os) ∧
    ReqAmEintritt P g (W.lese Λ os) (rhoF (W.lese Λ os)) := by
  obtain ⟨⟨H, HA, HU, HX, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hfu, hiu, hku, ⟨hfx, hkx⟩, hg,
    hok, heq⟩, hSt'⟩ := hF
  have hok' : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) := by rw [hr] at hok; exact hok
  have hg0 : GleichAuf (stabilS P S lok z.kopf.f Λ) σ W := by rw [hr] at hg; exact hg
  obtain ⟨HX', hfx', hkx', hsub, hrec⟩ := lese_schritt Tg hfx hkx Λ os W.speicher
  have hgκ := mischT_gleichAuf hg0 (hX hok') Λ Λ
  have hρk := hrho hok' _ hgκ
  have heq' : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
      (U : Umwelt D) (A : AUmwelt D), PasstV R H → PasstA O' HA → PasstU S U HU →
      PasstX Tg A HX' → HavocA Tg A → GleichRS O O' →
      (zErgG (execEndHA (V := vertragVon D z.kopf.f) S O' U A passes R (P.rumpf z.kopf.f) z.kopf.s0
        z.kopf.rho)).folgt (semHA S O' U A passes R r σ ρ) := by
    intro R O' U A hR hA hU hX hHA hQ
    have := heq R O' U A hR hA hU (passtX_teil hsub hX) hHA hQ
    rw [hr] at this
    exact this
  have hctr := hSt hok'
  have hreqκ := pushSA_req hO hRL hQ hS hsp hK hreq hf hv hfa hra hqa hfu hiu hfx' r heq' g
    (mischT Tg os (σ.lese Λ os) W.speicher) (rhoF (mischT Tg os (σ.lese Λ os) W.speicher))
    (fun O' U A R e hPX hHA h => hlogik O' U A R σ _ e hgκ (hrec A hPX hHA) h)
  rw [hρk] at hreqκ
  have hctrκ : GleichAuf ((P.requires g).orte ++ (P.ensures g).orte)
      (mischT Tg os (σ.lese Λ os) W.speicher) (W.lese Λ os) :=
    GleichAuf.mono (fun _ h => List.mem_append_left _ (hctr h)) hgκ
  have hreq0 := req_transfer hreqκ
    (GleichAuf.mono (fun _ h => List.mem_append_left _ h) hctrκ)
  have hsubc : (P.requires g).orte ++ (P.ensures g).orte ⊆ stabilS P S lok z.kopf.f Λc :=
    fun _ h => stabilS_iff (fun L => (hΛc L).symm) (hctr h)
  have hlen : σ.spur.length ≤ (mischT Tg os (σ.lese Λ os) W.speicher).spur.length :=
    lese_laenge _ _ _
  refine ⟨⟨⟨[], [], [], [], W.lese Λ os, hreq0, funkV_nil, vertraegeOkR_nil P, kurzVBA_nil _,
    funkA_nil, rahmenA_nil, vertragA_nil _ Q, kurzAB_nil _, funkU_nil, invU_nil S, kurzUB_nil _,
    ⟨funkX_nil, kurzX_nil _⟩, GleichAuf.refl _ _, ⟨hFragS g, fuss_rumpfG P g⟩,
    fun R O' U A _ _ _ _ _ _ => ZErgG.folgt_refl _⟩,
    ⟨H, HA, HU, HX', mischT Tg os (σ.lese Λ os) W.speicher, hreq, hf, hv, kurzVBA_mono hk hlen,
      hfa, hra, hqa, kurzAB_mono hka hlen, hfu, hiu, kurzUB_mono hku hlen, ⟨hfx', hkx'⟩, hrc hok',
      hreqκ, ⟨hctrκ, hsubc, gleichAuf_stabil_iff hΛc
        (GleichAuf.mono (fun _ h => List.mem_append_left _ h) hgκ)⟩, ?_⟩, hSt'⟩, hreq0⟩
  intro R O' U A hR hA hU hX hHA hQ
  have hw := hweiter O' U A R σ _ hgκ (hrec A hX hHA)
  rw [hρk] at hw
  exact fortSA_mono (F := ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩)
    (heq' R O' U A hR hA hU hX hHA hQ) hw

/-- **An axiom step keeps the replay** (as `fadenS_ax`): its argument read is recorded. -/
theorem fadenSA_ax {z : RufFadenG D} {W : World D}
    (hF : FadenSA P O passes Q S lok Tg z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    {l' : Bool} {Γ' : Ctx} {Λ' : List (Res D)} (ρ' : Env D Γ')
    (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (spur' : List (Ereignis D))
    (hΛ' : ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ)
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
    (hX : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      ∀ c ∈ args.orte, c ∈ stabilS P S lok z.kopf.f Λ ∨ Tg c)
    (hok : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      r'.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f))
    (xm : World D × Int) (hxm : Rahmen (D.aschreibt a) (D.agschreibt a) (W.lese Λ args.orte) xm.1)
    (hxO : ¬ Nonempty (Ereignis D) →
      xm.2 = (O.wirkt a (W.lese Λ args.orte) (evalArgs (W.lese Λ args.orte) args
        (W.lese Λ args.orte) ρ)).2)
    (hlok : AxEnsLokal Q)
    (hxq : ∀ v : ErgVal D (D.aerg a), einpassenErg O.zeiger (D.aerg a) xm.2 = some v →
      Q a xm.1 v = true)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (A : AUmwelt D) (σ0 κ : World D), ZeigerGleich O O' →
      leseA A σ0 Λ args.orte = κ →
      O'.wirkt a κ (evalArgs κ args κ ρ) = (axWeltF a κ xm.1, xm.2) →
      (semHA S O' U A passes R r σ0 ρ).folgt
        (semHA S O' U A passes R r' (axWeltF a κ xm.1) ρ')) :
    FadenSA P O passes Q S lok Tg
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩
      (xm.1.speicher.welt spur') := by
  obtain ⟨⟨H, HA, HU, HX, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hfu, hiu, hku, ⟨hfx, hkx⟩, hg,
    hok0, heq⟩, hS⟩ := hF
  have hok' : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) := by
    rw [hr] at hok0; exact hok0
  have hg0 : GleichAuf (stabilS P S lok z.kopf.f Λ) σ W := by rw [hr] at hg; exact hg
  obtain ⟨HX', hfx', hkx', hsub, hrec⟩ := lese_schritt Tg hfx hkx Λ args.orte W.speicher
  have hgκ := mischT_gleichAuf hg0 (hX hok') Λ Λ
  have hlen : σ.spur.length ≤ (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher).spur.length :=
    lese_laenge _ _ _
  have hlen2 : σ.spur.length ≤
      (axWeltF a (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher) xm.1).spur.length :=
    Nat.le_trans hlen (axWeltF_laenge _ _ _)
  have hlen3 : (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher).spur.length ≤
      (axWeltF a (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher) xm.1).spur.length :=
    axWeltF_laenge _ _ _
  have hlt : Nonempty (Ereignis D) →
      (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher).spur.length <
      (axWeltF a (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher) xm.1).spur.length :=
    fun hN => frischSpur_laenge hN _
  have hpa : ¬ Nonempty (Ereignis D) → PasstA O (HA ++ [⟨a,
      mischT Tg args.orte (σ.lese Λ args.orte) W.speicher,
      evalArgs (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher) args
        (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher) ρ,
      (axWeltF a (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher) xm.1, xm.2)⟩]) := by
    intro hN a' σk ρk x hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hka.2 hN a' σk ρk x hm
    · rw [List.mem_singleton] at hm
      cases hm
      rw [hxO hN, welt_eq hN (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher)
        (W.lese Λ args.orte)]
      exact Prod.ext (welt_eq hN _ _) rfl
  refine ⟨⟨H, HA ++ [⟨a, mischT Tg args.orte (σ.lese Λ args.orte) W.speicher,
      evalArgs (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher) args
        (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher) ρ,
      (axWeltF a (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher) xm.1, xm.2)⟩], HU, HX',
    axWeltF a (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher) xm.1, hreq, hf, hv,
    kurzVBA_mono hk hlen2, ?_, ?_, ?_, ?_,
    hfu, hiu, kurzUB_mono hku hlen2, ⟨hfx', kurzX_mono hkx' hlen3⟩, ?_, hok hok', ?_⟩, hS⟩
  · by_cases hN : Nonempty (Ereignis D)
    · exact funkA_append hfa (hka.1 hN) _ hlen
    · exact funkA_of_passtA (hpa hN)
  · intro a' σk ρk x hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hra a' σk ρk x hm
    · rw [List.mem_singleton] at hm
      cases hm
      exact axWeltF_rahmen a _ _
  · intro a' σk ρk x hm v hv
    rcases List.mem_append.mp hm with hm | hm
    · exact hqa a' σk ρk x hm v hv
    · rw [List.mem_singleton] at hm
      cases hm
      exact axWeltF_vertrag hlok a _ _ v (hxq v hv)
  · refine ⟨fun hN e hm => ?_, hpa⟩
    rcases List.mem_append.mp hm with hm | hm
    · exact Nat.lt_of_lt_of_le (hka.1 hN e hm) hlen2
    · rw [List.mem_singleton] at hm
      subst hm
      exact hlt hN
  · have h1 := axWeltF_gleichAuf a
      (GleichAuf.mono (fun _ h => List.mem_append_left _ h) hgκ) hxm
    exact gleichAuf_stabil_iff hΛ' ⟨fun t ht => h1.1 t ht, fun g hg' => h1.2 g hg'⟩
  · intro R O' U A hR hA hU hXA hHA hQ
    have h1 := heq R O' U A hR (passtA_append hA) hU (passtX_teil hsub hXA) hHA hQ
    rw [hr] at h1
    exact ZErgG.folgt_trans h1
      (hsem O' R U A σ _ hQ.2.2 (hrec A hXA hHA)
        (hA _ _ _ _ (List.mem_append_right _ List.mem_cons_self)))


/-- **A leaf's outcome world extends the world after its reads** (non-axiom leaves). -/
theorem blatt_lese_laenge (P : Programm D) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (hb : s.istBlatt = true)
    (ha : s.istAxiom = false) {σ : World D} {ρ : Env D Γ} {σ' : World D} {ρ' : Env D Γ}
    (h : execStmt O passes R s σ ρ = .ok σ' ρ') :
    (σ.lese Λ (stmtOrteP P s)).spur.length ≤ σ'.spur.length := by
  cases s with
  | assignSlot t f i e hw hL =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact spur_laenge_erw (Erw.schreibSlot _ _ _ _ _ _)
  | assignThru p t ht f i e hw hL =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact spur_laenge_erw (Erw.schreibSlot _ _ _ _ _ _)
  | assignGlob g e hw hL =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact spur_laenge_erw (Erw.schreibGlob _ _ _ _)
  | putBytes t f hf n i hlo hhi e hw hL =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact spur_laenge_erw (Erw.schreibBytes _ _ _ _ _ _ _)
  | assignVar x e =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Nat.le_refl _
  | shift t f hτ i von nach hn he hw hL =>
      simp only [execStmt] at h
      split at h
      · simp only [Ausgang.ok.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact spur_laenge_erw (Erw.schreibSlot _ _ _ _ _ _)
      · cases h
  | regWrite r hk e =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Nat.le_refl _
  | transition r hk m hm hmk maske bits =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [stmtOrteP, lese_nil]
      exact Nat.le_refl _
  | publish g e payload hp hw hL =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact spur_laenge_erw (Erw.schreibGlob _ _ _ _)
  | advances =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [stmtOrteP, lese_nil]
      exact Nat.le_refl _
  | retires =>
      simp only [execStmt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [stmtOrteP, lese_nil]
      exact Nat.le_refl _
  | axiomCall => simp [Stmt.istAxiom] at ha
  | ret e hp => simp [execStmt] at h
  | retWhy r hp => simp [execStmt] at h
  | leave hl => simp [execStmt] at h
  | next hl => simp [execStmt] at h
  | _ => simp [Stmt.istBlatt] at hb

theorem vorA_eq {A : AUmwelt D} {σ w : World D} {Λ : List (Res D)} {X : List (D.Tab ⊕ D.Glob)}
    (h : leseA A σ Λ X = w) : vorA A σ Λ X = ⟨w.slots, w.globs, σ.spur⟩ := by
  unfold vorA
  unfold leseA at h
  rw [h]

/-- **A leaf step keeps the replay** (as `fadenS_blatt`): its reads are recorded; a non-axiom
    leaf by leaf locality over the stable carriers AND the read list, an axiom call by recording
    its answer. -/
theorem fadenSA_blatt (hO : GutO O) (hQ : AxVertragO Q O)
    (hlok : AxEnsLokal Q) (hFS : ∀ f, FussSX P S lok Tg f) {z : RufFadenG D} {W : World D}
    (hF : FadenSA P O passes Q S lok Tg z W) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {ρ : Env D Γ} {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (s : Stmt D (vertragVon D z.kopf.f) l Γ Λ Λ') (K : GRest D (vertragVon D z.kopf.f) l Γ Λ')
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (A : AUmwelt D) (σ : World D),
      semHA S O' U A passes R r σ ρ = weiterHA S O' U A passes R K (execStmtHA S O' U A passes R s σ ρ))
    (hok : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      stmtOrteP P s ⊆ fussOrteG P z.kopf.f ∧ K.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f))
    (hleaf : s.istBlatt = true) (σ' : World D) (ρ' : Env D Γ)
    (hstep : execStmt O passes keinRuf s W ρ = .ok σ' ρ') :
    FadenSA P O passes Q S lok Tg
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, Λ', ρ', K⟩⟩, σ'.spur, z.log⟩
      (σ'.speicher.welt σ'.spur) := by
  have hΛ' : ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ := s.held_iff
  cases hax : s.istAxiom with
  | false =>
      refine fadenSA_lokalQ hF hr ρ' K σ'.spur (fun σ HX hfx hkx hg hok' => ?_)
      obtain ⟨hs, hK⟩ := hok hok'
      have hXs := orte_stabilX (hFS _) (s.blatt_darf P hleaf) hs
      obtain ⟨HX', hfx', hkx', hsub, hrec⟩ :=
        lese_schritt Tg hfx hkx Λ (stmtOrteP P s) W.speicher
      have hgX := mischT_gleichAuf hg hXs Λ Λ
      have hĝ : GleichAuf (stabilS P S lok z.kopf.f Λ ++ stmtOrteP P s)
          (⟨(mischT Tg (stmtOrteP P s) (σ.lese Λ (stmtOrteP P s)) W.speicher).slots,
            (mischT Tg (stmtOrteP P s) (σ.lese Λ (stmtOrteP P s)) W.speicher).globs, σ.spur⟩ :
            World D) W := hgX
      obtain ⟨σs, hes, hgs, _⟩ := blatt_lokalV P O passes s hleaf hax
        (fun _ h => List.mem_append_right _ h) hĝ hstep
      have hl := blatt_lese_laenge P O passes keinRuf s hleaf hax (hes O keinRuf)
      refine ⟨σs, HX', hfx', kurzX_mono hkx' hl, hsub, Nat.le_trans (lese_laenge σ Λ _) hl,
        gleichAuf_stabil_iff hΛ' (GleichAuf.mono (fun _ h => List.mem_append_left _ h)
          ⟨fun t ht => hgs.1 t ht, fun g hg' => hgs.2 g hg'⟩),
        hK, fun R O' U A hPX hHA _ => ?_⟩
      rw [hsem, execStmtHA_blatt P S O' U hHA passes R s hleaf, vorA_eq (hrec A hPX hHA), hes]
      exact ZErgG.folgt_refl _
  | true =>
      cases s with
      | axiomCall a args h hw hg hd hgd =>
          obtain ⟨e1, e2, u, hu⟩ := axiomCall_ok_inv O passes keinRuf a args h hw hg hd hgd W ρ σ' ρ'
            hstep
          subst e2
          have hfr := (hO a (W.lese Λ args.orte)
            (evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ')).1
          rw [← e1] at hfr
          refine fadenSA_ax hF hr ρ' K σ'.spur hΛ' a args
            (fun h' => orte_stabilX (hFS _) args.orte_darf (hok h').1) (fun h' => (hok h').2)
            (σ', (O.wirkt a (W.lese Λ args.orte)
              (evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ')).2) hfr (fun _ => rfl)
            hlok
            (fun v hv => by
              rw [e1]
              exact hQ a _ _ v hv) ?_
          intro O' R U A σ0 κ hz hκ hw
          rw [hsem]
          apply ZErgG.folgt_of_eq
          simp only [execStmtHA, axiomAntwort, hκ, hw]
          simp only [(show O'.zeiger = O.zeiger from hz), hu]
          rfl
      | _ => simp [Stmt.istAxiom] at hax

/-- **The acquire keeps the replay** (as `fadenS_locks`). -/
theorem fadenSA_locks {z : RufFadenG D} {W : World D} (hF : FadenSA P O passes Q S lok Tg z W)
    {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)} (L : D.Lock)
    (hrL : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D (vertragVon D z.kopf.f) l Γ (Res.held L :: Λ) (Res.held L :: Λ))
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.locks L hrL body) rest) k⟩)
    (hinv : S.inv L W.speicher = true) (spur' : List (Ereignis D)) :
    FadenSA P O passes Q S lok Tg
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
        ⟨l, Γ, Res.held L :: Λ, ρ, .dann body (.frei L (.dann rest k))⟩⟩, spur', z.log⟩
      (W.speicher.welt spur') := by
  obtain ⟨⟨H, HA, HU, HX, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hfu, hiu, hku, ⟨hfx, hkx⟩, hg,
    hok, heq⟩, hS⟩ := hF
  rw [hr] at hg hok
  simp only at hg hok
  obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
  have hlen : σ.spur.length < ((mischU S L σ W.speicher).nimmt L).spur.length := by
    show σ.spur.length < (Ereignis.nimmt L _ :: σ.spur).length
    exact Nat.lt_succ_self _
  refine ⟨⟨H, HA, HU ++ [(L, σ, W.speicher)], HX, (mischU S L σ W.speicher).nimmt L, hreq, hf, hv,
    kurzVBA_mono hk (Nat.le_of_lt hlen), hfa, hra, hqa, kurzAB_mono hka (Nat.le_of_lt hlen),
    funkU_append hfu (hku ⟨.gibt L⟩) _ (Nat.le_refl _), invU_append hiu L σ W.speicher hinv, ?_,
    ⟨hfx, kurzX_mono hkx (Nat.le_of_lt hlen)⟩, ?_, ⟨hks, hss, hrest⟩, ?_⟩, hS⟩
  · intro hN e he
    rcases List.mem_append.mp he with he | he
    · exact Nat.lt_trans (hku hN e he) hlen
    · rw [List.mem_singleton] at he
      subst he
      exact hlen
  · have key : ∀ c ∈ stabilS P S lok z.kopf.f (Res.held L :: Λ),
        TraegerGleich ((mischU S L σ W.speicher).nimmt L).speicher W.speicher c := by
      intro c hc
      by_cases hcL : c ∈ S.orte L
      · exact mischU_innen S L σ W.speicher c hcL
      · have hc' : c ∈ stabilS P S lok z.kopf.f Λ := by
          rcases stabilS_mem.mp hc with hc | ⟨K, hK, hcK⟩
          · exact stabilS_mem.mpr (Or.inl hc)
          · rcases List.mem_cons.mp hK with hK | hK
            · cases hK
              exact absurd hcK hcL
            · exact stabilS_mem.mpr (Or.inr ⟨K, hK, hcK⟩)
        refine traegerGleich_trans (mischU_aussen S L σ W.speicher c hcL) ?_
        cases c with
        | inl t => exact hg.1 t hc'
        | inr g => exact hg.2 g hc'
    exact ⟨fun t ht => key (.inl t) ht, fun g hg' => key (.inr g) hg'⟩
  · intro R O' U A hR hA hU hX hHA hQ
    have h1 := heq R O' U A hR hA (passtU_append hU) hX hHA hQ
    rw [hr] at h1
    simp only at h1
    refine ZErgG.folgt_trans h1 (ZErgG.folgt_of_eq ?_)
    rw [semHA_locks S O' U A passes R L hrL body rest k σ ρ,
      hU L σ W.speicher (List.mem_append_right _ List.mem_cons_self)]

end Schritte

end Gabbro.Grammatik
