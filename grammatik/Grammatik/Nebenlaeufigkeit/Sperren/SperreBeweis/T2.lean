/- Part 2 of 3 of `SperreBeweis` (split by instrumente/teile/lean-teilen.py; the umbrella `SperreBeweis.lean` imports all parts). -/
import Grammatik.Nebenlaeufigkeit.Sperren.SperreBeweis.T1

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Schritte

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool}

theorem kopfS_okS {F : RufRahmenG D} {W : World D} (h : KopfS P O passes Q S lok F W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D F.f) l Γ Λ} (hr : F.rest = ⟨l, Γ, Λ, ρ, r⟩) :
    r.okS P (fussOrteG P F.f) (sicher P lok F.f) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hok, _⟩ := h
  rw [hr] at hok
  exact hok

/-- **A head-local step without a new record.** -/
theorem fadenS_lokalQ {z : RufFadenG D} {W W' : World D} (hF : FadenS P O passes Q S lok z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    {l' : Bool} {Γ' : Ctx} {Λ' : List (Res D)} (ρ' : Env D Γ')
    (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (spur' : List (Ereignis D))
    (hstep : ∀ σ : World D, GleichAuf (stabilS P S lok z.kopf.f Λ) σ W →
      r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      ∃ σ', σ.spur.length ≤ σ'.spur.length ∧ GleichAuf (stabilS P S lok z.kopf.f Λ') σ' W' ∧
        r'.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) ∧
        ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
          (U : Umwelt D), GleichRS O O' →
          (semH S O' U passes R r σ ρ).folgt (semH S O' U passes R r' σ' ρ')) :
    FadenS P O passes Q S lok
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩ W' := by
  obtain ⟨⟨H, HA, HU, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hfu, hiu, hku, hg, hok, heq⟩, hS⟩ :=
    hF
  have hok' : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) := by rw [hr] at hok; exact hok
  have hg0 : GleichAuf (stabilS P S lok z.kopf.f Λ) σ W := by rw [hr] at hg; exact hg
  obtain ⟨σ', hl, hg', hok'', hsem⟩ := hstep σ hg0 hok'
  refine ⟨⟨H, HA, HU, σ', hreq, hf, hv, kurzVB_mono hk hl, hfa, hra, hqa, kurzAB_mono hka hl, hfu,
    hiu, kurzUB_mono hku hl, hg', hok'', fun R O' U hR hA hU hQ => ?_⟩, hS⟩
  have h1 := heq R O' U hR hA hU hQ
  rw [hr] at h1
  exact ZErgG.folgt_trans h1 (hsem R O' U hQ)

/-- `fadenS_lokalQ` for a step whose frame semantics holds for every
    sequential oracle. -/
theorem fadenS_lokal {z : RufFadenG D} {W W' : World D} (hF : FadenS P O passes Q S lok z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    {l' : Bool} {Γ' : Ctx} {Λ' : List (Res D)} (ρ' : Env D Γ')
    (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (spur' : List (Ereignis D))
    (hstep : ∀ σ : World D, GleichAuf (stabilS P S lok z.kopf.f Λ) σ W →
      r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      ∃ σ', σ.spur.length ≤ σ'.spur.length ∧ GleichAuf (stabilS P S lok z.kopf.f Λ') σ' W' ∧
        r'.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) ∧
        ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
          (U : Umwelt D), (semH S O' U passes R r σ ρ).folgt (semH S O' U passes R r' σ' ρ')) :
    FadenS P O passes Q S lok
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩ W' :=
  fadenS_lokalQ hF hr ρ' r' spur' fun σ hg hok => by
    obtain ⟨σ', hl, hg', hok', hsem⟩ := hstep σ hg hok
    exact ⟨σ', hl, hg', hok', fun R O' U _ => hsem R O' U⟩

/-- Memory moved outside the head's stable carriers keeps the replay. -/
theorem fadenS_speicher {z : RufFadenG D} {W W' : World D} (hF : FadenS P O passes Q S lok z W)
    (hw : ∀ c ∈ stabilS P S lok z.kopf.f z.kopf.rest.2.2.1,
      TraegerGleich W'.speicher W.speicher c) :
    FadenS P O passes Q S lok z W' := by
  obtain ⟨⟨H, HA, HU, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hfu, hiu, hku, hg, hok, heq⟩, hS⟩ :=
    hF
  refine ⟨⟨H, HA, HU, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hfu, hiu, hku,
    ⟨fun t ht => ?_, fun g hg' => ?_⟩, hok, heq⟩, hS⟩
  · exact (hg.1 t ht).trans (hw (.inl t) ht).symm
  · exact (hg.2 g hg').trans (hw (.inr g) hg').symm

/-- **The return leg.** -/
theorem popS_ens (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hS : SperrInvOk S)
    {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f) {G : RufRahmenG D}
    {W : World D} (hG : KopfS P O passes Q S lok G W) {lr : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {r : GRest D (vertragVon D G.f) lr Γ Λ} (hr : G.rest = ⟨lr, Γ, Λ, ρ, r⟩)
    (e : ErgExpr D Γ Λ (vertragVon D G.f).erg) (he : e.orte ⊆ stabilS P S lok G.f Λ)
    (hens : (P.ensures G.f).orte ⊆ stabilS P S lok G.f Λ)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (σ : World D), (semH S O' U passes R r σ ρ).gleich
        (.zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ))) :
    EnsAmRueck P G.f G.s0 (W.lese Λ e.orte) G.rho
      (evalErg (W.lese Λ e.orte) e (W.lese Λ e.orte) ρ) := by
  obtain ⟨H, HA, HU, σ, hreq, hf, hv, _, hfa, hra, hqa, _, hfu, hiu, _, hg, _, heq⟩ := hG
  have h1 := heq (rufAusV H) (orakelAus O HA) (umweltAus S sp HU) (rufAusV_passt hf)
    (orakelAus_passt O hfa) (umweltAus_passt S sp hfu) (gleichRS_orakelAus O HA)
  rw [hr] at h1 hg
  simp only at h1 hg
  have h2 := ZErgG.folgt_zurueck (ZErgG.folgt_trans h1 (ZErgG.folgt_of_gleich (hsem _ _ _ σ)))
  obtain ⟨σ'', hex, hsg⟩ := zErgG_gleich_zurueck h2
  have hE := ((hK G.f).1 (orakelAus O HA) (orakelAus_rahmen hO hra) (regLokal_orakelAus hRL HA)
    (orakelAus_vertrag hQ hqa) (umweltAus S sp HU) (umweltAus_ok hS hsp hiu) (rufAusV H)
    (rufAusV_rahmen hv) (rufAusV_ohneVorbedingung hv.1) G.s0 G.rho hreq).1 σ'' _ hex
  have hgl : GleichAuf (stabilS P S lok G.f Λ) (σ.lese Λ e.orte) (W.lese Λ e.orte) :=
    hg.lese Λ Λ e.orte e.orte
  rw [evalErg_gleichAuf e (fun _ h => he h) hgl ρ] at hE
  exact ens_transfer hE (GleichAuf.refl _ _)
    (GleichAuf.mono (fun _ h => hens h) ((gleichAuf_SG hsg).trans hgl))

/-- **The call leg.** -/
theorem pushS_req (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hS : SperrInvOk S)
    {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f) {F : RufRahmenG D}
    {H : List (EintragV D)} {HA : List (AxEintrag D)} {HU : List (UEintrag D)} {σ : World D}
    (hreq : ReqAmEintritt P F.f F.s0 F.rho) (hf : FunkV H) (hv : VertraegeOkR P H)
    (hfa : FunkA HA) (hra : RahmenA HA) (hqa : VertragA O.zeiger Q HA) (hfu : FunkU HU) (hiu : InvU S HU)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    (r : GRest D (vertragVon D F.f) l Γ Λ)
    (heq : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
      (U : Umwelt D), PasstV R H → PasstA O' HA → PasstU S U HU → GleichRS O O' →
      (zErgG (execEndH (V := vertragVon D F.f) S O' U passes R (P.rumpf F.f) F.s0 F.rho)).folgt
        (semH S O' U passes R r σ ρ))
    (g : D.Fn) (κ : World D) (ρk : Env D (D.params g))
    (hlogik : ∀ (O' : Orakel D) (U : Umwelt D) R (e : Logik D), R g κ ρk = .logik e →
      semH S O' U passes R r σ ρ = .logik e) :
    ReqAmEintritt P g κ ρk := by
  cases hq : wahr? (eval κ (P.requires g) κ ρk) with
  | true => exact hq
  | false =>
      exfalso
      have htor : torRuf P (rufAusV H) g κ ρk = .logik (.vorbedingung g) := by
        simp only [torRuf, hq]
        rfl
      have h1 := heq _ (orakelAus O HA) (umweltAus S sp HU) (torRuf_passtV (rufAusV_passt hf) hv.1)
        (orakelAus_passt O hfa) (umweltAus_passt S sp hfu) (gleichRS_orakelAus O HA)
      rw [hlogik _ _ _ _ htor] at h1
      have hex := zErgG_gleich_logik (ZErgG.folgt_logik h1)
      exact ((hK F.f).1 (orakelAus O HA) (orakelAus_rahmen hO hra) (regLokal_orakelAus hRL HA)
        (orakelAus_vertrag hQ hqa) (umweltAus S sp HU) (umweltAus_ok hS hsp hiu) (rufAusV H)
        (rufAusV_rahmen hv) (rufAusV_ohneVorbedingung hv.1) F.s0 F.rho hreq).2 g hex

/-- **A returning head justifies its answer** (no event): the head's
    record is justified, the machine oracle repeats its axiom record, and
    against every handler repeating its call record its body ends in the
    value the machine returns. -/
theorem popS_begr_ok (hE : ¬ Nonempty (Ereignis D)) {G : RufRahmenG D} {W : World D}
    (hG : KopfS P O passes Q S lok G W) {lr : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {r : GRest D (vertragVon D G.f) lr Γ Λ} (hr : G.rest = ⟨lr, Γ, Λ, ρ, r⟩)
    (e : ErgExpr D Γ Λ (vertragVon D G.f).erg)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (σ : World D), (semH S O' U passes R r σ ρ).gleich
        (.zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ))) :
    Begruendet P O passes S
      ⟨G.f, G.s0, G.rho, .ok G.s0 (evalErg (W.lese Λ e.orte) e (W.lese Λ e.orte) ρ)⟩ := by
  obtain ⟨H, HA, HU, σ, _, hf, _, hk, _, _, _, hka, _, _, _, _, _, heq⟩ := hG
  obtain rfl : σ = W := welt_eq hE σ W
  refine .mk _ _ _ _ H hf (hk.2 hE) (fun R U hR => ?_)
  have h1 := heq R O U hR (hka.2 hE) (passtU_leer hE S U HU) ⟨rfl, rfl, rfl⟩
  rw [hr] at h1
  simp only at h1
  have h2 := ZErgG.folgt_zurueck (ZErgG.folgt_trans h1 (ZErgG.folgt_of_gleich (hsem _ _ _ σ)))
  obtain ⟨σ'', hex, _⟩ := zErgG_gleich_zurueck h2
  exact ⟨σ'', hex⟩

/-- The same for a head at a REASON return. -/
theorem popS_begr_grund (hE : ¬ Nonempty (Ereignis D)) {G : RufRahmenG D} {W : World D}
    (hG : KopfS P O passes Q S lok G W) {lr : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {r : GRest D (vertragVon D G.f) lr Γ Λ} (hr : G.rest = ⟨lr, Γ, Λ, ρ, r⟩)
    (rg : Fin (vertragVon D G.f).gruende)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (σ : World D), (semH S O' U passes R r σ ρ).gleich (.why σ rg)) :
    Begruendet P O passes S ⟨G.f, G.s0, G.rho, .why G.s0 rg⟩ := by
  obtain ⟨H, HA, HU, σ, _, hf, _, hk, _, _, _, hka, _, _, _, _, _, heq⟩ := hG
  refine .mk _ _ _ _ H hf (hk.2 hE) (fun R U hR => ?_)
  have h1 := heq R O U hR (hka.2 hE) (passtU_leer hE S U HU) ⟨rfl, rfl, rfl⟩
  rw [hr] at h1
  simp only at h1
  have h2 := ZErgG.folgt_grund (ZErgG.folgt_trans h1 (ZErgG.folgt_of_gleich (hsem _ _ _ σ)))
  obtain ⟨σ'', hex, _⟩ := zErgG_gleich_grund h2
  exact ⟨σ'', hex⟩

/-- **The caller resumes** after its pending call to `G` (as `popR_kopf`):
    the answer is recorded with the answer world `rahmenWeltF`, and the frame
    becomes a replayed head whose residue has the same held locks. Without
    an event the new entry is fresh no more; it is justified instead
    (`hb`, from the returning head: `popS_begr_ok`, `popS_begr_grund`). -/
theorem popS_kopf {F : RufRahmenG D}
    {G : Σ f : D.Fn, Env D (D.params f) × World D}
    (hW : WarteS P O passes Q S lok F G) (s1 : World D) (mk : World D → RufAusgang G.1)
    (hmk : (∃ v, (∀ σa, mk σa = .ok σa v) ∧ EnsAmRueck P G.1 G.2.2 s1 G.2.1 v) ∨
      (∃ r, ∀ σa, mk σa = .why σa r))
    (hb : ¬ Nonempty (Ereignis D) → Begruendet P O passes S ⟨G.1, G.2.2, G.2.1, mk G.2.2⟩)
    (hRah : GleichOhne G.1 (stabilS P S lok F.f F.rest.2.2.1) G.2.2 s1)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ' : Env D Γ) (r' : GRest D (vertragVon D F.f) l Γ Λ)
    (hΛ : ∀ L, Res.held L ∈ Λ → Res.held L ∈ F.rest.2.2.1)
    (hok' : F.rest.2.2.2.2.okS P (fussOrteG P F.f) (sicher P lok F.f) →
      r'.okS P (fussOrteG P F.f) (sicher P lok F.f))
    (hwahl : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
      (U : Umwelt D) (σa : World D) (X : ZErgG (vertragVon D F.f)),
      FortS passes S F G.1 X R O' U (mk σa) → X.folgt (semH S O' U passes R r' σa ρ'))
    (W' : World D) (hW' : W'.slots = s1.slots ∧ W'.globs = s1.globs) :
    KopfS P O passes Q S lok ⟨F.f, F.rho, F.s0, ⟨l, Γ, Λ, ρ', r'⟩⟩ W' := by
  obtain ⟨H, HA, HU, κ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hfu, hiu, hku, hok, hreqκ,
    ⟨hglκ, hsub, hfussκ⟩, hcont⟩ := hW
  have hσa : GleichAuf (stabilS P S lok F.f F.rest.2.2.1) (rahmenWeltF G.1 κ s1) s1 :=
    rahmenWeltF_gleichAuf G.1 hfussκ hRah
  have hlen := rahmenWeltF_laenge G.1 κ s1
  have hlt : Nonempty (Ereignis D) → κ.spur.length < (rahmenWeltF G.1 κ s1).spur.length :=
    fun hN => frischSpur_laenge hN κ.spur
  have hbe : ¬ Nonempty (Ereignis D) →
      Begruendet P O passes S ⟨G.1, κ, G.2.1, mk (rahmenWeltF G.1 κ s1)⟩ := by
    intro hN
    rw [welt_eq hN (rahmenWeltF G.1 κ s1) G.2.2, welt_eq hN κ G.2.2]
    exact hb hN
  have hmem : (⟨G.1, κ, G.2.1, mk (rahmenWeltF G.1 κ s1)⟩ : EintragV D) ∈
      H ++ [⟨G.1, κ, G.2.1, mk (rahmenWeltF G.1 κ s1)⟩] :=
    List.mem_append_right _ List.mem_cons_self
  refine ⟨H ++ [⟨G.1, κ, G.2.1, mk (rahmenWeltF G.1 κ s1)⟩], HA, HU, rahmenWeltF G.1 κ s1,
    hreq, funkV_appendB hf hk _ (fun _ => Nat.le_refl _) hbe, ⟨?_, ?_⟩, ?_, hfa, hra, hqa,
    kurzAB_mono hka hlen, hfu, hiu, kurzUB_mono hku hlen, ?_,
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
  · intro R O' U hR hA hU hQ
    have hans := hR _ _ _ _ hmem
    have hc := hcont R O' U (passtV_append hR) hA hU hQ
    rw [hans] at hc
    exact hwahl R O' U _ _ hc

/-- **A push through a read set `os` and a parameter function `rhoF`**
    (direct and indirect calls): the head becomes a suspended frame with the
    continuation `rc` (same held locks), the callee a fresh replayed head. -/
theorem pushS_gen (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hS : SperrInvOk S)
    {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    {z : RufFadenG D} {W : World D} (hF : FadenS P O passes Q S lok z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (os : List (D.Tab ⊕ D.Glob)) (g : D.Fn) (rhoF : World D → Env D (D.params g))
    (hSt : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      (P.requires g).orte ++ (P.ensures g).orte ⊆ stabilS P S lok z.kopf.f Λ)
    (hrho : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) → ∀ σ : World D,
      GleichAuf (stabilS P S lok z.kopf.f Λ) σ W → rhoF (σ.lese Λ os) = rhoF (W.lese Λ os))
    {lc : Bool} {Γc : Ctx} {Λc : List (Res D)} (ρc : Env D Γc)
    (rc : GRest D (vertragVon D z.kopf.f) lc Γc Λc)
    (hΛc : ∀ L, Res.held L ∈ Λc ↔ Res.held L ∈ Λ)
    (hrc : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      rc.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f))
    (hlogik : ∀ (O' : Orakel D) (U : Umwelt D) R σ (e : Logik D),
      GleichAuf (stabilS P S lok z.kopf.f Λ) σ W →
      R g (σ.lese Λ os) (rhoF (σ.lese Λ os)) = .logik e → semH S O' U passes R r σ ρ = .logik e)
    (hweiter : ∀ (O' : Orakel D) (U : Umwelt D) R σ, GleichAuf (stabilS P S lok z.kopf.f Λ) σ W →
      FortS passes S ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩ g
        (semH S O' U passes R r σ ρ) R O' U (R g (σ.lese Λ os) (rhoF (σ.lese Λ os)))) :
    FadenS P O passes Q S lok
      ⟨⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩ :: z.stapel,
        ⟨g, rhoF (W.lese Λ os), W.lese Λ os,
          ⟨false, D.params g, Signatur.anfang D (D.signatur g), rhoF (W.lese Λ os),
            .ende (P.rumpf g)⟩⟩,
        (W.lese Λ os).spur,
        RufEreignisF.eintritt g (rhoF (W.lese Λ os)) (W.lese Λ os) :: z.log⟩
      (W.lese Λ os) ∧
    ReqAmEintritt P g (W.lese Λ os) (rhoF (W.lese Λ os)) := by
  obtain ⟨⟨H, HA, HU, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hfu, hiu, hku, hg, hok, heq⟩, hSt'⟩ :=
    hF
  have hok' : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) := by rw [hr] at hok; exact hok
  have hg0 : GleichAuf (stabilS P S lok z.kopf.f Λ) σ W := by rw [hr] at hg; exact hg
  have heq' : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
      (U : Umwelt D), PasstV R H → PasstA O' HA → PasstU S U HU → GleichRS O O' →
      (zErgG (execEndH (V := vertragVon D z.kopf.f) S O' U passes R (P.rumpf z.kopf.f) z.kopf.s0
        z.kopf.rho)).folgt (semH S O' U passes R r σ ρ) := by
    intro R O' U hR hA hU hQ
    have := heq R O' U hR hA hU hQ
    rw [hr] at this
    exact this
  have hctr := hSt hok'
  have hgκ : GleichAuf (stabilS P S lok z.kopf.f Λ) (σ.lese Λ os) (W.lese Λ os) :=
    hg0.lese Λ Λ os os
  have hρk : rhoF (σ.lese Λ os) = rhoF (W.lese Λ os) := hrho hok' σ hg0
  have hreqκ := pushS_req hO hRL hQ hS hsp hK hreq hf hv hfa hra hqa hfu hiu r heq' g
    (σ.lese Λ os) (rhoF (σ.lese Λ os)) (fun O' U R e h => hlogik O' U R σ e hg0 h)
  rw [hρk] at hreqκ
  have hctrκ : GleichAuf ((P.requires g).orte ++ (P.ensures g).orte) (σ.lese Λ os)
      (W.lese Λ os) := GleichAuf.mono (fun _ h => hctr h) hgκ
  have hreq0 := req_transfer hreqκ
    (GleichAuf.mono (fun _ h => List.mem_append_left _ h) hctrκ)
  have hsubc : (P.requires g).orte ++ (P.ensures g).orte ⊆ stabilS P S lok z.kopf.f Λc :=
    fun _ h => stabilS_iff (fun L => (hΛc L).symm) (hctr h)
  refine ⟨⟨⟨[], [], [], W.lese Λ os, hreq0, funkV_nil, vertraegeOkR_nil P, kurzVB_nil _,
    funkA_nil, rahmenA_nil, vertragA_nil _ Q, kurzAB_nil _, funkU_nil, invU_nil S, kurzUB_nil _,
    GleichAuf.refl _ _, ⟨hFragS g, fuss_rumpfG P g⟩, fun R O' U _ _ _ _ => ZErgG.folgt_refl _⟩,
    ⟨H, HA, HU, σ.lese Λ os, hreq, hf, hv, kurzVB_mono hk (lese_laenge _ _ _), hfa, hra, hqa,
      kurzAB_mono hka (lese_laenge _ _ _), hfu, hiu, kurzUB_mono hku (lese_laenge _ _ _), hrc hok',
      hreqκ, ⟨hctrκ, hsubc, gleichAuf_stabil_iff hΛc hgκ⟩, ?_⟩, hSt'⟩, hreq0⟩
  intro R O' U hR hA hU hQ
  have hw := hweiter O' U R σ hg0
  rw [hρk] at hw
  exact fortS_mono (F := ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩)
    (heq' R O' U hR hA hU hQ) hw

end Schritte
/-! ## 3. The steps of the replay that record an answer -/


end Gabbro.Grammatik
