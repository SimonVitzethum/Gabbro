module

public import Grammatik.Speichermodell.Atomar.AtomarReplay.T1

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

section Schritte

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} {m : Mass D} {zyk : D.Fn → D.Fn → Bool}

theorem kopfSA_okS {F : RufRahmenG D} {W : World D} (h : KopfSA P O passes Q S lok Tg m zyk F W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D F.f) l Γ Λ} (hr : F.rest = ⟨l, Γ, Λ, ρ, r⟩) :
    r.okS P (fussOrteG P F.f) (sicher P lok F.f) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hok, _⟩ := h
  rw [hr] at hok
  exact hok

/-- **A head-local step** (as `fadenS_lokalQ`): the step may extend the record of atomic reads
    (a read of a shared atomic), and its residue semantics is followed for every environment
    repeating the extended record. -/
theorem fadenSA_lokalQ {z : RufFadenG D} {W W' : World D}
    (hF : FadenSA P O passes Q S lok Tg m zyk z W)
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
    FadenSA P O passes Q S lok Tg m zyk
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩ W' := by
  obtain ⟨⟨H, HA, HU, HX, σ, hreq, hf, hv, hm, hk, hfa, hra, hqa, hka, hfu, hiu, hku, ⟨hfx, hkx⟩, hg,
    hok, heq⟩, hS⟩ := hF
  have hok' : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) := by rw [hr] at hok; exact hok
  have hg0 : GleichAuf (stabilS P S lok z.kopf.f Λ) σ W := by rw [hr] at hg; exact hg
  obtain ⟨σ', HX', hfx', hkx', hsub, hl, hg', hok'', hsem⟩ := hstep σ HX hfx hkx hg0 hok'
  refine ⟨⟨H, HA, HU, HX', σ', hreq, hf, hv, hm, kurzVBA_mono hk hl, hfa, hra, hqa, kurzAB_mono hka hl,
    hfu, hiu, kurzUB_mono hku hl, ⟨hfx', hkx'⟩, hg', hok'', fun R O' U A hR hA hU hX hHA hQ => ?_⟩,
    hS⟩
  have h1 := heq R O' U A hR hA hU (passtX_teil hsub hX) hHA hQ
  rw [hr] at h1
  exact ZErgG.folgt_trans h1 (hsem R O' U A hX hHA hQ)

/-- A head-local step with no read of a shared atomic and a semantics that holds for every
    oracle and environment (the record stays). -/
theorem fadenSA_lokal {z : RufFadenG D} {W W' : World D}
    (hF : FadenSA P O passes Q S lok Tg m zyk z W)
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
    FadenSA P O passes Q S lok Tg m zyk
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩ W' :=
  fadenSA_lokalQ hF hr ρ' r' spur' fun σ HX hfx hkx hg hok => by
    obtain ⟨_, hg', hok', hsem⟩ := hstep σ hg hok
    exact ⟨σ, HX, hfx, hkx, fun _ h => h, Nat.le_refl _, hg', hok',
      fun R O' U A _ _ _ => hsem R O' U A⟩

/-- **A head-local step that READS the list `X`** (every carrier of it stable or a shared
    atomic): the read is recorded, the sequential world after it holds the machine's presented
    values at the read shared atomics (`mischT`), and the step continues from there. -/
theorem fadenSA_lese {z : RufFadenG D} {W W' : World D}
    (hF : FadenSA P O passes Q S lok Tg m zyk z W)
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
    FadenSA P O passes Q S lok Tg m zyk
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩ W' := by
  refine fadenSA_lokalQ hF hr ρ' r' spur' fun σ HX hfx hkx hg hok => ?_
  obtain ⟨HX', hfx', hkx', hsub, hrec⟩ := lese_schritt Tg hfx hkx Λr X W.speicher
  have hgX := mischT_gleichAuf hg (hX hok) Λr Λr
  obtain ⟨σ', hl, hg', hok', hsem⟩ := hstep _ hgX hok
  refine ⟨σ', HX', hfx', kurzX_mono hkx' hl, hsub, Nat.le_trans (lese_laenge σ Λr X) hl, hg', hok',
    fun R O' U A hPX hHA hQ => hsem R O' U A σ hQ hg (hrec A hPX hHA)⟩

/-- **A question to the outside, then reads** (`fadenSA_lese` after `World.fragt`): the register and visibility
    steps record `Ereignis.fremd` before they read. -/
theorem fadenSA_fragtLese {z : RufFadenG D} {W W' : World D}
    (hF : FadenSA P O passes Q S lok Tg m zyk z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    {l' : Bool} {Γ' : Ctx} {Λ' : List (Res D)} (ρ' : Env D Γ')
    (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (spur' : List (Ereignis D))
    (q : D.Ax ⊕ D.Reg ⊕ D.Glob) (Λr : List (Res D)) (X : List (D.Tab ⊕ D.Glob))
    (hX : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      ∀ c ∈ X, c ∈ stabilS P S lok z.kopf.f Λ ∨ Tg c)
    (hstep : ∀ σ : World D, GleichAuf (stabilS P S lok z.kopf.f Λ ++ X) σ ((W.fragt q).lese Λr X) →
      r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      ∃ σ' : World D, σ.spur.length ≤ σ'.spur.length ∧
        GleichAuf (stabilS P S lok z.kopf.f Λ') σ' W' ∧
        r'.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) ∧
        ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
          (U : Umwelt D) (A : AUmwelt D) (σ0 : World D), GleichRS O O' →
          GleichAuf (stabilS P S lok z.kopf.f Λ) σ0 W → leseA A (σ0.fragt q) Λr X = σ →
          (semHA S O' U A passes R r σ0 ρ).folgt (semHA S O' U A passes R r' σ' ρ')) :
    FadenSA P O passes Q S lok Tg m zyk
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩ W' := by
  refine fadenSA_lokalQ hF hr ρ' r' spur' fun σ HX hfx hkx hg hok => ?_
  obtain ⟨HX', hfx', hkx', hsub, hrec⟩ :=
    lese_schritt (σ := σ.fragt q) Tg hfx (kurzX_mono hkx (Nat.le_succ _)) Λr X W.speicher
  have hgX := mischT_gleichAuf (σ := σ.fragt q) (W := W.fragt q) hg (hX hok) Λr Λr
  obtain ⟨σ', hl, hg', hok', hsem⟩ := hstep _ hgX hok
  refine ⟨σ', HX', hfx', kurzX_mono hkx' hl, hsub,
    Nat.le_trans (Nat.le_succ _) (Nat.le_trans (lese_laenge (σ.fragt q) Λr X) hl), hg', hok',
    fun R O' U A hPX hHA hQ => hsem R O' U A σ hQ hg (hrec A hPX hHA)⟩

/-- Memory moved outside the head's stable carriers keeps the replay. -/
theorem fadenSA_speicher {z : RufFadenG D} {W W' : World D}
    (hF : FadenSA P O passes Q S lok Tg m zyk z W)
    (hw : ∀ c ∈ stabilS P S lok z.kopf.f z.kopf.rest.2.2.1,
      TraegerGleich W'.speicher W.speicher c) :
    FadenSA P O passes Q S lok Tg m zyk z W' := by
  obtain ⟨⟨H, HA, HU, HX, σ, hreq, hf, hv, hm, hk, hfa, hra, hqa, hka, hfu, hiu, hku, hx, hg, hok,
    heq⟩, hS⟩ := hF
  refine ⟨⟨H, HA, HU, HX, σ, hreq, hf, hv, hm, hk, hfa, hra, hqa, hka, hfu, hiu, hku, hx,
    ⟨fun t ht => ?_, fun g hg' => ?_⟩, hok, heq⟩, hS⟩
  · exact (hg.1 t ht).trans (hw (.inl t) ht).symm
  · exact (hg.2 g hg').trans (hw (.inr g) hg').symm

/-- **The return leg** (as `popS_ens`): the returned expression may read shared atomics; the
    read is answered by a record made here. -/
theorem popSA_ens (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hS : SperrInvOk S)
    {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f) {G : RufRahmenG D}
    {W : World D} (hG : KopfSA P O passes Q S lok Tg m zyk G W) {lr : Bool} {Γ : Ctx}
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
  obtain ⟨H, HA, HU, HX, σ, hreq, hf, hv, hm, _, hfa, hra, hqa, _, hfu, hiu, _, ⟨hfx, hkx⟩, hg, _,
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

end Schritte
end Gabbro.Grammatik
