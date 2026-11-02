module

public import Grammatik.Speichermodell.Atomar.AtomarReplay.T1
public import Grammatik.Speichermodell.Atomar.AtomarReplay.T2.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Schritte
variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} {m : Mass D} {zyk : D.Fn → D.Fn → Bool}

/-- **A push through a read set `os`** (as `pushS_gen`): the read is recorded; the callee's key
    world is the sequential world after the read (it agrees with the machine's entry world on
    the caller's stable carriers and on `os`). -/
theorem pushSA_gen (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hS : SperrInvOk S)
    {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f) (hM : ∀ f, MassPflicht P passes Q S Tg m zyk f)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    {z : RufFadenG D} {W : World D} (hF : FadenSA P O passes Q S lok Tg m zyk z W)
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
    FadenSA P O passes Q S lok Tg m zyk
      ⟨⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩ :: z.stapel,
        ⟨g, rhoF (W.lese Λ os), W.lese Λ os,
          ⟨false, D.params g, Signatur.anfang D (D.signatur g), rhoF (W.lese Λ os),
            .ende (P.rumpf g)⟩⟩,
        (W.lese Λ os).spur,
        RufEreignisF.eintritt g (rhoF (W.lese Λ os)) (W.lese Λ os) :: z.log⟩
      (W.lese Λ os) ∧
    ReqAmEintritt P g (W.lese Λ os) (rhoF (W.lese Λ os)) := by
  obtain ⟨⟨H, HA, HU, HX, σ, hreq, hf, hv, hm, hk, hfa, hra, hqa, hka, hfu, hiu, hku, ⟨hfx, hkx⟩, hg,
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
  have hmκ : zyk z.kopf.f g = true →
      lexLt (m.wert g (mischT Tg os (σ.lese Λ os) W.speicher) (rhoF (W.lese Λ os)))
        (m.wert z.kopf.f z.kopf.s0 z.kopf.rho) = true := fun hz => by
    have h := pushSA_mass hO hRL hQ hS hsp hM hreq hf hv hm hfa hra hqa hfu hiu hfx' r heq' g
      (mischT Tg os (σ.lese Λ os) W.speicher) (rhoF (mischT Tg os (σ.lese Λ os) W.speicher))
      (fun O' U A R e hPX hHA h => hlogik O' U A R σ _ e hgκ (hrec A hPX hHA) h) hz
    rw [hρk] at h
    exact h
  have hctrκ : GleichAuf ((P.requires g).orte ++ (P.ensures g).orte)
      (mischT Tg os (σ.lese Λ os) W.speicher) (W.lese Λ os) :=
    GleichAuf.mono (fun _ h => List.mem_append_left _ (hctr h)) hgκ
  have hreq0 := req_transfer hreqκ
    (GleichAuf.mono (fun _ h => List.mem_append_left _ h) hctrκ)
  have hsubc : (P.requires g).orte ++ (P.ensures g).orte ⊆ stabilS P S lok z.kopf.f Λc :=
    fun _ h => stabilS_iff (fun L => (hΛc L).symm) (hctr h)
  have hlen : σ.spur.length ≤ (mischT Tg os (σ.lese Λ os) W.speicher).spur.length :=
    lese_laenge _ _ _
  refine ⟨⟨⟨[], [], [], [], W.lese Λ os, hreq0, funkV_nil, vertraegeOkR_nil P, massOkV_nil _ _ _, kurzVBA_nil _,
    funkA_nil, rahmenA_nil, vertragA_nil _ Q, kurzAB_nil _, funkU_nil, invU_nil S, kurzUB_nil _,
    ⟨funkX_nil, kurzX_nil _⟩, GleichAuf.refl _ _, ⟨hFragS g, fuss_rumpfG P g⟩,
    fun R O' U A _ _ _ _ _ _ => ZErgG.folgt_refl _⟩,
    ⟨H, HA, HU, HX', mischT Tg os (σ.lese Λ os) W.speicher, hreq, hf, hv, hm, kurzVBA_mono hk hlen,
      hfa, hra, hqa, kurzAB_mono hka hlen, hfu, hiu, kurzUB_mono hku hlen, ⟨hfx', hkx'⟩, hrc hok',
      hreqκ, hmκ, ⟨hctrκ, hsubc, gleichAuf_stabil_iff hΛc
        (GleichAuf.mono (fun _ h => List.mem_append_left _ h) hgκ)⟩, ?_⟩, hSt'⟩, hreq0⟩
  intro R O' U A hR hA hU hX hHA hQ
  have hw := hweiter O' U A R σ _ hgκ (hrec A hX hHA)
  rw [hρk] at hw
  exact fortSA_mono (F := ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩)
    (heq' R O' U A hR hA hU hX hHA hQ) hw

/-- **An axiom step keeps the replay** (as `fadenS_ax`): its argument read is recorded. -/
theorem fadenSA_ax {z : RufFadenG D} {W : World D}
    (hF : FadenSA P O passes Q S lok Tg m zyk z W)
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
      xm.2 = (O.wirkt a ((W.lese Λ args.orte).fragt (.inl a)) (evalArgs (W.lese Λ args.orte) args
        (W.lese Λ args.orte) ρ)).2)
    (hlok : AxEnsLokal Q)
    (hxq : ∀ v : ErgVal D (D.aerg a), einpassenErg O.zeiger (D.aerg a) xm.2 = some v →
      Q a xm.1 v = true)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (A : AUmwelt D) (σ0 κ : World D), ZeigerGleich O O' →
      leseA A σ0 Λ args.orte = κ →
      O'.wirkt a (κ.fragt (.inl a)) (evalArgs κ args κ ρ) = (axWeltF a (κ.fragt (.inl a)) xm.1, xm.2) →
      (semHA S O' U A passes R r σ0 ρ).folgt
        (semHA S O' U A passes R r' (axWeltF a (κ.fragt (.inl a)) xm.1) ρ')) :
    FadenSA P O passes Q S lok Tg m zyk
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩
      (xm.1.speicher.welt spur') := by
  obtain ⟨⟨H, HA, HU, HX, σ, hreq, hf, hv, hm, hk, hfa, hra, hqa, hka, hfu, hiu, hku, ⟨hfx, hkx⟩, hg,
    hok0, heq⟩, hS⟩ := hF
  have hok' : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) := by
    rw [hr] at hok0; exact hok0
  have hg0 : GleichAuf (stabilS P S lok z.kopf.f Λ) σ W := by rw [hr] at hg; exact hg
  obtain ⟨HX', hfx', hkx', hsub, hrec⟩ := lese_schritt Tg hfx hkx Λ args.orte W.speicher
  have hgκ := mischT_gleichAuf hg0 (hX hok') Λ Λ
  have hlen : σ.spur.length ≤ ((mischT Tg args.orte (σ.lese Λ args.orte) W.speicher).fragt (.inl a)).spur.length :=
    Nat.le_trans (lese_laenge _ _ _) (Nat.le_succ _)
  have hlen2 : σ.spur.length ≤
      (axWeltF a ((mischT Tg args.orte (σ.lese Λ args.orte) W.speicher).fragt (.inl a)) xm.1).spur.length :=
    Nat.le_trans hlen (axWeltF_laenge _ _ _)
  have hlen3 : ((mischT Tg args.orte (σ.lese Λ args.orte) W.speicher).fragt (.inl a)).spur.length ≤
      (axWeltF a ((mischT Tg args.orte (σ.lese Λ args.orte) W.speicher).fragt (.inl a)) xm.1).spur.length :=
    axWeltF_laenge _ _ _
  have hlt : Nonempty (Ereignis D) →
      ((mischT Tg args.orte (σ.lese Λ args.orte) W.speicher).fragt (.inl a)).spur.length <
      (axWeltF a ((mischT Tg args.orte (σ.lese Λ args.orte) W.speicher).fragt (.inl a)) xm.1).spur.length :=
    fun hN => frischSpur_laenge hN _
  have hpa : ¬ Nonempty (Ereignis D) → PasstA O (HA ++ [⟨a,
      (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher).fragt (.inl a),
      evalArgs (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher) args
        (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher) ρ,
      (axWeltF a ((mischT Tg args.orte (σ.lese Λ args.orte) W.speicher).fragt (.inl a)) xm.1, xm.2)⟩]) := by
    intro hN a' σk ρk x hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hka.2 hN a' σk ρk x hm
    · rw [List.mem_singleton] at hm
      cases hm
      rw [hxO hN, welt_eq hN ((mischT Tg args.orte (σ.lese Λ args.orte) W.speicher).fragt (.inl a))
        ((W.lese Λ args.orte).fragt (.inl a)),
        welt_eq hN (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher) (W.lese Λ args.orte)]
      exact Prod.ext (welt_eq hN _ _) rfl
  refine ⟨⟨H, HA ++ [⟨a, (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher).fragt (.inl a),
      evalArgs (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher) args
        (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher) ρ,
      (axWeltF a ((mischT Tg args.orte (σ.lese Λ args.orte) W.speicher).fragt (.inl a)) xm.1, xm.2)⟩], HU, HX',
    axWeltF a ((mischT Tg args.orte (σ.lese Λ args.orte) W.speicher).fragt (.inl a)) xm.1, hreq, hf, hv, hm,
    kurzVBA_mono hk hlen2, ?_, ?_, ?_, ?_,
    hfu, hiu, kurzUB_mono hku hlen2, ⟨hfx', kurzX_mono hkx' (Nat.le_trans (Nat.le_succ _) hlen3)⟩, ?_, hok hok', ?_⟩, hS⟩
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
  · have h1 := axWeltF_gleichAuf (κ := (mischT Tg args.orte (σ.lese Λ args.orte) W.speicher).fragt (.inl a)) a
      (GleichAuf.mono (fun _ h => List.mem_append_left _ h) hgκ) hxm
    exact gleichAuf_stabil_iff hΛ' ⟨fun t ht => h1.1 t ht, fun g hg' => h1.2 g hg'⟩
  · intro R O' U A hR hA hU hXA hHA hQ
    have h1 := heq R O' U A hR (passtA_append hA) hU (passtX_teil hsub hXA) hHA hQ
    rw [hr] at h1
    exact ZErgG.folgt_trans h1
      (hsem O' R U A σ _ hQ.2.2 (hrec A hXA hHA)
        (hA _ _ _ _ (List.mem_append_right _ List.mem_cons_self)))



end Schritte
end Gabbro.Grammatik
