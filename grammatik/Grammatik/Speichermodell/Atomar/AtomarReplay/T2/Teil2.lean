module

public import Grammatik.Speichermodell.Atomar.AtomarReplay.T1
public import Grammatik.Speichermodell.Atomar.AtomarReplay.T2.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Schritte
variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} {m : Mass D} {zyk : D.Fn → D.Fn → Bool}

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
  | assignSlotRef r t ht ho f e hw hL =>
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
      exact Nat.le_succ _
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
  | axiomCall => simp only [Stmt.istAxiom, Bool.true_eq_false] at ha
  | ret e hp => simp only [execStmt, reduceCtorEq] at h
  | retWhy r hp => simp only [execStmt, reduceCtorEq] at h
  | leave hl => simp only [execStmt, reduceCtorEq] at h
  | next hl => simp only [execStmt, reduceCtorEq] at h
  | _ => simp only [Stmt.istBlatt, Bool.false_eq_true] at hb

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
    (hF : FadenSA P O passes Q S lok Tg m zyk z W) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {ρ : Env D Γ} {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (s : Stmt D (vertragVon D z.kopf.f) l Γ Λ Λ') (K : GRest D (vertragVon D z.kopf.f) l Γ Λ')
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (A : AUmwelt D) (σ : World D),
      semHA S O' U A passes R r σ ρ = weiterHA S O' U A passes R K (execStmtHA S O' U A passes R s σ ρ))
    (hok : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      stmtOrteP P s ⊆ fussOrteG P z.kopf.f ∧ K.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f))
    (hleaf : s.istBlatt = true) (σ' : World D) (ρ' : Env D Γ)
    (hstep : execStmt O passes keinRuf s W ρ = .ok σ' ρ') :
    FadenSA P O passes Q S lok Tg m zyk
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
          have hfr := (hO a ((W.lese Λ args.orte).fragt (.inl a))
            (evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ')).1
          rw [← e1] at hfr
          refine fadenSA_ax hF hr ρ' K σ'.spur hΛ' a args
            (fun h' => orte_stabilX (hFS _) args.orte_darf (hok h').1) (fun h' => (hok h').2)
            (σ', (O.wirkt a ((W.lese Λ args.orte).fragt (.inl a))
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
      | _ => simp only [Stmt.istAxiom, Bool.false_eq_true] at hax

/-- **The acquire keeps the replay** (as `fadenS_locks`). -/
theorem fadenSA_locks {z : RufFadenG D} {W : World D} (hF : FadenSA P O passes Q S lok Tg m zyk z W)
    {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)} (L : D.Lock)
    (hrL : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D (vertragVon D z.kopf.f) l Γ (Res.held L :: Λ) (Res.held L :: Λ))
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.locks L hrL body) rest) k⟩)
    (hinv : S.inv L W.speicher = true) (spur' : List (Ereignis D)) :
    FadenSA P O passes Q S lok Tg m zyk
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
        ⟨l, Γ, Res.held L :: Λ, ρ, .dann body (.frei L (.dann rest k))⟩⟩, spur', z.log⟩
      (W.speicher.welt spur') := by
  obtain ⟨⟨H, HA, HU, HX, σ, hreq, hf, hv, hm, hk, hfa, hra, hqa, hka, hfu, hiu, hku, ⟨hfx, hkx⟩, hg,
    hok, heq⟩, hS⟩ := hF
  rw [hr] at hg hok
  simp only at hg hok
  obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
  have hlen : σ.spur.length < ((mischU S L σ W.speicher).nimmt L).spur.length := by
    show σ.spur.length < (Ereignis.nimmt L _ :: σ.spur).length
    exact Nat.lt_succ_self _
  refine ⟨⟨H, HA, HU ++ [(L, σ, W.speicher)], HX, (mischU S L σ W.speicher).nimmt L, hreq, hf, hv, hm,
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
