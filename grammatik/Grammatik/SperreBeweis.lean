/-
  File:      Grammatik/SperreBeweis.lean
  Subject:   The replay of `ziel_ort_ganz` (`ZielOrtRahmenBeweis.lean`) with
             LOCK INVARIANTS: the sequential side runs `execStmtH`
             (`SperreSem.lean`), the records also keep the environment's move
             at every acquire, and the sequential world agrees with the
             machine world on the STABLE carriers of the frame at its current
             holdings (`stabilS`, `SperreFuss.lean`), not on the whole
             footprint.

  Changes against `KopfR`/`WarteR`/`StapelR`/`FadenR`:
  * a third record `HU` of acquires (`UEintrag`: lock, key world, the
    memory the protected carriers were taken from), functional, below the
    sequential trace, every source meeting the lock's invariant (`InvU`);
    the sequential runs quantify over the moves repeating it (`PasstU`);
  * agreement on `stabilS P S lok F.f Λ`, where `Λ` is the residue's static
    holdings: it grows at an acquire (the new record takes the protected
    carriers from the machine, `fadenS_locks`) and shrinks at a release;
  * the release steps (`fadenS_frei`, `fadenS_peelFrei`) use the second
    clause of the obligation: the head's prediction is no `logik` outcome
    (`kopfS_keineLogik`), so the release check passes at the sequential
    world, hence (the protected carriers are stable while the lock is held)
    at the machine world (`kopfS_frei_inv`).
-/
import Grammatik.SperreFuss

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 0. The carriers a leaf reads carry their guards -/

theorem Stmt.blatt_darf (P : Programm D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (hb : s.istBlatt = true) : ∀ o ∈ stmtOrteP P s, OrtDarf Λ o := by
  intro o ho
  cases s with
  | assignSlot t f i e hw hL =>
      simp only [stmtOrteP, List.mem_append] at ho
      rcases ho with ho | ho
      · exact i.orte_darf o ho
      · exact e.orte_darf o ho
  | assignDurch p t ht f i e hw hL =>
      simp only [stmtOrteP, List.mem_append] at ho
      rcases ho with (ho | ho) | ho
      · exact p.orte_darf o ho
      · exact i.orte_darf o ho
      · exact e.orte_darf o ho
  | assignGlob g e hw hL => exact e.orte_darf o ho
  | schreibBytes t f hf n i hlo hhi e hw hL =>
      simp only [stmtOrteP, List.mem_append] at ho
      rcases ho with ho | ho
      · exact i.orte_darf o ho
      · exact e.orte_darf o ho
  | assignVar x e => exact e.orte_darf o ho
  | uebergang t f hτ i von nach hn he hw hL =>
      simp only [stmtOrteP, List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact hL
      · exact i.orte_darf o ho
  | axiomCall a args h hw hg hd hgd => exact args.orte_darf o ho
  | regSchreib r hk e => exact e.orte_darf o ho
  | transition => simp [stmtOrteP] at ho
  | publish g e payload hp hw hL => exact e.orte_darf o ho
  | advances => simp [stmtOrteP] at ho
  | retires => simp [stmtOrteP] at ho
  | ret e hp => exact e.orte_darf o ho
  | retGrund => simp [stmtOrteP] at ho
  | leave => simp [stmtOrteP] at ho
  | next => simp [stmtOrteP] at ho
  | _ => simp [Stmt.istBlatt] at hb

/-! ## 1. The replay invariants -/

section Inv

variable (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D) (S : SperrInv D)
  (lok : D.Tab ⊕ D.Glob → Bool)

/-- How a suspended frame continues once its pending call is answered (as
    `FortV`), over the semantics with lock invariants. -/
def FortS (F : RufRahmenG D) (g : D.Fn) (X : ZErg (vertragVon D F.f))
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D) (U : Umwelt D) :
    RufAusgang g → Prop
  | .ok σa v =>
      (F.wartend = false → X.folgt (semH S O' U passes R F.rest.2.2.2.2 σa F.rest.2.2.2.1)) ∧
      (∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
          (restb : Block D (vertragVon D F.f) l (τ :: Γ) Λ Λ')
          (k : GRest D (vertragVon D F.f) l Γ Λ') (ρc : Env D Γ),
        (F.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩ ∨
          ∃ (n : Nat) (err : Endblock D (vertragVon D F.f) l (.grund n :: Γ) Λ),
            F.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩) →
        ∀ he : D.erg g = some τ,
          X.folgt (semH S O' U passes R (.dann restb (.schrumpf k)) σa (.cons (ergWert he v) ρc)))
  | .grund σa r =>
      ∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty) (n : Nat)
        (err : Endblock D (vertragVon D F.f) l (.grund n :: Γ) Λ)
        (restb : Block D (vertragVon D F.f) l (τ :: Γ) Λ Λ')
        (k : GRest D (vertragVon D F.f) l Γ Λ') (ρc : Env D Γ),
        F.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩ →
        ∀ hn : D.gruende g = n,
          X.folgt (semH S O' U passes R (.ende err) σa (.cons (Fin.cast hn r) ρc))
  | _ => True

/-- **The replay of a head frame** `F` whose thread world is `W`, with lock
    invariants. -/
def KopfS (F : RufRahmenG D) (W : World D) : Prop :=
  ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (HU : List (UEintrag D)) (σ : World D),
    ReqAmEintritt P F.f F.s0 F.rho ∧ FunkV H ∧ VertraegeOkR P H ∧ KurzV σ.spur.length H ∧
    FunkA HA ∧ RahmenA HA ∧ VertragA Q HA ∧ KurzA σ.spur.length HA ∧
    FunkU HU ∧ InvU S HU ∧ KurzU σ.spur.length HU ∧
    GleichAuf (stabilS P S lok F.f F.rest.2.2.1) σ W ∧
    F.rest.2.2.2.2.okS P (fussOrteG P F.f) (sicher P lok F.f) ∧
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
      (U : Umwelt D),
      PasstV R H → PasstA O' HA → PasstU S U HU → GleichRS O O' →
      (zErg (execEndH (V := vertragVon D F.f) S O' U passes R (P.rumpf F.f) F.s0 F.rho)).folgt
        (semH S O' U passes R F.rest.2.2.2.2 σ F.rest.2.2.2.1)

/-- **The replay of a suspended frame** `F` waiting for the callee with key
    `G`. The key world agrees with the callee's machine entry world on the
    frame's stable carriers at its holdings, which contain the callee's
    contract carriers. -/
def WarteS (F : RufRahmenG D) (G : Σ f : D.Fn, Env D (D.params f) × World D) : Prop :=
  ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (HU : List (UEintrag D)) (κ : World D),
    ReqAmEintritt P F.f F.s0 F.rho ∧ FunkV H ∧ VertraegeOkR P H ∧ KurzV κ.spur.length H ∧
    FunkA HA ∧ RahmenA HA ∧ VertragA Q HA ∧ KurzA κ.spur.length HA ∧
    FunkU HU ∧ InvU S HU ∧ KurzU κ.spur.length HU ∧
    F.rest.2.2.2.2.okS P (fussOrteG P F.f) (sicher P lok F.f) ∧
    ReqAmEintritt P G.1 κ G.2.1 ∧
    (GleichAuf ((P.requires G.1).orte ++ (P.ensures G.1).orte) κ G.2.2 ∧
      (P.requires G.1).orte ++ (P.ensures G.1).orte ⊆ stabilS P S lok F.f F.rest.2.2.1 ∧
      GleichAuf (stabilS P S lok F.f F.rest.2.2.1) κ G.2.2) ∧
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
      (U : Umwelt D),
      PasstV R H → PasstA O' HA → PasstU S U HU → GleichRS O O' →
      FortS passes S F G.1
        (zErg (execEndH (V := vertragVon D F.f) S O' U passes R (P.rumpf F.f) F.s0 F.rho)) R O' U
        (R G.1 κ G.2.1)

def StapelS : (Σ f : D.Fn, Env D (D.params f) × World D) → List (RufRahmenG D) → Prop
  | _, [] => True
  | G, F :: rest => WarteS P O passes Q S lok F G ∧ StapelS (RufSchluesselG F) rest

def FadenS (z : RufFadenG D) (W : World D) : Prop :=
  KopfS P O passes Q S lok z.kopf W ∧ StapelS P O passes Q S lok (RufSchluesselG z.kopf) z.stapel

def ZielInvS (M : RufMaschineG D) : Prop :=
  (∀ t, FadenS P O passes Q S lok (M.faeden t) (M.weltVon t)) ∧ ∀ t, LogOk P (M.faeden t).log

end Inv

/-- `FortS` is monotone in the predicted result. -/
theorem fortS_mono {passes : Nat} {S : SperrInv D} {F : RufRahmenG D} {g : D.Fn}
    {X Y : ZErg (vertragVon D F.f)}
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f} {O' : Orakel D} {U : Umwelt D}
    (hXY : X.folgt Y) :
    ∀ {a : RufAusgang g}, FortS passes S F g Y R O' U a → FortS passes S F g X R O' U a
  | .ok _ _, h => ⟨fun hw => ZErg.folgt_trans hXY (h.1 hw),
      fun l Γ Λ Λ' τ restb k ρc hc he => ZErg.folgt_trans hXY (h.2 l Γ Λ Λ' τ restb k ρc hc he)⟩
  | .grund _ _, h => fun l Γ Λ Λ' τ n err restb k ρc hc hn =>
      ZErg.folgt_trans hXY (h l Γ Λ Λ' τ n err restb k ρc hc hn)
  | .logik _, _ => trivial
  | .hardware _, _ => trivial

/-! ## 2. The steps of the replay -/

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
  refine ⟨⟨H, HA, HU, σ', hreq, hf, hv, kurzV_mono hk hl, hfa, hra, hqa, kurzA_mono hka hl, hfu,
    hiu, kurzU_mono hku hl, hg', hok'', fun R O' U hR hA hU hQ => ?_⟩, hS⟩
  have h1 := heq R O' U hR hA hU hQ
  rw [hr] at h1
  exact ZErg.folgt_trans h1 (hsem R O' U hQ)

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
  have h2 := ZErg.folgt_zurueck (ZErg.folgt_trans h1 (ZErg.folgt_of_gleich (hsem _ _ _ σ)))
  obtain ⟨σ'', hex, hsg⟩ := zErg_gleich_zurueck h2
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
    (hfa : FunkA HA) (hra : RahmenA HA) (hqa : VertragA Q HA) (hfu : FunkU HU) (hiu : InvU S HU)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    (r : GRest D (vertragVon D F.f) l Γ Λ)
    (heq : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
      (U : Umwelt D), PasstV R H → PasstA O' HA → PasstU S U HU → GleichRS O O' →
      (zErg (execEndH (V := vertragVon D F.f) S O' U passes R (P.rumpf F.f) F.s0 F.rho)).folgt
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
      have hex := zErg_gleich_logik (ZErg.folgt_logik h1)
      exact ((hK F.f).1 (orakelAus O HA) (orakelAus_rahmen hO hra) (regLokal_orakelAus hRL HA)
        (orakelAus_vertrag hQ hqa) (umweltAus S sp HU) (umweltAus_ok hS hsp hiu) (rufAusV H)
        (rufAusV_rahmen hv) (rufAusV_ohneVorbedingung hv.1) F.s0 F.rho hreq).2 g hex

/-- **The caller resumes** after its pending call to `G` (as `popR_kopf`):
    the answer is recorded with the answer world `rahmenWelt`, and the frame
    becomes a replayed head whose residue has the same held locks. -/
theorem popS_kopf (e0 : Ereignis D) {F : RufRahmenG D}
    {G : Σ f : D.Fn, Env D (D.params f) × World D}
    (hW : WarteS P O passes Q S lok F G) (s1 : World D) (mk : World D → RufAusgang G.1)
    (hmk : (∃ v, (∀ σa, mk σa = .ok σa v) ∧ EnsAmRueck P G.1 G.2.2 s1 G.2.1 v) ∨
      (∃ r, ∀ σa, mk σa = .grund σa r))
    (hRah : GleichOhne G.1 (stabilS P S lok F.f F.rest.2.2.1) G.2.2 s1)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ' : Env D Γ) (r' : GRest D (vertragVon D F.f) l Γ Λ)
    (hΛ : ∀ L, Res.held L ∈ Λ → Res.held L ∈ F.rest.2.2.1)
    (hok' : F.rest.2.2.2.2.okS P (fussOrteG P F.f) (sicher P lok F.f) →
      r'.okS P (fussOrteG P F.f) (sicher P lok F.f))
    (hwahl : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
      (U : Umwelt D) (σa : World D) (X : ZErg (vertragVon D F.f)),
      FortS passes S F G.1 X R O' U (mk σa) → X.folgt (semH S O' U passes R r' σa ρ'))
    (W' : World D) (hW' : W'.slots = s1.slots ∧ W'.globs = s1.globs) :
    KopfS P O passes Q S lok ⟨F.f, F.rho, F.s0, ⟨l, Γ, Λ, ρ', r'⟩⟩ W' := by
  obtain ⟨H, HA, HU, κ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hfu, hiu, hku, hok, hreqκ,
    ⟨hglκ, hsub, hfussκ⟩, hcont⟩ := hW
  have hσa : GleichAuf (stabilS P S lok F.f F.rest.2.2.1) (rahmenWelt e0 G.1 κ s1) s1 :=
    rahmenWelt_gleichAuf e0 G.1 hfussκ hRah
  have hlen := rahmenWelt_laenge e0 G.1 κ s1
  have hmem : (⟨G.1, κ, G.2.1, mk (rahmenWelt e0 G.1 κ s1)⟩ : EintragV D) ∈
      H ++ [⟨G.1, κ, G.2.1, mk (rahmenWelt e0 G.1 κ s1)⟩] :=
    List.mem_append_right _ List.mem_cons_self
  refine ⟨H ++ [⟨G.1, κ, G.2.1, mk (rahmenWelt e0 G.1 κ s1)⟩], HA, HU, rahmenWelt e0 G.1 κ s1,
    hreq, funkV_append hf hk _ (Nat.le_refl _), ⟨?_, ?_⟩, ?_, hfa, hra, hqa,
    kurzA_mono hka (Nat.le_of_lt hlen), hfu, hiu, kurzU_mono hku (Nat.le_of_lt hlen), ?_,
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
      have e : σ' = rahmenWelt e0 G.1 κ s1 := by
        rcases hmk with ⟨v, hv', _⟩ | ⟨rr, hr'⟩
        · rw [hv'] at hw; cases hw; rfl
        · rw [hr'] at hw; cases hw
      subst e
      exact ⟨rahmenWelt_rahmen e0 G.1 κ s1, rahmenWelt_offen e0 G.1 κ s1⟩
  · intro e hm
    rcases List.mem_append.mp hm with hm | hm
    · exact Nat.lt_trans (hk e hm) hlen
    · rw [List.mem_singleton] at hm
      subst hm
      exact hlen
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
      (zErg (execEndH (V := vertragVon D z.kopf.f) S O' U passes R (P.rumpf z.kopf.f) z.kopf.s0
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
  refine ⟨⟨⟨[], [], [], W.lese Λ os, hreq0, funkV_nil, vertraegeOkR_nil P, kurzV_nil _,
    funkA_nil, rahmenA_nil, vertragA_nil Q, kurzA_nil _, funkU_nil, invU_nil S, kurzU_nil _,
    GleichAuf.refl _ _, ⟨hFragS g, fuss_rumpfG P g⟩, fun R O' U _ _ _ _ => ZErg.folgt_refl _⟩,
    ⟨H, HA, HU, σ.lese Λ os, hreq, hf, hv, kurzV_mono hk (lese_laenge _ _ _), hfa, hra, hqa,
      kurzA_mono hka (lese_laenge _ _ _), hfu, hiu, kurzU_mono hku (lese_laenge _ _ _), hrc hok',
      hreqκ, ⟨hctrκ, hsubc, gleichAuf_stabil_iff hΛc hgκ⟩, ?_⟩, hSt'⟩, hreq0⟩
  intro R O' U hR hA hU hQ
  have hw := hweiter O' U R σ hg0
  rw [hρk] at hw
  exact fortS_mono (F := ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩)
    (heq' R O' U hR hA hU hQ) hw

end Schritte

/-! ## 3. The steps of the replay that record an answer -/

section Schritte2

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool}

/-- **An axiom step keeps the replay** (as `fadenR_ax`). -/
theorem fadenS_ax (e0 : Ereignis D) {z : RufFadenG D} {W : World D}
    (hF : FadenS P O passes Q S lok z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    {l' : Bool} {Γ' : Ctx} {Λ' : List (Res D)} (ρ' : Env D Γ')
    (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (spur' : List (Ereignis D))
    (hΛ' : ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ)
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
    (hok : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      r'.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f))
    (xm : World D × Int) (hxm : Rahmen (D.aschreibt a) (D.agschreibt a) (W.lese Λ args.orte) xm.1)
    (hlok : AxEnsLokal Q)
    (hxq : ∀ v : ErgVal D (D.aerg a), einpassenErg (D.aerg a) xm.2 = some v → Q a xm.1 v = true)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (σ : World D),
      O'.wirkt a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
        (axWelt e0 a (σ.lese Λ args.orte) xm.1, xm.2) →
      (semH S O' U passes R r σ ρ).folgt
        (semH S O' U passes R r' (axWelt e0 a (σ.lese Λ args.orte) xm.1) ρ')) :
    FadenS P O passes Q S lok
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩
      (xm.1.speicher.welt spur') := by
  obtain ⟨⟨H, HA, HU, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hfu, hiu, hku, hg, hok0, heq⟩, hS⟩ :=
    hF
  have hok' : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) := by
    rw [hr] at hok0; exact hok0
  have hg0 : GleichAuf (stabilS P S lok z.kopf.f Λ) σ W := by rw [hr] at hg; exact hg
  have hlen : σ.spur.length ≤ (σ.lese Λ args.orte).spur.length := lese_laenge _ _ _
  refine ⟨⟨H, HA ++ [⟨a, σ.lese Λ args.orte,
      evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ,
      (axWelt e0 a (σ.lese Λ args.orte) xm.1, xm.2)⟩], HU,
    axWelt e0 a (σ.lese Λ args.orte) xm.1, hreq, hf, hv,
    kurzV_mono hk (Nat.le_trans hlen (Nat.le_succ _)), funkA_append hfa hka _ hlen, ?_, ?_, ?_,
    hfu, hiu, kurzU_mono hku (Nat.le_trans hlen (Nat.le_succ _)), ?_, hok hok', ?_⟩, hS⟩
  · intro a' σk ρk x hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hra a' σk ρk x hm
    · rw [List.mem_singleton] at hm
      cases hm
      exact axWelt_rahmen e0 a _ _
  · intro a' σk ρk x hm v hv
    rcases List.mem_append.mp hm with hm | hm
    · exact hqa a' σk ρk x hm v hv
    · rw [List.mem_singleton] at hm
      cases hm
      exact axWelt_vertrag hlok e0 a _ _ v (hxq v hv)
  · intro e hm
    rcases List.mem_append.mp hm with hm | hm
    · exact Nat.lt_of_lt_of_le (hka e hm) (Nat.le_trans hlen (Nat.le_succ _))
    · rw [List.mem_singleton] at hm
      subst hm
      exact Nat.lt_succ_self _
  · have h1 := axWelt_gleichAuf e0 a (hg0.lese Λ Λ args.orte args.orte) hxm
    exact gleichAuf_stabil_iff hΛ' ⟨fun t ht => h1.1 t ht, fun g hg' => h1.2 g hg'⟩
  · intro R O' U hR hA hU hQ
    have h1 := heq R O' U hR (passtA_append hA) hU hQ
    rw [hr] at h1
    exact ZErg.folgt_trans h1
      (hsem O' R U σ (hA _ _ _ _ (List.mem_append_right _ List.mem_cons_self)))

/-- **A leaf step keeps the replay**: a non-axiom leaf by leaf locality, an
    axiom call by recording its answer. -/
theorem fadenS_blatt (e0 : Ereignis D) (hO : GutO O) (hQ : AxVertragO Q O)
    (hlok : AxEnsLokal Q) (hFS : ∀ f, FussS P S lok f) {z : RufFadenG D} {W : World D}
    (hF : FadenS P O passes Q S lok z W) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (s : Stmt D (vertragVon D z.kopf.f) l Γ Λ Λ') (K : GRest D (vertragVon D z.kopf.f) l Γ Λ')
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (U : Umwelt D) (σ : World D),
      semH S O' U passes R r σ ρ = weiterH S O' U passes R K (execStmtH S O' U passes R s σ ρ))
    (hok : r.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f) →
      stmtOrteP P s ⊆ fussOrteG P z.kopf.f ∧ K.okS P (fussOrteG P z.kopf.f) (sicher P lok z.kopf.f))
    (hleaf : s.istBlatt = true) (σ' : World D) (ρ' : Env D Γ)
    (hstep : execStmt O passes keinRuf s W ρ = .ok σ' ρ') :
    FadenS P O passes Q S lok
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, Λ', ρ', K⟩⟩, σ'.spur, z.log⟩
      (σ'.speicher.welt σ'.spur) := by
  have hΛ' : ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ := s.held_iff
  cases hax : s.istAxiom with
  | false =>
      refine fadenS_lokal hF hr ρ' K σ'.spur (fun σ hg hok' => ?_)
      obtain ⟨hs, hK⟩ := hok hok'
      have hs' : stmtOrteP P s ⊆ stabilS P S lok z.kopf.f Λ :=
        orte_stabil (hFS _) (s.blatt_darf P hleaf) hs
      obtain ⟨σs, hes, hgs, hls⟩ := blatt_lokalV P O passes s hleaf hax hs' hg hstep
      refine ⟨σs, hls, gleichAuf_stabil_iff hΛ' ⟨fun t ht => hgs.1 t ht, fun g hg' => hgs.2 g hg'⟩,
        hK, fun R O' U => ?_⟩
      rw [hsem, execStmtH_blatt S O' U passes R s hleaf, hes]
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
          refine fadenS_ax e0 hF hr ρ' K σ'.spur hΛ' a args (fun h' => (hok h').2)
            (σ', (O.wirkt a (W.lese Λ args.orte)
              (evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ')).2) hfr hlok
            (fun v hv => by
              rw [e1]
              exact hQ a _ _ v hv) ?_
          intro O' R U σ hw
          rw [hsem]
          apply ZErg.folgt_of_eq
          simp only [execStmtH, axiomAntwort, hw]
          simp only [hu]
          rfl
      | _ => simp [Stmt.istAxiom] at hax

/-- **The acquire keeps the replay.** At `locks L { body }` with `L` free in
    the machine, the invariant of `L` holds at the machine memory
    (`SperrInvG`, `SperreMaschine.lean`), so the move "protected carriers of
    `L` from the machine" is in the class; it is recorded at the sequential
    key, the new sequential world takes the protected carriers from the
    machine, and the stable set grows by them. -/
theorem fadenS_locks {z : RufFadenG D} {W : World D} (hF : FadenS P O passes Q S lok z W)
    {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)} (L : D.Lock)
    (hrL : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D (vertragVon D z.kopf.f) l Γ (Res.held L :: Λ) (Res.held L :: Λ))
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.locks L hrL body) rest) k⟩)
    (hinv : S.inv L W.speicher = true) (spur' : List (Ereignis D)) :
    FadenS P O passes Q S lok
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
        ⟨l, Γ, Res.held L :: Λ, ρ, .dann body (.frei L (.dann rest k))⟩⟩, spur', z.log⟩
      (W.speicher.welt spur') := by
  obtain ⟨⟨H, HA, HU, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hfu, hiu, hku, hg, hok, heq⟩, hS⟩ :=
    hF
  rw [hr] at hg hok
  simp only at hg hok
  obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
  have hlen : σ.spur.length < ((mischU S L σ W.speicher).nimmt L).spur.length := by
    show σ.spur.length < (Ereignis.nimmt L _ :: σ.spur).length
    exact Nat.lt_succ_self _
  refine ⟨⟨H, HA, HU ++ [(L, σ, W.speicher)], (mischU S L σ W.speicher).nimmt L, hreq, hf, hv,
    kurzV_mono hk (Nat.le_of_lt hlen), hfa, hra, hqa, kurzA_mono hka (Nat.le_of_lt hlen),
    funkU_append hfu hku _ (Nat.le_refl _), invU_append hiu L σ W.speicher hinv, ?_, ?_,
    ⟨hks, hss, hrest⟩, ?_⟩, hS⟩
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact Nat.lt_trans (hku e he) hlen
    · rw [List.mem_singleton] at he
      subst he
      exact hlen
  · -- agreement on the grown stable set
    have key : ∀ c ∈ stabilS P S lok z.kopf.f (Res.held L :: Λ),
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
  · intro R O' U hR hA hU hQ
    have h1 := heq R O' U hR hA (passtU_append hU) hQ
    rw [hr] at h1
    simp only at h1
    refine ZErg.folgt_trans h1 (ZErg.folgt_of_eq ?_)
    rw [semH_locks S O' U passes R L hrL body rest k σ ρ,
      hU L σ W.speicher (List.mem_append_right _ List.mem_cons_self)]

end Schritte2

/-! ## 4. The head never predicts a `logik` outcome; the release steps -/

section Frei

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool}

/-- **The head's prediction is never a `logik` outcome** (as
    `kopfR_keineLogik`): against the record handler with hardware default,
    the record oracle and the record's environment move. -/
theorem kopfS_keineLogik (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f) {F : RufRahmenG D} {W : World D}
    (hG : KopfS P O passes Q S lok F W) :
    ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (HU : List (UEintrag D)) (σ : World D),
      GleichAuf (stabilS P S lok F.f F.rest.2.2.1) σ W ∧
      F.rest.2.2.2.2.okS P (fussOrteG P F.f) (sicher P lok F.f) ∧
      ∀ e : Logik D,
        semH S (orakelAus O HA) (umweltAus S sp HU) passes (rufAusL H) F.rest.2.2.2.2 σ
          F.rest.2.2.2.1 ≠ .logik e := by
  obtain ⟨H, HA, HU, σ, hreq, hf, hv, _, hfa, hra, hqa, _, hfu, hiu, _, hg, hok, heq⟩ := hG
  refine ⟨H, HA, HU, σ, hg, hok, fun e he => ?_⟩
  have h1 := heq (rufAusL H) (orakelAus O HA) (umweltAus S sp HU) (rufAusL_passt hf)
    (orakelAus_passt O hfa) (umweltAus_passt S sp hfu) (gleichRS_orakelAus O HA)
  rw [he] at h1
  exact (hK F.f).2 (orakelAus O HA) (orakelAus_rahmen hO hra) (regLokal_orakelAus hRL HA)
    (orakelAus_vertrag hQ hqa) (umweltAus S sp HU) (umweltAus_ok hS hsp hiu) (rufAusL H)
    (rufAusL_rahmen hv) (rufAusL_ohneLogik hv.1) F.s0 F.rho hreq e
    (zErg_gleich_logik (ZErg.folgt_logik h1))

/-- The same, for a residue named by its shape. -/
theorem kopfS_keineLogik' (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f) {F : RufRahmenG D} {W : World D}
    (hG : KopfS P O passes Q S lok F W) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D F.f) l Γ Λ} (hr : F.rest = ⟨l, Γ, Λ, ρ, r⟩) :
    ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (HU : List (UEintrag D)) (σ : World D),
      GleichAuf (stabilS P S lok F.f Λ) σ W ∧ r.okS P (fussOrteG P F.f) (sicher P lok F.f) ∧
      ∀ e : Logik D, semH S (orakelAus O HA) (umweltAus S sp HU) passes (rufAusL H) r σ ρ ≠
        .logik e := by
  obtain ⟨H, HA, HU, σ, hg, hok, hno⟩ := kopfS_keineLogik hO hRL hQ hS hsp hK hG
  rw [hr] at hok hno hg
  exact ⟨H, HA, HU, σ, hg, hok, hno⟩

/-- **At a release the invariant holds in the machine.** A head at the
    release marker `frei L` (after the body) or at a `leave`/`next` that
    leaves the body: the release check passes at the sequential world (else
    the head would predict `logik schleife`), and the protected carriers of
    `L` are stable (the frame holds `L`), so the check passes at the machine
    memory. -/
theorem kopfS_frei_inv (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f) {F : RufRahmenG D} {W : World D}
    (hG : KopfS P O passes Q S lok F W) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    (L : D.Lock) (hL : Res.held L ∈ Λ) {r : GRest D (vertragVon D F.f) l Γ Λ}
    (hr : F.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (hlog : ∀ (O' : Orakel D) (U : Umwelt D) R (σ : World D), S.inv L σ.speicher = false →
      semH S O' U passes R r σ ρ = .logik .schleife) :
    S.inv L W.speicher = true := by
  obtain ⟨H, HA, HU, σ, hg, _, hno⟩ := kopfS_keineLogik' hO hRL hQ hS hsp hK hG hr
  have hi : S.inv L σ.speicher = true := by
    cases h : S.inv L σ.speicher with
    | true => rfl
    | false => exact absurd (hlog _ _ _ σ h) (hno .schleife)
  rw [← hi]
  refine hS.2 L _ _ fun c hc => ?_
  have hcs : c ∈ stabilS P S lok F.f Λ := stabilS_mem.mpr (Or.inr ⟨L, hL, hc⟩)
  cases c with
  | inl t => exact (hg.1 t hcs).symm
  | inr g => exact (hg.2 g hcs).symm

/-- The invariant of a held lock is the same at two worlds agreeing on the
    stable carriers. -/
theorem inv_gleich (hS : SperrInvOk S) {f : D.Fn} {Λ : List (Res D)} {L : D.Lock}
    (hL : Res.held L ∈ Λ) {σ W : World D} (hg : GleichAuf (stabilS P S lok f Λ) σ W) :
    S.inv L σ.speicher = S.inv L W.speicher := by
  refine hS.2 L _ _ fun c hc => ?_
  have hcs : c ∈ stabilS P S lok f Λ := stabilS_mem.mpr (Or.inr ⟨L, hL, hc⟩)
  cases c with
  | inl t => exact hg.1 t hcs
  | inr g => exact hg.2 g hcs

/-- Agreement read at a released world with the machine memory. -/
theorem gleichAuf_frei {f : D.Fn} {Λ : List (Res D)} {L : D.Lock} {σ W : World D}
    (hg : GleichAuf (stabilS P S lok f (Res.held L :: Λ)) σ W) (spur' : List (Ereignis D)) :
    GleichAuf (stabilS P S lok f Λ) (σ.gibt L) (W.speicher.welt spur') :=
  GleichAuf.mono (fun _ h => stabilS_mono (fun _ h' => List.mem_cons_of_mem _ h') h)
    ⟨fun t ht => hg.1 t ht, fun g hg' => hg.2 g hg'⟩

/-- **The release after the body keeps the replay** (`freiGib`). -/
theorem fadenS_frei (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f) {z : RufFadenG D} {W : World D}
    (hF : FadenS P O passes Q S lok z W) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (L : D.Lock)
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hr : z.kopf.rest = ⟨l, Γ, Res.held L :: Λ, ρ, .frei L k⟩) (spur' : List (Ereignis D)) :
    FadenS P O passes Q S lok
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, Λ, ρ, k⟩⟩, spur', z.log⟩
      (W.speicher.welt spur') := by
  have hW := kopfS_frei_inv hO hRL hQ hS hsp hK hF.1 L List.mem_cons_self hr
    (fun O' U R σ h => semH_frei_falsch S O' U passes R L k σ ρ h)
  refine fadenS_lokal hF hr ρ k spur' (fun σ hg hok => ?_)
  have hiσ : S.inv L σ.speicher = true := (inv_gleich hS List.mem_cons_self hg).trans hW
  exact ⟨σ.gibt L, Nat.le_succ _, gleichAuf_frei hg spur', hok,
    fun R O' U => ZErg.folgt_of_eq (semH_frei S O' U passes R L k σ ρ hiσ)⟩

/-- **A `leave`/`next` out of a `locks` body keeps the replay**
    (`peelFreiLeave`, `peelFreiNext`). -/
theorem fadenS_peelFrei (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f) {z : RufFadenG D} {W : World D}
    (hF : FadenS P O passes Q S lok z W) {Γ : Ctx} {Λ Λ1 : List (Res D)} (L : D.Lock)
    (rest : Block D (vertragVon D z.kopf.f) true Γ Λ (Res.held L :: Λ1))
    (k : GRest D (vertragVon D z.kopf.f) true Γ Λ1) (ρ : Env D Γ) (h : true = true) (x : Bool)
    (hr : z.kopf.rest =
      ⟨true, Γ, Λ, ρ, .dann (.cons (if x then .leave h else .next h) rest) (.frei L k)⟩)
    (spur' : List (Ereignis D)) :
    FadenS P O passes Q S lok
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
        ⟨true, Γ, Λ1, ρ, .dann (.cons (if x then .leave h else .next h) .nil) k⟩⟩, spur', z.log⟩
      (W.speicher.welt spur') := by
  have hLΛ : Res.held L ∈ Λ := (Block.held_iff rest L).mp List.mem_cons_self
  have hΛ1 : ∀ M, Res.held M ∈ Λ1 → Res.held M ∈ Λ :=
    fun M hM => (Block.held_iff rest M).mp (List.mem_cons_of_mem _ hM)
  have hW := kopfS_frei_inv hO hRL hQ hS hsp hK hF.1 L hLΛ hr
    (fun O' U R σ hi => semH_peelFrei_falsch S O' U passes R L rest k σ ρ h x hi)
  refine fadenS_lokal hF hr ρ _ spur' (fun σ hg hok => ?_)
  have hiσ : S.inv L σ.speicher = true := (inv_gleich hS hLΛ hg).trans hW
  obtain ⟨_, _, hk⟩ := hok
  refine ⟨σ.gibt L, Nat.le_succ _,
    GleichAuf.mono (fun _ hc => stabilS_mono hΛ1 hc) ⟨fun t ht => hg.1 t ht, fun g hg' => hg.2 g hg'⟩,
    ⟨by cases x <;> rfl, fun _ hc => by cases x <;> simp [blockOrteP, stmtOrteP] at hc, hk⟩,
    fun R O' U => ZErg.folgt_of_eq (semH_peelFrei S O' U passes R L rest k σ ρ h x hiσ)⟩

end Frei

end Gabbro.Grammatik
