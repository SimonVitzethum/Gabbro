/-
  File:      Grammatik/Zielsatz/RuheNutzer.lean
  Subject:   THE USER'S LOGIC AND THE HARDWARE ASSUMPTIONS TRANSFER TO
             P.mitRuhe (the runtime's idle root, MitRuhe.lean).

  * `logikPflicht_mitRuhe`: `LogikPflicht P S Q` (the body half of `NutzerPflicht`) gives
    `LogikPflicht P.mitRuhe S.mitRuhe (axEnsRuhe Q)`. At `some f` the
    obligation of `D.mitRuhe` quantifies over oracles, moves and handlers of
    `D.mitRuhe`; each is answered by one of `D` (`Orakel.zurueck`,
    `umweltZ`, `rufZuD`) in the same class, and the translated body runs as
    the body (`rumpfH_mitRuhe`, MitRuheSperre.lean). At the root `none`
    (body `return`, `ensures true`, no reason, writes nothing) the
    obligation holds outright.
  * `hardware_mitRuhe`: `HardwareAnnahmen O Q` gives
    `HardwareAnnahmen O.mitRuhe (axEnsRuhe Q)`.

  `axEnsRuhe Q` -- the declared axiom ensures of `D.mitRuhe`: `Q` on the
  translated-back answer world and result. It is not in `Spec.lean`: the
  statement names `Q` only on `P`; the flagships on `P.mitRuhe` are
  instantiated with this family.
-/
import Grammatik.Zielsatz.Spec
import Grammatik.MitRuheSperre

namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration}

/-- **The declared axiom ensures of `D.mitRuhe`.** -/
def axEnsRuhe (Q : AxEns D) : AxEns D.mitRuhe := fun a σ v => Q a (worldZ σ) (ergZ (D.aerg a) v)

/-! ## 1. Frames, agreement, the classes of oracles, moves and handlers -/

theorem rahmen_worldZ {W : D.Tab → Bool} {G : D.Glob → Bool} {σ : World D} {x : World D.mitRuhe}
    (h : Rahmen (D := D.mitRuhe) W G (worldR σ) x) : Rahmen W G σ (worldZ x) :=
  ⟨fun t ht k f => by
    show valZ _ (x.slots t k f) = _
    rw [h.1 t ht k f]
    exact valZ_valR _ _,
   fun g hg => by
    show valZ _ (x.globs g) = _
    rw [h.2 g hg]
    exact valZ_valR _ _⟩

theorem rahmen_worldR {W : D.Tab → Bool} {G : D.Glob → Bool} {σ : World D.mitRuhe} {x : World D}
    (h : Rahmen W G (worldZ σ) x) : Rahmen (D := D.mitRuhe) W G σ (worldR x) :=
  ⟨fun t ht k f => by
    show valR _ (x.slots t k f) = _
    rw [h.1 t ht k f]
    exact valR_valZ _ _,
   fun g hg => by
    show valR _ (x.globs g) = _
    rw [h.2 g hg]
    exact valR_valZ _ _⟩

theorem gleichAuf_worldR {l : List (D.Tab ⊕ D.Glob)} {σ σ' : World D} (h : GleichAuf l σ σ') :
    GleichAuf (D := D.mitRuhe) l (worldR σ) (worldR σ') :=
  ⟨fun t ht => by
    show (fun k f => valR _ (σ.slots t k f)) = fun k f => valR _ (σ'.slots t k f)
    rw [h.1 t ht],
   fun g hg => by
    show valR _ (σ.globs g) = valR _ (σ'.globs g)
    rw [h.2 g hg]⟩

theorem gleichAuf_worldZ {l : List (D.Tab ⊕ D.Glob)} {σ σ' : World D.mitRuhe}
    (h : GleichAuf (D := D.mitRuhe) l σ σ') : GleichAuf l (worldZ σ) (worldZ σ') :=
  ⟨fun t ht => by
    show (fun k f => valZ _ (σ.slots t k f)) = fun k f => valZ _ (σ'.slots t k f)
    rw [show σ.slots t = σ'.slots t from h.1 t ht],
   fun g hg => by
    show valZ _ (σ.globs g) = valZ _ (σ'.globs g)
    rw [show σ.globs g = σ'.globs g from h.2 g hg]⟩

theorem rahmenO_zurueck {O' : Orakel D.mitRuhe} (h : RahmenO O') : RahmenO (Orakel.zurueck O') :=
  fun a σ ρ => rahmen_worldZ (h a (worldR σ) (envR ρ))

theorem regLokal_zurueck {O' : Orakel D.mitRuhe} (h : RegLokal O') :
    RegLokal (Orakel.zurueck O') :=
  ⟨fun r _ _ hg => h.1 r _ _ (gleichAuf_worldR hg), fun g _ _ hg => h.2 g _ _ (gleichAuf_worldR hg)⟩

theorem axVertrag_zurueck {Q : AxEns D} {O' : Orakel D.mitRuhe} (h : AxVertragO (axEnsRuhe Q) O') :
    AxVertragO Q (Orakel.zurueck O') := by
  intro a σ ρ v hv
  change einpassenErg (Orakel.zurueck O').zeiger (D.aerg a) (O'.wirkt a (worldR σ) (envR ρ)).2 =
    some v at hv
  have e : einpassenErg (D := D.mitRuhe) O'.zeiger ((D.aerg a).map tyR)
      (O'.wirkt a (worldR σ) (envR ρ)).2 = some (ergR (D.aerg a) v) := by
    rw [einpassenErg_ru (Orakel.zurueck O').zeiger O'.zeiger (fun _ => rfl), hv]
    rfl
  have hq := h a (worldR σ) (envR ρ) (ergR (D.aerg a) v) e
  change Q a (worldZ (O'.wirkt a (worldR σ) (envR ρ)).1) (ergZ (D.aerg a) (ergR (D.aerg a) v)) = true
    at hq
  rw [ergZ_ergR] at hq
  exact hq

theorem havocOk_umweltZ {S : SperrInv D} {U' : Umwelt D.mitRuhe} (h : HavocOk S.mitRuhe U') :
    HavocOk S (umweltZ U') := by
  intro L σ
  obtain ⟨h1, h2, h3⟩ := h L (worldR σ)
  refine ⟨?_, fun c hc => ?_, h3⟩
  · show (U' L (worldR σ)).spur.map evZ = σ.spur
    rw [h1]
    show (σ.spur.map evR).map evZ = σ.spur
    rw [List.map_map]
    conv => rhs; rw [← List.map_id σ.spur]
    exact List.map_congr_left fun e _ => evZ_evR e
  · have h4 := h2 c hc
    cases c with
    | inl t =>
        funext k f
        have e := congrFun (congrFun h4 k) f
        exact (congrArg (valZ _) e).trans (valZ_valR _ _)
    | inr g =>
        exact (congrArg (valZ _) h4).trans (valZ_valR _ _)

theorem ens_mitRuhe_iff (P : Programm D) (g : D.Fn) (s0 σ : World D) (ρ : Env D (D.params g))
    (v : ErgVal D (D.erg g)) :
    EnsAmRueck P.mitRuhe (some g) (worldR s0) (worldR σ) (envR ρ) (ergR (D.erg g) v) ↔
      EnsAmRueck P g s0 σ ρ v := by
  unfold EnsAmRueck
  show wahr? (eval (worldR s0) (P.mitRuhe.ensures (some g)) (worldR σ)
    (ergEnv ((D.erg g).map tyR) (ergR (D.erg g) v) (envR ρ))) = true ↔ _
  rw [ens_mitRuhe_eval]
  exact Iff.rfl

theorem respektiert_rufZuD {P : Programm D}
    {R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) → RufAusgang f}
    (h : RespektiertRahmen P.mitRuhe R') : RespektiertRahmen P (rufZuD R') := by
  refine ⟨fun g σ ρ hreq σ' v hx => ?_, fun g σ ρ σ' v hx => ?_⟩
  · unfold rufZuD at hx
    cases hy : R' (some g) (worldR σ) (envR ρ) with
    | ok σ1 v1 =>
        rw [hy] at hx
        cases hx
        have he := h.1 (some g) (worldR σ) (envR ρ) ((req_mitRuhe_iff P g σ ρ).mpr hreq) σ1 v1 hy
        rw [← worldR_worldZ σ1, ← ergR_ergZ (D.erg g) v1] at he
        exact (ens_mitRuhe_iff P g σ (worldZ σ1) ρ (ergZ (D.erg g) v1)).mp he
    | grund => rw [hy] at hx; cases hx
    | logik => rw [hy] at hx; cases hx
    | hardware => rw [hy] at hx; cases hx
  · unfold rufZuD at hx
    cases hy : R' (some g) (worldR σ) (envR ρ) with
    | ok σ1 v1 =>
        rw [hy] at hx
        cases hx
        obtain ⟨h1, h2⟩ := h.2 (some g) (worldR σ) (envR ρ) σ1 v1 hy
        refine ⟨rahmen_worldZ h1, ?_⟩
        show (worldZ σ1).haelt = σ.haelt
        rw [haelt_worldZ, ← haelt_worldR σ]
        exact h2
    | grund => rw [hy] at hx; cases hx
    | logik => rw [hy] at hx; cases hx
    | hardware => rw [hy] at hx; cases hx

theorem ohneVorbedingung_rufZuD
    (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) → RufAusgang f) :
    OhneVorbedingung (rufZuD R') := by
  intro g σ ρ e hx g' he
  subst he
  unfold rufZuD at hx
  cases hy : R' (some g) (worldR σ) (envR ρ) with
  | ok => rw [hy] at hx; cases hx
  | grund => rw [hy] at hx; cases hx
  | logik => rw [hy] at hx; cases hx
  | hardware => rw [hy] at hx; cases hx

theorem ohneLogik_rufZuD
    {R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) → RufAusgang f}
    (h : OhneLogik R') : OhneLogik (rufZuD R') := by
  intro g σ ρ e hx
  unfold rufZuD at hx
  cases hy : R' (some g) (worldR σ) (envR ρ) with
  | ok => rw [hy] at hx; cases hx
  | grund => rw [hy] at hx; cases hx
  | logik e' => exact h (some g) _ _ e' hy
  | hardware => rw [hy] at hx; cases hx

theorem rufRel_rufZuD
    {R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) → RufAusgang f}
    (h : OhneVorbedingung R') : RufRel (rufZuD R') R' := by
  intro g σ ρ
  unfold rufZuD
  cases hy : R' (some g) (worldR σ) (envR ρ) with
  | ok σ1 v1 =>
      left
      simp only [rufZ, rufR, worldR_worldZ]
      exact congrArg _ (ergR_ergZ (D.erg g) v1).symm
  | grund σ1 r =>
      left
      simp only [rufZ, rufR, worldR_worldZ]
  | logik e' =>
      right
      exact ⟨e', .schleife, rfl, rfl, fun g' he => absurd he (h (some g) _ _ e' hy g')⟩
  | hardware e =>
      left
      simp only [rufZ, rufR, hwR_hwZ]

theorem rufRel_torRuf (P : Programm D)
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    {R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) → RufAusgang f}
    (h : RufRel R R') : RufRel (torRuf P R) (torRuf P.mitRuhe R') := by
  intro g σ ρ
  have hq := req_mitRuhe_iff P g σ ρ
  unfold ReqAmEintritt at hq
  unfold torRuf
  by_cases hr : wahr? (eval σ (P.requires g) σ ρ) = true
  · rw [if_pos hr, if_pos (hq.mpr hr)]
    exact h g σ ρ
  · rw [if_neg hr, if_neg (fun x => hr (hq.mp x))]
    exact Or.inr ⟨_, _, rfl, rfl, fun _ _ => ⟨g, rfl⟩⟩

/-- The body of `some f`, related to the body of `f` under the answering
    oracle, move and handler of `D`. -/
theorem rumpf_rel (P : Programm D) (S : SperrInv D) (passes : Nat) (O' : Orakel D.mitRuhe)
    (U' : Umwelt D.mitRuhe) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) → RufAusgang f)
    (hR : RufRel R R') (f : D.Fn) (σ0 : World D) (ρ0 : Env D (D.params f)) :
    @EndRel D (vertragVon D f) false (D.params f)
      (execEndH S.mitRuhe O' U' passes R' (P.mitRuhe.rumpf (some f)) (worldR σ0) (envR ρ0))
      (execEndH S (Orakel.zurueck O') (umweltZ U') passes R (P.rumpf f) σ0 ρ0) := by
  exact rumpfH_mitRuhe P S (Orakel.zurueck O') O' (orakelRu_zurueck O') (umweltZ U') U' passes R R'
    (umweltZ_ru U') hR f σ0 ρ0

theorem invAmRueck_mitRuhe (P : Programm D) (f : D.Fn) (σ : World D) :
    InvAmRueck P.mitRuhe (some f) (worldR σ) ↔ InvAmRueck P f σ := by
  unfold InvAmRueck InvHaelt
  show (∀ i ∈ D.invs, schuldet f i = true →
    wahr? (eval (worldR σ) (P.mitRuhe.invariante i) (worldR σ) Env.nil) = true) ↔ _
  simp only [inv_mitRuhe_eval]
  rfl

/-! ## 2. The user obligation at `some f` -/

section Transfer

variable {P : Programm D} {passes : Nat} {Q : AxEns D} {S : SperrInv D} {f : D.Fn}

theorem koerperGutS_mitRuhe (h : KoerperGutS P passes Q S f) :
    KoerperGutS P.mitRuhe passes (axEnsRuhe Q) S.mitRuhe (some f) := by
  unfold KoerperGutS at h ⊢
  refine ⟨fun O' hr hl hq U' hU' R' hR hOV σ ρ hreq => ?_,
    fun O' hr hl hq U' hU' R' hR hOL σ ρ hreq => ?_⟩
  · obtain ⟨σ0, rfl⟩ : ∃ σ0, σ = worldR σ0 := ⟨worldZ σ, (worldR_worldZ σ).symm⟩
    obtain ⟨ρ0, rfl⟩ : ∃ ρ0 : Env D (D.params f), ρ = envR ρ0 :=
      ⟨envZ ρ, (envR_envZ (Γ := D.params f) ρ).symm⟩
    have hreq0 : ReqAmEintritt P f σ0 ρ0 := (req_mitRuhe_iff P f σ0 ρ0).mp hreq
    have hk := h.1 (Orakel.zurueck O') (rahmenO_zurueck hr) (regLokal_zurueck hl)
      (axVertrag_zurueck hq) (umweltZ U') (havocOk_umweltZ hU') (rufZuD R') (respektiert_rufZuD hR)
      (ohneVorbedingung_rufZuD R') σ0 ρ0 hreq0
    have hrel := rumpf_rel P S passes O' U' (rufZuD R') R' (rufRel_rufZuD hOV) f σ0 ρ0
    have hrel2 := rumpf_rel P S passes O' U' (torRuf P (rufZuD R')) (torRuf P.mitRuhe R')
      (rufRel_torRuf P (rufRel_rufZuD hOV)) f σ0 ρ0
    refine ⟨fun σ' v hx => ?_, fun g hx => ?_⟩
    · rcases hrel with e | ⟨e', e, h1, h2, ht⟩
      · have e := hx.symm.trans e
        cases hy : execEndH (V := vertragVon D f) S (Orakel.zurueck O') (umweltZ U') passes
            (rufZuD R') (P.rumpf f) σ0 ρ0 with
        | zurueck σa va =>
            rw [hy] at e
            simp only [endR] at e
            cases e
            exact (ens_mitRuhe_iff P f σ0 σa ρ0 va).mpr (hk.1 σa va hy)
        | grund => rw [hy] at e; cases e
        | leave => rw [hy] at e; cases e
        | next => rw [hy] at e; cases e
        | logik => rw [hy] at e; cases e
        | hardware => rw [hy] at e; cases e
      · have h1 := hx.symm.trans h1; cases h1
    · rcases hrel2 with e | ⟨e', e, h1, h2, ht⟩
      · have e := hx.symm.trans e
        cases hy : execEndH (V := vertragVon D f) S (Orakel.zurueck O') (umweltZ U') passes
            (torRuf P (rufZuD R')) (P.rumpf f) σ0 ρ0 with
        | logik e0 =>
            rw [hy] at e
            simp only [endR] at e
            cases e0 with
            | vorbedingung g0 => exact hk.2 g0 hy
            | _ => simp only [logikR] at e; cases e
        | zurueck => rw [hy] at e; cases e
        | grund => rw [hy] at e; cases e
        | leave => rw [hy] at e; cases e
        | next => rw [hy] at e; cases e
        | hardware => rw [hy] at e; cases e
      · have h1 := hx.symm.trans h1
        cases h1
        obtain ⟨g0, hg0⟩ := ht g rfl
        rw [hg0] at h2
        exact hk.2 g0 h2
  · obtain ⟨σ0, rfl⟩ : ∃ σ0, σ = worldR σ0 := ⟨worldZ σ, (worldR_worldZ σ).symm⟩
    obtain ⟨ρ0, rfl⟩ : ∃ ρ0 : Env D (D.params f), ρ = envR ρ0 :=
      ⟨envZ ρ, (envR_envZ (Γ := D.params f) ρ).symm⟩
    have hreq0 : ReqAmEintritt P f σ0 ρ0 := (req_mitRuhe_iff P f σ0 ρ0).mp hreq
    have hOV : OhneVorbedingung R' := fun g σ ρ e hx => absurd hx (hOL g σ ρ e)
    have hk := h.2 (Orakel.zurueck O') (rahmenO_zurueck hr) (regLokal_zurueck hl)
      (axVertrag_zurueck hq) (umweltZ U') (havocOk_umweltZ hU') (rufZuD R') (respektiert_rufZuD hR)
      (ohneLogik_rufZuD hOL) σ0 ρ0 hreq0
    have hrel := rumpf_rel P S passes O' U' (rufZuD R') R' (rufRel_rufZuD hOV) f σ0 ρ0
    intro e' hx
    rcases hrel with e | ⟨e1, e2, h1, h2, _⟩
    · have e := hx.symm.trans e
      cases hy : execEndH (V := vertragVon D f) S (Orakel.zurueck O') (umweltZ U') passes
          (rufZuD R') (P.rumpf f) σ0 ρ0 with
      | logik e0 => exact hk e0 hy
      | zurueck => rw [hy] at e; cases e
      | grund => rw [hy] at e; cases e
      | leave => rw [hy] at e; cases e
      | next => rw [hy] at e; cases e
      | hardware => rw [hy] at e; cases e
    · exact hk e2 h2

theorem invGutS_mitRuhe (h : InvGutS P passes Q S f) :
    InvGutS P.mitRuhe passes (axEnsRuhe Q) S.mitRuhe (some f) := by
  intro O' hr hl hq U' hU' R' hR hOV σ ρ hreq σ' v hx
  obtain ⟨σ0, rfl⟩ : ∃ σ0, σ = worldR σ0 := ⟨worldZ σ, (worldR_worldZ σ).symm⟩
  obtain ⟨ρ0, rfl⟩ : ∃ ρ0 : Env D (D.params f), ρ = envR ρ0 :=
    ⟨envZ ρ, (envR_envZ (Γ := D.params f) ρ).symm⟩
  have hreq0 : ReqAmEintritt P f σ0 ρ0 := (req_mitRuhe_iff P f σ0 ρ0).mp hreq
  have hk := h (Orakel.zurueck O') (rahmenO_zurueck hr) (regLokal_zurueck hl)
    (axVertrag_zurueck hq) (umweltZ U') (havocOk_umweltZ hU') (rufZuD R') (respektiert_rufZuD hR)
    (ohneVorbedingung_rufZuD R') σ0 ρ0 hreq0
  have hrel := rumpf_rel P S passes O' U' (rufZuD R') R' (rufRel_rufZuD hOV) f σ0 ρ0
  rcases hrel with e | ⟨e', e, h1, h2, ht⟩
  · have e := hx.symm.trans e
    cases hy : execEndH (V := vertragVon D f) S (Orakel.zurueck O') (umweltZ U') passes
        (rufZuD R') (P.rumpf f) σ0 ρ0 with
    | zurueck σa va =>
        rw [hy] at e
        simp only [endR] at e
        cases e
        exact (invAmRueck_mitRuhe P f σa).mpr (hk σa va hy)
    | grund => rw [hy] at e; cases e
    | leave => rw [hy] at e; cases e
    | next => rw [hy] at e; cases e
    | logik => rw [hy] at e; cases e
    | hardware => rw [hy] at e; cases e
  · have h1 := hx.symm.trans h1; cases h1

theorem invGutGrund_mitRuhe (h : InvGutGrund P passes Q S f) :
    InvGutGrund P.mitRuhe passes (axEnsRuhe Q) S.mitRuhe (some f) := by
  intro O' hr hl hq U' hU' R' hR hOV σ ρ hreq σ' r hx
  obtain ⟨σ0, rfl⟩ : ∃ σ0, σ = worldR σ0 := ⟨worldZ σ, (worldR_worldZ σ).symm⟩
  obtain ⟨ρ0, rfl⟩ : ∃ ρ0 : Env D (D.params f), ρ = envR ρ0 :=
    ⟨envZ ρ, (envR_envZ (Γ := D.params f) ρ).symm⟩
  have hreq0 : ReqAmEintritt P f σ0 ρ0 := (req_mitRuhe_iff P f σ0 ρ0).mp hreq
  have hk := h (Orakel.zurueck O') (rahmenO_zurueck hr) (regLokal_zurueck hl)
    (axVertrag_zurueck hq) (umweltZ U') (havocOk_umweltZ hU') (rufZuD R') (respektiert_rufZuD hR)
    (ohneVorbedingung_rufZuD R') σ0 ρ0 hreq0
  have hrel := rumpf_rel P S passes O' U' (rufZuD R') R' (rufRel_rufZuD hOV) f σ0 ρ0
  rcases hrel with e | ⟨e', e, h1, h2, ht⟩
  · have e := hx.symm.trans e
    cases hy : execEndH (V := vertragVon D f) S (Orakel.zurueck O') (umweltZ U') passes
        (rufZuD R') (P.rumpf f) σ0 ρ0 with
    | grund σa ra =>
        rw [hy] at e
        simp only [endR] at e
        cases e
        exact (invAmRueck_mitRuhe P f σa).mpr (hk σa _ hy)
    | zurueck => rw [hy] at e; cases e
    | leave => rw [hy] at e; cases e
    | next => rw [hy] at e; cases e
    | logik => rw [hy] at e; cases e
    | hardware => rw [hy] at e; cases e
  · have h1 := hx.symm.trans h1; cases h1

end Transfer

/-! ## 3. The user obligation at the root -/

section Ruhe

variable (P : Programm D) (passes : Nat) (Q : AxEns D.mitRuhe) (S : SperrInv D.mitRuhe)

theorem schuldet_ruhe (i : D.Inv) : schuldet (D := D.mitRuhe) none i = false := by
  unfold schuldet
  rw [List.any_eq_false]
  intro t _ ht
  exact Bool.noConfusion ((show (D.mitRuhe).schreibt none t = false from rfl).symm.trans ht)

theorem koerperGutS_ruhe : KoerperGutS P.mitRuhe passes Q S none := by
  unfold KoerperGutS
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v hx => ?_, fun g hx => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hx => ?_⟩
  · rfl
  · cases hx
  · cases hx

theorem invGutS_ruhe : InvGutS P.mitRuhe passes Q S none :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i _ hs => absurd hs (by rw [schuldet_ruhe]; decide)

theorem invGutGrund_ruhe : InvGutGrund P.mitRuhe passes Q S none :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ r _ => r.elim0

end Ruhe

/-! ## 4. The lock invariants, the axiom ensures, the hardware -/

theorem sperrInvLokal_mitRuhe {S : SperrInv D} (h : SperrInvLokal S) : SperrInvLokal S.mitRuhe := by
  intro L s s' hc
  show S.inv L (speicherZ s) = S.inv L (speicherZ s')
  refine h L _ _ fun c hcL => ?_
  have h4 := hc c hcL
  cases c with
  | inl t =>
      show (fun k f => valZ _ (s.slots t k f)) = fun k f => valZ _ (s'.slots t k f)
      rw [show s.slots t = s'.slots t from h4]
  | inr g =>
      show valZ _ (s.globs g) = valZ _ (s'.globs g)
      rw [show s.globs g = s'.globs g from h4]

theorem axEnsLokal_mitRuhe {Q : AxEns D} (h : AxEnsLokal Q) : AxEnsLokal (axEnsRuhe Q) := by
  intro a σ σ' v ht hg
  show Q a (worldZ σ) (ergZ _ v) = Q a (worldZ σ') (ergZ _ v)
  refine h a _ _ _ (fun t hta => ?_) (fun g hga => ?_)
  · show (fun k f => valZ _ (σ.slots t k f)) = fun k f => valZ _ (σ'.slots t k f)
    rw [ht t hta]
  · show valZ _ (σ.globs g) = valZ _ (σ'.globs g)
    rw [hg g hga]

/-- **The user's logic on `P` is the user's logic on `P.mitRuhe`.** -/
theorem logikPflicht_mitRuhe {P : Programm D} {S : SperrInv D} {Q : AxEns D}
    (h : LogikPflicht P S Q) : LogikPflicht P.mitRuhe S.mitRuhe (axEnsRuhe Q) :=
  ⟨fun passes f => match f with
    | none => ⟨koerperGutS_ruhe P passes _ _, invGutS_ruhe P passes _ _, invGutGrund_ruhe P passes _ _⟩
    | some f => ⟨koerperGutS_mitRuhe (h.1 passes f).1, invGutS_mitRuhe (h.1 passes f).2.1,
        invGutGrund_mitRuhe (h.1 passes f).2.2⟩,
   sperrInvLokal_mitRuhe h.2.1, axEnsLokal_mitRuhe h.2.2⟩

theorem axiomSpur_map (tabs : List D.Tab) (globs : List D.Glob) (a : D.Ax) (Λ : List (Res D))
    (h : List D.Lock) :
    (axiomSpur tabs globs a Λ h).map evR = axiomSpur (D := D.mitRuhe) tabs globs a (Λ.map resR) h := by
  unfold axiomSpur
  simp only [List.map_append, List.map_map]
  rfl

theorem gutO_mitRuhe {O : Orakel D} (h : GutO O) : GutO O.mitRuhe := by
  intro a σ ρ
  obtain ⟨h1, h2, h3⟩ := h a (worldZ σ) (envZ ρ)
  have hh : (worldZ σ).haelt = σ.haelt := haelt_worldZ σ
  refine ⟨rahmen_worldR h1, ?_, fun ht hg => ?_⟩
  · show (worldR (O.wirkt a (worldZ σ) (envZ ρ)).1).haelt = σ.haelt
    rw [haelt_worldR, h2, hh]
  · obtain ⟨tabs, globs, Λe, e1, e2, e3, e4, e5, e6, e7⟩ :=
      h3 (fun t hta L hL => hh ▸ ht t hta L hL) (fun g hga L hL => hh ▸ hg g hga L hL)
    refine ⟨tabs, globs, Λe.map resR, e1, e2, fun t hta => darfR (e3 t hta),
      fun g hga => gdarfR (e4 g hga), fun m st hm => ?_, fun L hL => ?_, ?_⟩
    · obtain ⟨r, hr, he⟩ := List.mem_map.mp hm
      cases r with
      | held L => cases he
      | marke m' s' =>
          cases he
          exact e5 _ _ hr
    · rw [← hh]
      exact e6 L (held_mem_map.mp hL)
    · show (O.wirkt a (worldZ σ) (envZ ρ)).1.spur.map evR =
        axiomSpur (D := D.mitRuhe) tabs globs a (Λe.map resR) σ.haelt ++ σ.spur
      rw [e7, List.map_append, hh, axiomSpur_map]
      congr 1
      show (σ.spur.map evZ).map evR = σ.spur
      rw [List.map_map]
      conv => rhs; rw [← List.map_id σ.spur]
      exact List.map_congr_left fun e _ => evR_evZ e

theorem regLokal_mitRuhe {O : Orakel D} (h : RegLokal O) : RegLokal O.mitRuhe :=
  ⟨fun r _ _ hg => h.1 r _ _ (gleichAuf_worldZ hg), fun g _ _ hg => h.2 g _ _ (gleichAuf_worldZ hg)⟩

theorem axVertrag_mitRuhe {Q : AxEns D} {O : Orakel D} (h : AxVertragO Q O) :
    AxVertragO (axEnsRuhe Q) O.mitRuhe := by
  intro a σ ρ v hv
  change einpassenErg (D := D.mitRuhe) O.mitRuhe.zeiger ((D.aerg a).map tyR)
    (O.wirkt a (worldZ σ) (envZ ρ)).2 = some v at hv
  rw [einpassenErg_ru O.zeiger O.mitRuhe.zeiger (zeiger_mitRuhe O)] at hv
  cases hx : einpassenErg O.zeiger (D.aerg a) (O.wirkt a (worldZ σ) (envZ ρ)).2 with
  | none => rw [hx] at hv; cases hv
  | some v0 =>
      rw [hx] at hv
      cases hv
      show Q a (worldZ (worldR (O.wirkt a (worldZ σ) (envZ ρ)).1)) (ergZ _ (ergR _ v0)) = true
      rw [worldZ_worldR, ergZ_ergR]
      exact h a _ _ v0 hx

/-- **The hardware assumptions on `O` are the ones on `O.mitRuhe`.** -/
theorem hardware_mitRuhe {O : Orakel D} {Q : AxEns D} (h : HardwareAnnahmen O Q) :
    HardwareAnnahmen O.mitRuhe (axEnsRuhe Q) :=
  ⟨gutO_mitRuhe h.1, regLokal_mitRuhe h.2.1, axVertrag_mitRuhe h.2.2⟩

#print axioms Gabbro.Grammatik.koerperGutS_mitRuhe
#print axioms Gabbro.Grammatik.invGutS_mitRuhe
#print axioms Gabbro.Grammatik.invGutGrund_mitRuhe
#print axioms Gabbro.Grammatik.logikPflicht_mitRuhe
#print axioms Gabbro.Grammatik.hardware_mitRuhe

end Gabbro.Grammatik
