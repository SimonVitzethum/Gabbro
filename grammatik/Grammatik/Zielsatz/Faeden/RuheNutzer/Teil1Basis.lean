module

public import Grammatik.Zielsatz.Kern.Spec
public import Grammatik.Zielsatz.Faeden.RuheNutzer.Ptr
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSperre

@[expose] public section



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
    | why => rw [hy] at hx; cases hx
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
    | why => rw [hy] at hx; cases hx
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
  | why => rw [hy] at hx; cases hx
  | logik e' =>
      rw [hy] at hx
      simp only [rufZ, RufAusgang.logik.injEq] at hx
      unfold logikZ at hx
      split at hx <;> cases hx
  | hardware => rw [hy] at hx; cases hx

theorem ohneLogik_rufZuD
    {R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) → RufAusgang f}
    (h : OhneLogik R') : OhneLogik (rufZuD R') := by
  intro g σ ρ e hx
  unfold rufZuD at hx
  cases hy : R' (some g) (worldR σ) (envR ρ) with
  | ok => rw [hy] at hx; cases hx
  | why => rw [hy] at hx; cases hx
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
  | why σ1 r =>
      left
      simp only [rufZ, rufR, worldR_worldZ]
  | logik e' =>
      cases e' with
      | abstieg h' =>
          cases h' with
          | some h0 => exact Or.inl rfl
          | none =>
              right
              exact ⟨_, .schleife, rfl, rfl, logikTreu_schleife (by intro g' he; cases he) (by intro h0 he; cases he)⟩
      | vorbedingung g' => exact absurd rfl (h (some g) _ _ _ hy g')
      | _ =>
          right
          exact ⟨_, .schleife, rfl, rfl, logikTreu_schleife (by intro g' he; cases he) (by intro h0 he; cases he)⟩
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
    exact Or.inr ⟨_, _, rfl, rfl, ⟨fun _ _ => ⟨g, rfl⟩, by intro h0 he; cases he⟩⟩

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


end Gabbro.Grammatik
