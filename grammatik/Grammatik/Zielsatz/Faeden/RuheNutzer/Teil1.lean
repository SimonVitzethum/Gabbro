module
public import Grammatik.Zielsatz.Faeden.RuheNutzer.Teil1Basis
import all Grammatik.Zielsatz.Faeden.RuheNutzer.Teil1Basis

public import Grammatik.Zielsatz.Kern.Spec
public import Grammatik.Zielsatz.Faeden.RuheNutzer.Ptr
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSperre

@[expose] public section



namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration}
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
        | why => rw [hy] at e; cases e
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
        | why => rw [hy] at e; cases e
        | leave => rw [hy] at e; cases e
        | next => rw [hy] at e; cases e
        | hardware => rw [hy] at e; cases e
      · have h1 := hx.symm.trans h1
        cases h1
        obtain ⟨g0, hg0⟩ := ht.1 g rfl
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
      | why => rw [hy] at e; cases e
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
    | why => rw [hy] at e; cases e
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
    | why σa ra =>
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
  intro c _ hc
  cases c with
  | inl t =>
      exact Bool.noConfusion ((show (D.mitRuhe).schreibt none t = false from rfl).symm.trans hc)
  | inr g =>
      exact Bool.noConfusion ((show (D.mitRuhe).gschreibt none g = false from rfl).symm.trans hc)

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
   sperrInvLokal_mitRuhe h.2.1, ⟨axEnsLokal_mitRuhe h.2.2.1, ptrVerfeinert_mitRuhe h.2.2.2⟩⟩

theorem axiomSpur_map (tabs : List D.Tab) (globs : List D.Glob) (a : D.Ax) (Λ : List (Res D))
    (h : List D.Lock) :
    (axiomSpur tabs globs a Λ h).map evR = axiomSpur (D := D.mitRuhe) tabs globs a (Λ.map resR) h := by
  unfold axiomSpur
  simp only [List.map_append, List.map_map]
  rfl

end Gabbro.Grammatik
