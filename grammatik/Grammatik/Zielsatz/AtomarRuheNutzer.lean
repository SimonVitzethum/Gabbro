/-
  File:      Grammatik/Zielsatz/AtomarRuheNutzer.lean
  Subject:   The user's obligation WITH THE ATOMIC RELY on `P` is the obligation on `P.mitRuhe`
             (the idle root added): `logikPflichtA_mitRuhe`, the twin of `logikPflicht_mitRuhe`
             (RuheNutzer.lean). Opus lane O25b, 2026-09-26. Standalone.
-/
import Grammatik.Zielsatz.RuheNutzer
import Grammatik.Speichermodell.AtomarRuhe
import Grammatik.Zielsatz.AtomarPflicht

namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration}

/-- The atomic environment of `D`, from one of `D.mitRuhe`. -/
def umweltZA (A' : AUmwelt D.mitRuhe) : AUmwelt D := fun X σ => worldZ (A' X (worldR σ))

theorem umweltZA_ru (A' : AUmwelt D.mitRuhe) (X : List (D.Tab ⊕ D.Glob)) (σ : World D) :
    A' X (worldR σ) = worldR (umweltZA A' X σ) := (worldR_worldZ _).symm

theorem havocA_umweltZA {T : D.Tab ⊕ D.Glob → Prop} {A' : AUmwelt D.mitRuhe}
    (h : HavocA (D := D.mitRuhe) T A') : HavocA T (umweltZA A') := by
  intro X σ
  obtain ⟨h1, h2⟩ := h X (worldR σ)
  refine ⟨?_, fun c hc => ?_⟩
  · show (A' X (worldR σ)).spur.map evZ = σ.spur
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

/-- The body of `some f`, related to the body of `f` under the answering
    oracle, move and handler of `D`. -/
theorem rumpfA_rel (P : Programm D) (S : SperrInv D) (passes : Nat) (O' : Orakel D.mitRuhe)
    (U' : Umwelt D.mitRuhe) (A' : AUmwelt D.mitRuhe) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) → RufAusgang f)
    (hR : RufRel R R') (f : D.Fn) (σ0 : World D) (ρ0 : Env D (D.params f)) :
    @EndRel D (vertragVon D f) false (D.params f)
      (execEndHA S.mitRuhe O' U' A' passes R' (P.mitRuhe.rumpf (some f)) (worldR σ0) (envR ρ0))
      (execEndHA S (Orakel.zurueck O') (umweltZ U') (umweltZA A') passes R (P.rumpf f) σ0 ρ0) := by
  exact rumpfHA_mitRuhe P S (Orakel.zurueck O') O' (orakelRu_zurueck O') (umweltZ U') U'
    (umweltZA A') A' passes R R' (umweltZ_ru U') (umweltZA_ru A') hR f σ0 ρ0

/-! ## 2. The user obligation at `some f` -/

section Transfer

variable {P : Programm D} {passes : Nat} {Q : AxEns D} {S : SperrInv D} {f : D.Fn}
  {T : D.Tab ⊕ D.Glob → Prop}

theorem koerperGutSA_mitRuhe (h : KoerperGutSA P passes Q S T f) :
    KoerperGutSA P.mitRuhe passes (axEnsRuhe Q) S.mitRuhe T (some f) := by
  refine ⟨fun O' hr hl hq U' hU' A' hA' R' hR hOV σ ρ hreq => ?_,
    fun O' hr hl hq U' hU' A' hA' R' hR hOL σ ρ hreq => ?_⟩
  · obtain ⟨σ0, rfl⟩ : ∃ σ0, σ = worldR σ0 := ⟨worldZ σ, (worldR_worldZ σ).symm⟩
    obtain ⟨ρ0, rfl⟩ : ∃ ρ0 : Env D (D.params f), ρ = envR ρ0 :=
      ⟨envZ ρ, (envR_envZ (Γ := D.params f) ρ).symm⟩
    have hreq0 : ReqAmEintritt P f σ0 ρ0 := (req_mitRuhe_iff P f σ0 ρ0).mp hreq
    have hk := h.1 (Orakel.zurueck O') (rahmenO_zurueck hr) (regLokal_zurueck hl)
      (axVertrag_zurueck hq) (umweltZ U') (havocOk_umweltZ hU') (umweltZA A') (havocA_umweltZA hA') (rufZuD R') (respektiert_rufZuD hR)
      (ohneVorbedingung_rufZuD R') σ0 ρ0 hreq0
    have hrel := rumpfA_rel P S passes O' U' A' (rufZuD R') R' (rufRel_rufZuD hOV) f σ0 ρ0
    have hrel2 := rumpfA_rel P S passes O' U' A' (torRuf P (rufZuD R')) (torRuf P.mitRuhe R')
      (rufRel_torRuf P (rufRel_rufZuD hOV)) f σ0 ρ0
    refine ⟨fun σ' v hx => ?_, fun g hx => ?_⟩
    · rcases hrel with e | ⟨e', e, h1, h2, ht⟩
      · have e := hx.symm.trans e
        cases hy : execEndHA (V := vertragVon D f) S (Orakel.zurueck O') (umweltZ U') (umweltZA A') passes
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
        cases hy : execEndHA (V := vertragVon D f) S (Orakel.zurueck O') (umweltZ U') (umweltZA A') passes
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
      (axVertrag_zurueck hq) (umweltZ U') (havocOk_umweltZ hU') (umweltZA A') (havocA_umweltZA hA') (rufZuD R') (respektiert_rufZuD hR)
      (ohneLogik_rufZuD hOL) σ0 ρ0 hreq0
    have hrel := rumpfA_rel P S passes O' U' A' (rufZuD R') R' (rufRel_rufZuD hOV) f σ0 ρ0
    intro e' hx
    rcases hrel with e | ⟨e1, e2, h1, h2, _⟩
    · have e := hx.symm.trans e
      cases hy : execEndHA (V := vertragVon D f) S (Orakel.zurueck O') (umweltZ U') (umweltZA A') passes
          (rufZuD R') (P.rumpf f) σ0 ρ0 with
      | logik e0 => exact hk e0 hy
      | zurueck => rw [hy] at e; cases e
      | grund => rw [hy] at e; cases e
      | leave => rw [hy] at e; cases e
      | next => rw [hy] at e; cases e
      | hardware => rw [hy] at e; cases e
    · exact hk e2 h2

theorem invGutSA_mitRuhe (h : InvGutSA P passes Q S T f) :
    InvGutSA P.mitRuhe passes (axEnsRuhe Q) S.mitRuhe T (some f) := by
  intro O' hr hl hq U' hU' A' hA' R' hR hOV σ ρ hreq σ' v hx
  obtain ⟨σ0, rfl⟩ : ∃ σ0, σ = worldR σ0 := ⟨worldZ σ, (worldR_worldZ σ).symm⟩
  obtain ⟨ρ0, rfl⟩ : ∃ ρ0 : Env D (D.params f), ρ = envR ρ0 :=
    ⟨envZ ρ, (envR_envZ (Γ := D.params f) ρ).symm⟩
  have hreq0 : ReqAmEintritt P f σ0 ρ0 := (req_mitRuhe_iff P f σ0 ρ0).mp hreq
  have hk := h (Orakel.zurueck O') (rahmenO_zurueck hr) (regLokal_zurueck hl)
    (axVertrag_zurueck hq) (umweltZ U') (havocOk_umweltZ hU') (umweltZA A') (havocA_umweltZA hA') (rufZuD R') (respektiert_rufZuD hR)
    (ohneVorbedingung_rufZuD R') σ0 ρ0 hreq0
  have hrel := rumpfA_rel P S passes O' U' A' (rufZuD R') R' (rufRel_rufZuD hOV) f σ0 ρ0
  rcases hrel with e | ⟨e', e, h1, h2, ht⟩
  · have e := hx.symm.trans e
    cases hy : execEndHA (V := vertragVon D f) S (Orakel.zurueck O') (umweltZ U') (umweltZA A') passes
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

theorem invGutGrundA_mitRuhe (h : InvGutGrundA P passes Q S T f) :
    InvGutGrundA P.mitRuhe passes (axEnsRuhe Q) S.mitRuhe T (some f) := by
  intro O' hr hl hq U' hU' A' hA' R' hR hOV σ ρ hreq σ' r hx
  obtain ⟨σ0, rfl⟩ : ∃ σ0, σ = worldR σ0 := ⟨worldZ σ, (worldR_worldZ σ).symm⟩
  obtain ⟨ρ0, rfl⟩ : ∃ ρ0 : Env D (D.params f), ρ = envR ρ0 :=
    ⟨envZ ρ, (envR_envZ (Γ := D.params f) ρ).symm⟩
  have hreq0 : ReqAmEintritt P f σ0 ρ0 := (req_mitRuhe_iff P f σ0 ρ0).mp hreq
  have hk := h (Orakel.zurueck O') (rahmenO_zurueck hr) (regLokal_zurueck hl)
    (axVertrag_zurueck hq) (umweltZ U') (havocOk_umweltZ hU') (umweltZA A') (havocA_umweltZA hA') (rufZuD R') (respektiert_rufZuD hR)
    (ohneVorbedingung_rufZuD R') σ0 ρ0 hreq0
  have hrel := rumpfA_rel P S passes O' U' A' (rufZuD R') R' (rufRel_rufZuD hOV) f σ0 ρ0
  rcases hrel with e | ⟨e', e, h1, h2, ht⟩
  · have e := hx.symm.trans e
    cases hy : execEndHA (V := vertragVon D f) S (Orakel.zurueck O') (umweltZ U') (umweltZA A') passes
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
  (T : D.mitRuhe.Tab ⊕ D.mitRuhe.Glob → Prop)

theorem koerperGutSA_ruhe : KoerperGutSA P.mitRuhe passes Q S T none := by
  refine ⟨fun O' _ _ _ U _ A _ R _ _ σ ρ _ => ⟨fun σ' v hx => ?_, fun g hx => ?_⟩,
    fun O' _ _ _ U _ A _ R _ _ σ ρ _ e hx => ?_⟩
  · rfl
  · cases hx
  · cases hx

theorem invGutSA_ruhe : InvGutSA P.mitRuhe passes Q S T none :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i _ hs => absurd hs (by rw [schuldet_ruhe]; decide)

theorem invGutGrundA_ruhe : InvGutGrundA P.mitRuhe passes Q S T none :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r _ => r.elim0

end Ruhe


/-- **The user's logic with the atomic rely on `P` is the one on `P.mitRuhe`.** -/
theorem logikPflichtA_mitRuhe {P : Programm D} {S : SperrInv D} {Q : AxEns D}
    {T : D.Tab ⊕ D.Glob → Prop} (h : LogikPflichtA P S Q T) :
    LogikPflichtA P.mitRuhe S.mitRuhe (axEnsRuhe Q) T :=
  ⟨fun passes f => match f with
    | none => ⟨koerperGutSA_ruhe P passes _ _ _, invGutSA_ruhe P passes _ _ _,
        invGutGrundA_ruhe P passes _ _ _⟩
    | some f => ⟨koerperGutSA_mitRuhe (h.1 passes f).1, invGutSA_mitRuhe (h.1 passes f).2.1,
        invGutGrundA_mitRuhe (h.1 passes f).2.2⟩,
   sperrInvLokal_mitRuhe h.2.1, axEnsLokal_mitRuhe h.2.2⟩

#print axioms Gabbro.Grammatik.logikPflichtA_mitRuhe

end Gabbro.Grammatik
