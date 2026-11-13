module
public import Bruecke.Kette.Pflichten
public import Bruecke.Kette.Lauf
public import Bruecke.Kette.Realisierung
public import Bruecke.Teil.Simulation
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

theorem lauf_P_G {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : GetragenG u C) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, C c → ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body)
    (c : (declOf u).Fn) (hc : C c) (O' : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (hRR : RespektiertRahmen P R) (σ : World (declOf u)) (ρ : Env (declOf u) ((declOf u).params c)) :
    (∀ e, execEnd (V := vertragVon (declOf u) c) O' passes R (P.rumpf c) σ ρ = .logik e →
      ∃ (g : (declOf u).Fn) (σr : World (declOf u)) (envA : Env (declOf u) ((declOf u).params g)),
        C g ∧ R g σr envA = .logik e) ∧
    (∀ σ' v, execEnd (V := vertragVon (declOf u) c) O' passes R (P.rumpf c) σ ρ = .zurueck σ' v →
      EnsAmRueck P c σ σ' ρ v) := by
  have G := gesenkt_of_teil S.toGetragen hlow
  have hlowAll : ∀ c : Fin u.fns.length, C c → ∃ b0,
      lowBody u c (fnAt u c).body (fnAt u c).ret = .ok b0 :=
    fun c hc => (G.rumpf c hc).imp fun _ h => h.1
  obtain ⟨ρP, hP⟩ := realisiert_alle_G S.toGetragen hZ hlowAll rk hR
  obtain ⟨b0, hb0, hPb⟩ := G.rumpf c hc
  obtain ⟨body, hbody, hmeets⟩ := hZ c hc
  let ρ₀ : Env (declOf u) (ctxOf u c) := cast (congrArg (Env (declOf u)) (ctxParams_eq u c).symm) ρ
  have hρ : HEq ρ ρ₀ := (cast_heq _ _).symm
  have hW0 : WRel u σ (eintritt u c σ ρ).world := wrel_enc u σ _
  have hL : LRel (fnAt u c) 0 ρ (eintritt u c σ ρ).local' := eintritt_lrel c σ ρ
  have hL0 : LRel (fnAt u c) 0 ρ₀ (eintritt u c σ ρ).local' := fun p j hj =>
    (hL p j hj).trans (nthVal_heq (ctxParams_eq u c).symm ρ ρ₀ hρ _)
  have hlauf := lauf_G G S.toGetragen c hc O' passes R hRR (fnAt u c).ret ((fnAt u c).body.length + 1)
    ((fnAt u c).body.length + 1) (fnAt u c).body (fnAt u c) (fnAt u c) b0 body (UmfangB.start c (S.art c hc) (S.namen c hc))
    (Sicht.refl _) (fun _ hm => hm) (S.frisch c hc) hb0 hbody σ ρ₀ _ hW0 hL0
  have hX := execEnd_heq (V := verOf u c) O' passes R (ctxParams_eq u c).symm
    (anfangRes_eq u c).symm (P.rumpf c) b0 hPb σ ρ ρ₀ hρ
  refine ⟨fun e h => hlauf.1 e ((logik_heq (ctxParams_eq u c).symm _ _ hX _).mp h),
    fun σ' v h => ?_⟩
  have h0 := (zurueck_heq (ctxParams_eq u c).symm _ _ hX σ' v).mp h
  obtain ⟨A, hg, _, hk, hrun⟩ := hlauf.2 σ' v h0
  have hB := tabEnv_gut_teil hg ρP hP
  obtain ⟨s'', h1, h2, h3⟩ := hrun (tabEnv A ρP) (tabEnv_treu hk ρP)
    (fun n d hd hgf => (hB n d hd hgf).2)
  have hwf : wfU u (eintritt u c σ ρ) := wf_of_wrel u S.boolTab hW0
  have hpre := preExpr_wahr (fnAt u c) ρ (eintritt u c σ ρ).local' (eintritt u c σ ρ).world
    (S.namen c hc) (params_eq u c) hL
  have hm := hmeets (tabEnv A ρP) (eintritt u c σ ρ) hwf hpre
  obtain ⟨s', hs', hpost⟩ := hyps_elim (wfU u) (tabEnv A ρP) (calleesOf (fnAt u c)) _
    (fun g hg => by
      obtain ⟨args, hm'⟩ := mem_calleesOf hg
      obtain ⟨gf, hgf⟩ := callee_gefundenZ hbody g args hm'
      obtain ⟨d, rfl, _⟩ := fnSuch_mem hgf
      exact ⟨fnAt u d, hgf, hB g d (S.geschlossen c hc g hg d hgf) hgf⟩) hm
  rw [h1] at hs'
  cases hs'
  rw [h2] at hpost
  exact (post_iff_teil G c hc (S.art c hc) S.tab (S.frei c hc) (S.olds c hc) (S.post c hc) (S.boolErg c hc) S.boolTab
    σ σ' ρ v _ _ hW0 hL h3).mp hpost

end Gabbro.Bruecke
