module
public import Bruecke.Teil.Lauf
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

theorem realisiert_alle_teil (S : Getragen u C)
    (hZ : ∀ c : Fin u.fns.length, C c → ∃ body, zuBody u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body)
    (hlow : ∀ c : Fin u.fns.length, C c → ∃ b0, lowBody u c (fnAt u c).body (fnAt u c).ret = .ok b0)
    (rk : String → Nat) (hR : Rang u rk) :
    ∃ ρ : Gabbro.Body.Env, ∀ n c, C c → fnSuch u n = some (fnAt u c) →
      Gabbro.Body.Contract ρ n (preProp (wfU u) (fnAt u c)) (postP u (fnAt u c)) ∧ Gabbro.Body.Frame ρ n (fnAt u c).puts := by
  let K := (u.fns.map (fun f => rk f.name)).foldr max 0 + 1
  obtain ⟨ρ, hρ⟩ := realisiert_teil S hZ hlow rk hR K
  refine ⟨ρ, fun n c hc hgf => hρ n c hc hgf ?_⟩
  have hname : (fnAt u c).name = n := by simpa using List.find?_some hgf
  have hmem : rk n ∈ u.fns.map (fun f => rk f.name) := by
    rw [List.mem_map]
    exact ⟨fnAt u c, List.get_mem _ _, by rw [hname]⟩
  have : ∀ (l : List Nat) (x : Nat), x ∈ l → x ≤ l.foldr max 0 := by
    intro l x hx
    induction l with
    | nil => cases hx
    | cons y ys ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hx) (Nat.le_max_right _ _)
  have := this _ _ hmem
  omega

theorem tabEnv_gut_teil {A : List Eintrag} (hG : ∀ e ∈ A, EintragGut u e) (ρP : Gabbro.Body.Env)
    (hP : ∀ n c, C c → fnSuch u n = some (fnAt u c) →
      Gabbro.Body.Contract ρP n (preProp (wfU u) (fnAt u c)) (postP u (fnAt u c)) ∧ Gabbro.Body.Frame ρP n (fnAt u c).puts) :
    ∀ n c, C c → fnSuch u n = some (fnAt u c) →
      Gabbro.Body.Contract (tabEnv A ρP) n (preProp (wfU u) (fnAt u c)) (postP u (fnAt u c)) ∧
      Gabbro.Body.Frame (tabEnv A ρP) n (fnAt u c).puts := by
  intro n c hc hgf
  refine ⟨fun t ht => ?_, fun t p hp => ?_⟩
  · by_cases hex : ∃ e ∈ A, e.name = n ∧ e.ein = t
    · simp only [tabEnv, dif_pos hex]
      obtain ⟨hm, hn, hi⟩ := Classical.choose_spec hex
      have := (hG _ hm (fnAt u c) (by rw [hn]; exact hgf)).1 (by rw [hi]; exact ht)
      rw [hi] at this
      exact this
    · simp only [tabEnv, dif_neg hex]
      exact (hP n c hc hgf).1 t ht
  · by_cases hex : ∃ e ∈ A, e.name = n ∧ e.ein = t
    · simp only [tabEnv, dif_pos hex]
      obtain ⟨hm, hn, hi⟩ := Classical.choose_spec hex
      have := (hG _ hm (fnAt u c) (by rw [hn]; exact hgf)).2 p hp
      rw [hi] at this
      exact this
    · simp only [tabEnv, dif_neg hex]
      exact (hP n c hc hgf).2 t p hp

theorem lauf_P_teil {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : Getragen u C) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, C c → ∃ body, zuBody u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body)
    (c : (declOf u).Fn) (hc : C c) (O' : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (hRR : RespektiertRahmen P R) (σ : World (declOf u)) (ρ : Env (declOf u) ((declOf u).params c)) :
    (∀ e, execEnd (V := vertragVon (declOf u) c) O' passes R (P.rumpf c) σ ρ = .logik e →
      ∃ (g : (declOf u).Fn) (σr : World (declOf u)) (envA : Env (declOf u) ((declOf u).params g)),
        C g ∧ R g σr envA = .logik e) ∧
    (∀ σ' v, execEnd (V := vertragVon (declOf u) c) O' passes R (P.rumpf c) σ ρ = .zurueck σ' v →
      EnsAmRueck P c σ σ' ρ v) := by
  have G := gesenkt_of_teil S hlow
  have hlowAll : ∀ c : Fin u.fns.length, C c → ∃ b0,
      lowBody u c (fnAt u c).body (fnAt u c).ret = .ok b0 :=
    fun c hc => (G.rumpf c hc).imp fun _ h => h.1
  obtain ⟨ρP, hP⟩ := realisiert_alle_teil S hZ hlowAll rk hR
  obtain ⟨b0, hb0, hPb⟩ := G.rumpf c hc
  obtain ⟨body, hbody, hmeets⟩ := hZ c hc
  rw [zuBody_eq] at hbody
  cases hbs : stmtsBody u (fnAt u c) (fnAt u c).body with
  | none => rw [hbs] at hbody; cases hbody
  | some bs =>
  rw [hbs] at hbody
  cases heB : endBody u (fnAt u c) (fnAt u c).ret with
  | none => rw [heB] at hbody; cases hbody
  | some eB =>
  rw [heB] at hbody
  simp only [Option.map_some, Option.some.injEq] at hbody
  subst hbody
  let ρ₀ : Env (declOf u) (ctxOf u c) := cast (congrArg (Env (declOf u)) (ctxParams_eq u c).symm) ρ
  have hρ : HEq ρ ρ₀ := (cast_heq _ _).symm
  have hW0 : WRel u σ (eintritt u c σ ρ).world := wrel_enc u σ _
  have hL : LRel (fnAt u c) 0 ρ (eintritt u c σ ρ).local' := eintritt_lrel c σ ρ
  have hL0 : LRel (fnAt u c) 0 ρ₀ (eintritt u c σ ρ).local' := fun p j hj =>
    (hL p j hj).trans (nthVal_heq (ctxParams_eq u c).symm ρ ρ₀ hρ _)
  have hlauf := lauf_teil G S c hc O' passes R hRR _ eB heB _ b0 bs (fun _ hm => hm) hb0 hbs σ ρ₀ _ hW0 hL0
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
      obtain ⟨gf, hgf⟩ := callee_gefunden hbs hm'
      obtain ⟨d, rfl, _⟩ := fnSuch_mem hgf
      exact ⟨fnAt u d, hgf, hB g d (S.geschlossen c hc g hg d hgf) hgf⟩) hm
  rw [h1] at hs'
  cases hs'
  rw [h2] at hpost
  exact (post_iff_teil G c hc (S.art c hc) S.tab (S.frei c hc) (S.olds c hc) (S.post c hc) (S.boolErg c hc) S.boolTab σ σ' ρ v _ _
    hW0 hL h3).mp hpost

end Gabbro.Bruecke
