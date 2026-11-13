module
public import Bruecke.Anweisung.Zweig.Lauf
public import Bruecke.Anweisung.Zweig.Realisierung
public import Bruecke.Anweisung.Lokal.SimulationB
@[expose] public section

/-!
# C6, part 9: the simulation theorem for bodies with conditionals

`lauf_PZ`, `bruecke_koerperGutRZ`, `bruecke_keineLogikZ`, `bruecke_logikZ` and `bruecke_nutzerZ`
(`Lokal/SimulationB.lean`) over the duties of `zuBodyZ`: the same conclusion -- the body
obligation of premise (b) of the goal theorem -- for units whose functions branch with
`if`/`else` (non-terminal, the arms read as blocks) beside `let`, `let mut`, assignment to a
number local, slot writes, direct calls, `return` inside a branch and the trailing return. The
per-unit conditions are `StimmigLokal` (freshness of every binder over the flat body), decided.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-! ## 1. The run of a function, and the simulation theorem -/

/-- **The run of a function of the lowered program** (`lauf_P` for bodies with conditionals). -/
theorem lauf_PZ {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : StimmigLokal u) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body)
    (c : (declOf u).Fn) (O' : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (hRR : RespektiertRahmen P R) (σ : World (declOf u)) (ρ : Env (declOf u) ((declOf u).params c)) :
    (∀ e, execEnd (V := vertragVon (declOf u) c) O' passes R (P.rumpf c) σ ρ = .logik e →
      ∃ (g : (declOf u).Fn) (σr : World (declOf u)) (envA : Env (declOf u) ((declOf u).params g)),
        R g σr envA = .logik e) ∧
    (∀ σ' v, execEnd (V := vertragVon (declOf u) c) O' passes R (P.rumpf c) σ ρ = .zurueck σ' v →
      EnsAmRueck P c σ σ' ρ v) := by
  have G := gesenkt_of S.ohneReq S.ohneTransition hlow
  have hlowAll : ∀ c : Fin u.fns.length, ∃ b0,
      lowBody u c (fnAt u c).body (fnAt u c).ret = .ok b0 :=
    fun c => (G.rumpf c).imp fun _ h => h.1
  obtain ⟨ρP, hP⟩ := realisiert_alleZ S.toStimmig hZ hlowAll rk hR
  obtain ⟨b0, hb0, hPb⟩ := G.rumpf c
  obtain ⟨body, hbody, hmeets⟩ := hZ c
  let ρ₀ : Env (declOf u) (ctxOf u c) := cast (congrArg (Env (declOf u)) (ctxParams_eq u c).symm) ρ
  have hρ : HEq ρ ρ₀ := (cast_heq _ _).symm
  have hW0 : WRel u σ (eintritt u c σ ρ).world := wrel_enc u σ _
  have hL : LRel (fnAt u c) 0 ρ (eintritt u c σ ρ).local' := eintritt_lrel c σ ρ
  have hL0 : LRel (fnAt u c) 0 ρ₀ (eintritt u c σ ρ).local' := fun p j hj =>
    (hL p j hj).trans (nthVal_heq (ctxParams_eq u c).symm ρ ρ₀ hρ _)
  have hlauf := laufZ G S.toStimmig c O' passes R hRR (fnAt u c).ret ((fnAt u c).body.length + 1)
    ((fnAt u c).body.length + 1)
    (fnAt u c).body (fnAt u c) (fnAt u c) b0 body (UmfangB.start c (S.art c) (S.namen c))
    (Sicht.refl _) (S.frisch c) hb0 hbody σ ρ₀ _ hW0 hL0
  have hX := execEnd_heq (V := verOf u c) O' passes R (ctxParams_eq u c).symm
    (anfangRes_eq u c).symm (P.rumpf c) b0 hPb σ ρ ρ₀ hρ
  refine ⟨fun e h => hlauf.1 e ((logik_heq (ctxParams_eq u c).symm _ _ hX _).mp h),
    fun σ' v h => ?_⟩
  have h0 := (zurueck_heq (ctxParams_eq u c).symm _ _ hX σ' v).mp h
  obtain ⟨A, hg, _, hk, hrun⟩ := hlauf.2 σ' v h0
  have hB := tabEnv_gut hg ρP hP
  obtain ⟨s'', h1, h2, h3⟩ := hrun (tabEnv A ρP) (tabEnv_treu hk ρP)
    (fun n gf hgf => (hB n gf hgf).2)
  have hwf : wfU u (eintritt u c σ ρ) := wf_of_wrel u S.boolTab hW0
  have hpre := preExpr_wahr (fnAt u c) ρ (eintritt u c σ ρ).local' (eintritt u c σ ρ).world
    (S.namen c) (params_eq u c) hL
  have hm := hmeets (tabEnv A ρP) (eintritt u c σ ρ) hwf hpre
  obtain ⟨s', hs', hpost⟩ := hyps_elim (wfU u) (tabEnv A ρP) (calleesOf (fnAt u c)) _
    (fun g hg => by
      obtain ⟨args, hm'⟩ := mem_calleesOf hg
      obtain ⟨gf, hgf⟩ := callee_gefundenZ hbody g args hm'
      exact ⟨gf, hgf, hB g gf hgf⟩) hm
  rw [h1] at hs'
  cases hs'
  rw [h2] at hpost
  exact (post_iff G c (S.art c) S.tab (S.frei c) (S.olds c) (S.post c) (S.boolErg c) S.boolTab
    σ σ' ρ v _ _ hW0 hL h3).mp hpost

/-- **THE SIMULATION THEOREM (S3) for bodies with conditionals.** -/
theorem bruecke_koerperGutRZ {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : StimmigLokal u) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body) :
    ∀ (passes : Nat) (c : (declOf u).Fn), KoerperGutR P passes c := by
  intro passes c O' _ _ R hRR hOV σ ρ _
  have hl := lauf_PZ hlow S rk hR hZ c O' passes R hRR σ ρ
  refine ⟨hl.2, fun g h => ?_⟩
  rw [torRuf_eq (gesenkt_of S.ohneReq S.ohneTransition hlow) R] at h
  obtain ⟨g0, σr, envA, hR0⟩ := hl.1 _ h
  exact hOV g0 σr envA _ hR0 g rfl

/-- **No `logik` outcome of the bodies' own**, for bodies with conditionals. -/
theorem bruecke_keineLogikZ {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : StimmigLokal u) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body) :
    ∀ (passes : Nat) (Q : AxEns (declOf u)) (c : (declOf u).Fn), KeineLogik P passes Q c := by
  intro passes Q c O' _ _ _ R hRR hOL σ ρ _ e h
  obtain ⟨g0, σr, envA, hR0⟩ := (lauf_PZ hlow S rk hR hZ c O' passes R hRR σ ρ).1 e h
  exact hOL g0 σr envA e hR0

/-- **The bodies' logic of premise (b)** (`LogikPflicht`), for bodies with conditionals. -/
theorem bruecke_logikZ {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : StimmigLokal u) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body)
    (hPtr : PtrVerfeinert P) :
    Zielsatz.LogikPflicht P (SperrInv.leer (declOf u)) (axWahr (declOf u)) :=
  ⟨fun passes f => ⟨koerperGutS_leer ⟨koerperGutRQ_of_R _ (bruecke_koerperGutRZ hlow S rk hR hZ passes f),
      bruecke_keineLogikZ hlow S rk hR hZ passes _ f⟩,
    invGutS_leer (show List.finRange u.invs.length = [] from
      List.eq_nil_of_length_eq_zero (by rw [List.length_finRange, S.ohneInv]; rfl)) f,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ r _ => by
      have h := r.isLt
      have h0 : (declOf u).gruende f = 0 := sigGruende_null u S.ohneGrund f
      omega⟩,
   fun _ _ _ _ => rfl, axEnsLokal_wahr, hPtr⟩

/-- **PREMISE (b) OF THE GOAL THEOREM, FROM GABBROV** -- for bodies with conditionals. -/
theorem bruecke_nutzerZ {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : StimmigLokal u) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body)
    (hPtr : PtrVerfeinert P)
    (E : Zielsatz.Einheit (declOf u)) (hP : E.P = P) (hS : E.S = SperrInv.leer (declOf u))
    (hQ : E.Q = axWahr (declOf u)) : Zielsatz.NutzerPflicht E := by
  obtain ⟨EP, ES, EQ, st, sp, ge, arenen, akku, pruefungen, grants0⟩ := E
  simp only at hP hS hQ
  subst hP hS hQ
  exact ⟨bruecke_logikZ hlow S rk hR hZ hPtr,
    startPflicht_wahr _ (fun _ => rfl) (lowerAllg_requires u _ fs S.ohneReq hlow)⟩

end Gabbro.Bruecke
