module
public import Bruecke.Anweisung.Lokal.Lauf
public import Bruecke.Anweisung.Lokal.RealisierungB
public import Bruecke.Pruefung
@[expose] public section

/-!
# C5, part 5: the simulation theorem for bodies with local bindings

`bruecke_koerperGutR`, `bruecke_keineLogik`, `bruecke_logik` and `bruecke_nutzer`
(`Simulation.lean`) over the duties of `zuBodyB`: the same conclusion -- the body obligation of
premise (b) of the goal theorem -- for units whose functions use `let`, `let mut` and assignment
to a number local beside slot writes, direct calls and the trailing return. The per-unit
conditions are `Stimmig` and freshness of every binder (`StimmigLokal`), both decided
(`stimmigB`, `bindFrischAllB`).
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-! ## 1. The per-unit conditions -/

/-- `Stimmig`, and every binder of every body is fresh where it stands. -/
structure StimmigLokal (u : UProg) : Prop extends Stimmig u where
  frisch : ∀ c : Fin u.fns.length, BindFrisch (fnAt u c)

def nameFrischB (ns : List String) (x : String) : Bool :=
  decide (x ∉ ns) && decide (x ≠ "result") && decide (x ≠ "#erg") && decide (x ∉ oldNamen)

def bindFrischLB : List String → List UStmt → Bool
  | _, [] => true
  | ns, s :: ss =>
      match binderOf s with
      | some x => nameFrischB ns x && bindFrischLB (x :: ns) ss
      | none => bindFrischLB ns ss

/-- **`bindFrischB`** -- freshness of every binder of the body of `fn`, decided. -/
def bindFrischB (fn : UFn) : Bool := bindFrischLB (fn.params.map (·.1)) fn.body

def bindFrischAllB (u : UProg) : Bool := u.fns.all bindFrischB

theorem nameFrischB_ok {ns : List String} {x : String} (h : nameFrischB ns x = true) :
    NameFrisch ns x := by
  simp only [nameFrischB, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1.1.1, h.1.1.2, h.1.2, fun i e => ?_⟩
  have hm := oldName_mem i
  rw [← e] at hm
  exact h.2 hm

theorem bindFrischLB_ok : ∀ (ns : List String) (ss : List UStmt),
    bindFrischLB ns ss = true → BindFrischL ns ss
  | _, [], _ => trivial
  | ns, s :: ss, h => by
      cases hb : binderOf s with
      | none =>
        have h' : bindFrischLB ns ss = true := by simpa only [bindFrischLB, hb] using h
        have := bindFrischLB_ok ns ss h'
        simp only [BindFrischL, hb]
        exact this
      | some x =>
        have h' : nameFrischB ns x = true ∧ bindFrischLB (x :: ns) ss = true := by
          simpa only [bindFrischLB, hb, Bool.and_eq_true] using h
        simp only [BindFrischL, hb]
        exact ⟨nameFrischB_ok h'.1, bindFrischLB_ok (x :: ns) ss h'.2⟩

theorem bindFrischB_ok {fn : UFn} (h : bindFrischB fn = true) : BindFrisch fn :=
  bindFrischLB_ok _ _ h

theorem bindFrischAllB_ok (h : bindFrischAllB u = true) : ∀ c : Fin u.fns.length,
    BindFrisch (fnAt u c) :=
  fun c => bindFrischB_ok (List.all_eq_true.mp h _ (List.get_mem _ _))

theorem stimmigLokal_of (h : stimmigB u = true) (hPlain : ohneTransitionB u = true)
    (hf : bindFrischAllB u = true) : StimmigLokal u :=
  { toStimmig := stimmig_of h hPlain, frisch := bindFrischAllB_ok hf }

/-- A body `zuBody` carries has no binder: its freshness check holds. -/
theorem bindFrischLB_ohne {fn : UFn} : ∀ (ns : List String) (ss : List UStmt)
    (bs : List Gabbro.Body.Stmt), stmtsBody u fn ss = some bs → bindFrischLB ns ss = true
  | _, [], _, _ => rfl
  | ns, s :: ss, bs, h => by
      simp only [stmtsBody] at h
      split at h
      · rename_i x xs hx hxs
        have hb : binderOf s = none := by
          cases s <;> first | rfl | simp [stmtBody] at hx
        simp only [bindFrischLB, hb]
        exact bindFrischLB_ohne ns ss xs hxs
      · cases h

/-! ## 2. The run of a function, and the simulation theorem -/

/-- **The run of a function of the lowered program** (`lauf_P` for bodies with local bindings). -/
theorem lauf_PB {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : StimmigLokal u) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, ∃ body, zuBodyB u (fnAt u c) = some body ∧
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
  obtain ⟨ρP, hP⟩ := realisiert_alleB S.toStimmig hZ hlowAll rk hR
  obtain ⟨b0, hb0, hPb⟩ := G.rumpf c
  obtain ⟨body, hbody, hmeets⟩ := hZ c
  let ρ₀ : Env (declOf u) (ctxOf u c) := cast (congrArg (Env (declOf u)) (ctxParams_eq u c).symm) ρ
  have hρ : HEq ρ ρ₀ := (cast_heq _ _).symm
  have hW0 : WRel u σ (eintritt u c σ ρ).world := wrel_enc u σ _
  have hL : LRel (fnAt u c) 0 ρ (eintritt u c σ ρ).local' := eintritt_lrel c σ ρ
  have hL0 : LRel (fnAt u c) 0 ρ₀ (eintritt u c σ ρ).local' := fun p j hj =>
    (hL p j hj).trans (nthVal_heq (ctxParams_eq u c).symm ρ ρ₀ hρ _)
  have hlauf := laufB G S.toStimmig c O' passes R hRR (fnAt u c).ret ((fnAt u c).body.length + 1)
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
      obtain ⟨gf, hgf⟩ := callee_gefundenB (fnAt u c).ret (fnAt u c) (fnAt u c).body body
        hbody g args hm'
      exact ⟨gf, hgf, hB g gf hgf⟩) hm
  rw [h1] at hs'
  cases hs'
  rw [h2] at hpost
  exact (post_iff G c (S.art c) S.tab (S.frei c) (S.olds c) (S.post c) (S.boolErg c) S.boolTab
    σ σ' ρ v _ _ hW0 hL h3).mp hpost

/-- **THE SIMULATION THEOREM (S3) for bodies with local bindings.** -/
theorem bruecke_koerperGutRB {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : StimmigLokal u) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, ∃ body, zuBodyB u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body) :
    ∀ (passes : Nat) (c : (declOf u).Fn), KoerperGutR P passes c := by
  intro passes c O' _ _ R hRR hOV σ ρ _
  have hl := lauf_PB hlow S rk hR hZ c O' passes R hRR σ ρ
  refine ⟨hl.2, fun g h => ?_⟩
  rw [torRuf_eq (gesenkt_of S.ohneReq S.ohneTransition hlow) R] at h
  obtain ⟨g0, σr, envA, hR0⟩ := hl.1 _ h
  exact hOV g0 σr envA _ hR0 g rfl

/-- **No `logik` outcome of the bodies' own**, for bodies with local bindings. -/
theorem bruecke_keineLogikB {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : StimmigLokal u) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, ∃ body, zuBodyB u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body) :
    ∀ (passes : Nat) (Q : AxEns (declOf u)) (c : (declOf u).Fn), KeineLogik P passes Q c := by
  intro passes Q c O' _ _ _ R hRR hOL σ ρ _ e h
  obtain ⟨g0, σr, envA, hR0⟩ := (lauf_PB hlow S rk hR hZ c O' passes R hRR σ ρ).1 e h
  exact hOL g0 σr envA e hR0

/-- **The bodies' logic of premise (b)** (`LogikPflicht`), for bodies with local bindings. -/
theorem bruecke_logikB {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : StimmigLokal u) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, ∃ body, zuBodyB u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body)
    (hPtr : PtrVerfeinert P) :
    Zielsatz.LogikPflicht P (SperrInv.leer (declOf u)) (axWahr (declOf u)) :=
  ⟨fun passes f => ⟨koerperGutS_leer ⟨koerperGutRQ_of_R _ (bruecke_koerperGutRB hlow S rk hR hZ passes f),
      bruecke_keineLogikB hlow S rk hR hZ passes _ f⟩,
    invGutS_leer (show List.finRange u.invs.length = [] from
      List.eq_nil_of_length_eq_zero (by rw [List.length_finRange, S.ohneInv]; rfl)) f,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ r _ => by
      have h := r.isLt
      have h0 : (declOf u).gruende f = 0 := sigGruende_null u S.ohneGrund f
      omega⟩,
   fun _ _ _ _ => rfl, axEnsLokal_wahr, hPtr⟩

/-- **PREMISE (b) OF THE GOAL THEOREM, FROM GABBROV** -- for bodies with local bindings. -/
theorem bruecke_nutzerB {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : StimmigLokal u) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, ∃ body, zuBodyB u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body)
    (hPtr : PtrVerfeinert P)
    (E : Zielsatz.Einheit (declOf u)) (hP : E.P = P) (hS : E.S = SperrInv.leer (declOf u))
    (hQ : E.Q = axWahr (declOf u)) : Zielsatz.NutzerPflicht E := by
  obtain ⟨EP, ES, EQ, st, sp, ge, arenen, akku, pruefungen, grants0⟩ := E
  simp only at hP hS hQ
  subst hP hS hQ
  exact ⟨bruecke_logikB hlow S rk hR hZ hPtr,
    startPflicht_wahr _ (fun _ => rfl) (lowerAllg_requires u _ fs S.ohneReq hlow)⟩

end Gabbro.Bruecke
