import Bruecke.Realisierung

/-!
# S3: THE SIMULATION THEOREM -- GabbroV's duties give the goal theorem's body obligation

For every unit the Lean parser lowers (`lowerAllg u = .ok (P, fs)`, the program of the SOURCE
TEXT), whose call graph has a rank and which passes the per-unit name checks (`Stimmig`): if every
duty GabbroV states -- `meetsU`, computed in Lean from the same `UProg` (`Pflichten.lean`) -- is
proved, then every function of the lowered program meets `KoerperGutR`, the body obligation of
premise (b) of the goal theorem, at every budget.

The proof is the run simulation (`Lauf.lean`): a G run with a contract- and frame-respecting
handler `R` that returns, and the Body run of `zuBody` in an environment that answers every call
the run makes as `R` did (the answer table) and every other entry state as the program's own
bodies do (`realisiert`), end in related states with the same answer; the duty's promise there
is the goal theorem's return check (`post_iff`).
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-! ## 1. The environment for every rank -/

theorem realisiert_alle (S : Stimmig u)
    (hZ : ∀ c : Fin u.fns.length, ∃ body, zuBody u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body)
    (hlow : ∀ c : Fin u.fns.length, ∃ b0, lowBody u c (fnAt u c).saetze (fnAt u c).rueck = .ok b0)
    (rk : String → Nat) (hR : Rang u rk) :
    ∃ ρ : Gabbro.Body.Env, ∀ n gf, fnSuch u n = some gf →
      Gabbro.Body.Contract ρ n (preProp (wfU u) gf) (postP u gf) ∧ Gabbro.Body.Frame ρ n gf.schreibt := by
  let K := (u.fns.map (fun f => rk f.name)).foldr max 0 + 1
  obtain ⟨ρ, hρ⟩ := realisiert S hZ hlow rk hR K
  refine ⟨ρ, fun n gf hgf => hρ n gf hgf ?_⟩
  obtain ⟨c, rfl, hname⟩ := fnSuch_mem hgf
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

/-! ## 2. The environment of a table -/

theorem schluessel_eind {A : List Eintrag} (hA : Schluessel A) :
    ∀ e₁ ∈ A, ∀ e₂ ∈ A, e₁.name = e₂.name → e₁.ein = e₂.ein → e₁ = e₂ := by
  induction A with
  | nil => intro e₁ h; cases h
  | cons a l ih =>
    intro e₁ h₁ e₂ h₂ hn he
    rcases List.mem_cons.mp h₁ with r₁ | m₁
    · rcases List.mem_cons.mp h₂ with r₂ | m₂
      · rw [r₁, r₂]
      · subst r₁; exact absurd ⟨hn, he⟩ (List.rel_of_pairwise_cons hA m₂)
    · rcases List.mem_cons.mp h₂ with r₂ | m₂
      · subst r₂; exact absurd ⟨hn.symm, he.symm⟩ (List.rel_of_pairwise_cons hA m₁)
      · exact ih hA.of_cons e₁ m₁ e₂ m₂ hn he

/-- The table's answer where the table has one, `ρP`'s everywhere else. -/
noncomputable def tabEnv (A : List Eintrag) (ρP : Gabbro.Body.Env) : Gabbro.Body.Env := fun n t =>
  haveI := Classical.propDecidable (∃ e ∈ A, e.name = n ∧ e.ein = t)
  if h : ∃ e ∈ A, e.name = n ∧ e.ein = t then (Classical.choose h).aus else ρP n t

theorem tabEnv_treu {A : List Eintrag} (hA : Schluessel A) (ρP : Gabbro.Body.Env) :
    Treu A (tabEnv A ρP) := by
  intro e he
  have hex : ∃ e' ∈ A, e'.name = e.name ∧ e'.ein = e.ein := ⟨e, he, rfl, rfl⟩
  simp only [tabEnv, dif_pos hex]
  obtain ⟨hm, hn, hi⟩ := Classical.choose_spec hex
  rw [schluessel_eind hA _ hm e he hn hi]

theorem tabEnv_gut {A : List Eintrag} (hG : ∀ e ∈ A, EintragGut u e) (ρP : Gabbro.Body.Env)
    (hP : ∀ n gf, fnSuch u n = some gf →
      Gabbro.Body.Contract ρP n (preProp (wfU u) gf) (postP u gf) ∧ Gabbro.Body.Frame ρP n gf.schreibt) :
    ∀ n gf, fnSuch u n = some gf →
      Gabbro.Body.Contract (tabEnv A ρP) n (preProp (wfU u) gf) (postP u gf) ∧
      Gabbro.Body.Frame (tabEnv A ρP) n gf.schreibt := by
  intro n gf hgf
  refine ⟨fun t ht => ?_, fun t p hp => ?_⟩
  · by_cases hex : ∃ e ∈ A, e.name = n ∧ e.ein = t
    · simp only [tabEnv, dif_pos hex]
      obtain ⟨hm, hn, hi⟩ := Classical.choose_spec hex
      have := (hG _ hm gf (by rw [hn]; exact hgf)).1 (by rw [hi]; exact ht)
      rw [hi] at this
      exact this
    · simp only [tabEnv, dif_neg hex]
      exact (hP n gf hgf).1 t ht
  · by_cases hex : ∃ e ∈ A, e.name = n ∧ e.ein = t
    · simp only [tabEnv, dif_pos hex]
      obtain ⟨hm, hn, hi⟩ := Classical.choose_spec hex
      have := (hG _ hm gf (by rw [hn]; exact hgf)).2 p hp
      rw [hi] at this
      exact this
    · simp only [tabEnv, dif_neg hex]
      exact (hP n gf hgf).2 t p hp

/-! ## 3. Transport of a run along the lowering's type equations -/

theorem execEnd_heq {D : Deklaration} {V : Vertrag D} {Γ₁ Γ₂ : Ctx} {Λ₁ Λ₂ : List (Res D)}
    (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (hΓ : Γ₁ = Γ₂) (hΛ : Λ₁ = Λ₂) (b₁ : Endblock D V false Γ₁ Λ₁) (b₂ : Endblock D V false Γ₂ Λ₂)
    (hb : HEq b₁ b₂) (σ : World D) (ρ₁ : Env D Γ₁) (ρ₂ : Env D Γ₂) (hρ : HEq ρ₁ ρ₂) :
    HEq (execEnd O passes R b₁ σ ρ₁) (execEnd O passes R b₂ σ ρ₂) := by
  subst hΓ; subst hΛ; cases hb; cases hρ; rfl

theorem zurueck_heq {D : Deklaration} {V : Vertrag D} {Γ₁ Γ₂ : Ctx} (hΓ : Γ₁ = Γ₂)
    (x₁ : EndAusgang V false Γ₁) (x₂ : EndAusgang V false Γ₂) (hx : HEq x₁ x₂)
    (σ' : World D) (v : ErgVal D V.erg) :
    x₁ = .zurueck σ' v ↔ x₂ = .zurueck σ' v := by
  subst hΓ; cases hx; rfl

theorem logik_heq {D : Deklaration} {V : Vertrag D} {Γ₁ Γ₂ : Ctx} (hΓ : Γ₁ = Γ₂)
    (x₁ : EndAusgang V false Γ₁) (x₂ : EndAusgang V false Γ₂) (hx : HEq x₁ x₂) (e : Logik D) :
    x₁ = .logik e ↔ x₂ = .logik e := by
  subst hΓ; cases hx; rfl

/-! ## 4. The simulation theorem -/

/-- The Body entry state of `c` at a G entry: the G world written over a zero world, every
    parameter name bound to its position's value. -/
def eintritt (u : UProg) (c : Fin u.fns.length) (σ : World (declOf u))
    (ρ : Env (declOf u) ((declOf u).params c)) : Gabbro.Body.State :=
  ⟨enc u σ (fun _ => .int 0), fun p => match paramPos (fnAt u c).params p with
    | .ok j => nthVal ρ j
    | .error _ => .absent⟩

theorem eintritt_lrel (c : Fin u.fns.length) (σ : World (declOf u))
    (ρ : Env (declOf u) ((declOf u).params c)) : LRel (fnAt u c) 0 ρ (eintritt u c σ ρ).local' := by
  intro p j hj
  simp [eintritt, hj]

/-- Without a `requires`, the gate lets every call through. -/
theorem torRuf_eq {P : Programm (declOf u)} (G : Gesenkt u P)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f) :
    torRuf P R = R := by
  funext g σ ρ
  unfold torRuf
  rw [G.req g]
  rfl

/-- **The run of a function of the lowered program, read back to the program's own types**:
    every `logik` outcome is the handler's, and where the run returns, the duty file's promise at
    the Body run of `zuBody` is the goal theorem's return check. -/
theorem lauf_P {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : Stimmig u) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, ∃ body, zuBody u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body)
    (c : (declOf u).Fn) (O' : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (hRR : RespektiertRahmen P R) (σ : World (declOf u)) (ρ : Env (declOf u) ((declOf u).params c)) :
    (∀ e, execEnd (V := vertragVon (declOf u) c) O' passes R (P.rumpf c) σ ρ = .logik e →
      ∃ (g : (declOf u).Fn) (σr : World (declOf u)) (envA : Env (declOf u) ((declOf u).params g)),
        R g σr envA = .logik e) ∧
    (∀ σ' v, execEnd (V := vertragVon (declOf u) c) O' passes R (P.rumpf c) σ ρ = .zurueck σ' v →
      EnsAmRueck P c σ σ' ρ v) := by
  have G := gesenkt_of hlow
  have hlowAll : ∀ c : Fin u.fns.length, ∃ b0,
      lowBody u c (fnAt u c).saetze (fnAt u c).rueck = .ok b0 :=
    fun c => (G.rumpf c).imp fun _ h => h.1
  obtain ⟨ρP, hP⟩ := realisiert_alle S hZ hlowAll rk hR
  obtain ⟨b0, hb0, hPb⟩ := G.rumpf c
  obtain ⟨body, hbody, hmeets⟩ := hZ c
  rw [zuBody_eq] at hbody
  cases hbs : stmtsBody u (fnAt u c) (fnAt u c).saetze with
  | none => rw [hbs] at hbody; cases hbody
  | some bs =>
  rw [hbs] at hbody
  cases heB : endBody u (fnAt u c) (fnAt u c).rueck with
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
  have hlauf := lauf G S c O' passes R hRR _ eB heB _ b0 bs hb0 hbs σ ρ₀ _ hW0 hL0
  have hX := execEnd_heq (V := verOf u c) O' passes R (ctxParams_eq u c).symm
    (anfangRes_eq u c).symm (P.rumpf c) b0 hPb σ ρ ρ₀ hρ
  refine ⟨fun e h => hlauf.1 e ((logik_heq (ctxParams_eq u c).symm _ _ hX _).mp h),
    fun σ' v h => ?_⟩
  have h0 := (zurueck_heq (ctxParams_eq u c).symm _ _ hX σ' v).mp h
  obtain ⟨A, hg, _, hk, hrun⟩ := hlauf.2 σ' v h0
  have hB := tabEnv_gut hg ρP hP
  obtain ⟨s'', h1, h2, h3⟩ := hrun (tabEnv A ρP) (tabEnv_treu hk ρP)
    (fun n gf hgf => (hB n gf hgf).2)
  have hwf : wfU u (eintritt u c σ ρ) := wf_of_wrel u hW0
  have hpre := preExpr_wahr (fnAt u c) ρ (eintritt u c σ ρ).local' (eintritt u c σ ρ).world
    (S.namen c) (params_eq u c) hL
  have hm := hmeets (tabEnv A ρP) (eintritt u c σ ρ) hwf hpre
  obtain ⟨s', hs', hpost⟩ := hyps_elim (wfU u) (tabEnv A ρP) (calleesOf (fnAt u c)) _
    (fun g hg => by
      obtain ⟨args, hm'⟩ := mem_calleesOf hg
      obtain ⟨gf, hgf⟩ := callee_gefunden hbs hm'
      exact ⟨gf, hgf, hB g gf hgf⟩) hm
  rw [h1] at hs'
  cases hs'
  rw [h2] at hpost
  exact (post_iff G c (S.art c) S.tab (S.frei c) (S.olds c) (S.post c) σ σ' ρ v _ _
    hW0 hL h3).mp hpost

/-- **THE SIMULATION THEOREM (S3).** For a unit the Lean parser lowers, with a ranked call graph
    and the per-unit name checks: GabbroV's duties (`meetsU`, computed in Lean from the parsed
    program) give the goal theorem's body obligation `KoerperGutR` for every function, at every
    budget. -/
theorem bruecke_koerperGutR {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : Stimmig u) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, ∃ body, zuBody u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body) :
    ∀ (passes : Nat) (c : (declOf u).Fn), KoerperGutR P passes c := by
  intro passes c O' _ _ R hRR hOV σ ρ _
  have hl := lauf_P hlow S rk hR hZ c O' passes R hRR σ ρ
  refine ⟨hl.2, fun g h => ?_⟩
  rw [torRuf_eq (gesenkt_of hlow) R] at h
  obtain ⟨g0, σr, envA, hR0⟩ := hl.1 _ h
  exact hOV g0 σr envA _ hR0 g rfl

/-- **No `logik` outcome of the bodies' own** (the second half of `KoerperGutZ`): every `logik`
    outcome of a lowered body is a callee's answer. -/
theorem bruecke_keineLogik {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : Stimmig u) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, ∃ body, zuBody u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body) :
    ∀ (passes : Nat) (Q : AxEns (declOf u)) (c : (declOf u).Fn), KeineLogik P passes Q c := by
  intro passes Q c O' _ _ _ R hRR hOL σ ρ _ e h
  obtain ⟨g0, σr, envA, hR0⟩ := (lauf_P hlow S rk hR hZ c O' passes R hRR σ ρ).1 e h
  exact hOL g0 σr envA e hR0

/-! ## 5. Premise (b) of the goal theorem -/

/-- **The bodies' logic of premise (b)** (`LogikPflicht`), for the lowered program with the
    parser's empty lock family and the trivial axiom ensures -- from GabbroV's duties. -/
theorem bruecke_logik {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : Stimmig u) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, ∃ body, zuBody u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body) :
    Zielsatz.LogikPflicht P (SperrInv.leer (declOf u)) (axWahr (declOf u)) :=
  ⟨fun passes f => ⟨koerperGutS_leer ⟨koerperGutRQ_of_R _ (bruecke_koerperGutR hlow S rk hR hZ passes f),
      bruecke_keineLogik hlow S rk hR hZ passes _ f⟩,
    invGutS_leer rfl f,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ r _ => by
      have h := r.isLt
      have h0 : (declOf u).gruende f = 0 := sigGruende_zero u f
      omega⟩,
   fun _ _ _ _ => rfl, axEnsLokal_wahr⟩

/-- **PREMISE (b) OF THE GOAL THEOREM, FROM GABBROV** -- for a unit whose program is the Lean
    parser's lowering of its source text: the bodies' logic from the duties (S3), the start from
    the shape of the lowering (S4, `startPflicht_wahr`). -/
theorem bruecke_nutzer {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (hlow : lowerAllg u = .ok (P, fs)) (S : Stimmig u) (rk : String → Nat) (hR : Rang u rk)
    (hZ : ∀ c : Fin u.fns.length, ∃ body, zuBody u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body)
    (E : Zielsatz.Einheit (declOf u)) (hP : E.P = P) (hS : E.S = SperrInv.leer (declOf u))
    (hQ : E.Q = axWahr (declOf u)) : Zielsatz.NutzerPflicht E := by
  obtain ⟨EP, ES, EQ, st, sp, ge⟩ := E
  simp only at hP hS hQ
  subst hP hS hQ
  exact ⟨bruecke_logik hlow S rk hR hZ,
    startPflicht_wahr _ (fun _ => rfl) (lowerAllg_requires u _ fs hlow)⟩

end Gabbro.Bruecke
