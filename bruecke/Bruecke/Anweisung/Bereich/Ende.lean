module
public import Bruecke.Anweisung.Bereich.Kopf
public import Bruecke.Kette.Schritt
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

/-- Explicit ending returns share the existing return-statement simulation. -/
theorem lowRetEnd_sim {loopMode : Bool} (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn} {ns : BodyNames}
    {Λ : List (Res (declOf u))} {r : URet}
    {ending : Endblock (declOf u) (verOf u c) loopMode Γ Λ} {b : Gabbro.Body.Stmt}
    (h : lowRetEnd (l := loopMode) u c Γ fn Λ [] r = .ok ending)
    (hb : retZ u fn ns r = some b) (hU : UmfangB Γ fn ns) (hT : TabEindeutig u)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    ∃ σ' v, execEnd O passes R ending σ ρ = .zurueck σ' v ∧ WGRel u σ' s.world ∧
      ∀ ρB, Gabbro.Body.step ρB b s = .returned s (ergValOf (verOf u c).erg v) := by
  have hn : ∀ i, r ≠ .why i := by
    intro i hr
    subst r
    cases hb
  have hEnd : lowRetEnd (l := loopMode) u c Γ fn Λ [] r =
      (lowErg u c Γ Λ fn r).bind (fun erg =>
        if hp : decide (Λ.Perm (verOf u c).ende) = true then
          .ok (Endblock.ret erg (of_decide_eq_true hp))
        else .error "lower: return without produced marks") := by
    cases r
    all_goals first | rfl | exact (hn _ rfl).elim
  rw [hEnd] at h
  cases he : lowErg u c Γ Λ fn r with
  | error e => simp only [he, Except.bind] at h; cases h
  | ok erg =>
    simp only [he, Except.bind] at h
    split at h
    · rename_i hp
      cases h
      have hStmt : lowRetStmt (l := loopMode) u c Γ fn Λ [] r =
          .ok (.ret erg (of_decide_eq_true hp)) := by
        cases r
        case why i => exact (hn i rfl).elim
        all_goals simp only [lowRetStmt, he, Except.bind, hp, ↓reduceDIte]
      obtain ⟨σ', v, hex, hw, hs⟩ := lowRet_sim c hStmt hb hU hT O passes R σ ρ s hW hL
      refine ⟨σ', v, ?_, hw, hs⟩
      simp only [execStmt] at hex
      cases hex
      rfl
    · cases h

/-- Explicit endings cannot fall through; successful G returns are matched by Body returns. -/
abbrev EndZiel_G {loopMode : Bool} (u : UProg) (C : Fin u.fns.length → Prop) (c : Fin u.fns.length)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    {Γ : Ctx} {Λ : List (Res (declOf u))}
    (ending : Endblock (declOf u) (verOf u c) loopMode Γ Λ) (σ : World (declOf u))
    (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State) (bs : List Gabbro.Body.Stmt) : Prop :=
  (∀ e, execEnd O passes R ending σ ρ = .logik e →
    ∃ g σr envA, C g ∧ R g σr envA = .logik e) ∧
  (∀ σ' v, execEnd O passes R ending σ ρ = .zurueck σ' v →
    ∃ A, RueckZ_G u C A s bs σ' (ergValOf (verOf u c).erg v))

theorem endZiel_cons_G {loopMode : Bool} {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {Γ : Ctx} {Λ Λ' : List (Res (declOf u))} {fn : UFn} {ids : List String}
    {st : Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ'}
    {rest : Endblock (declOf u) (verOf u c) loopMode Γ Λ'}
    {σ : World (declOf u)} {ρ : Env (declOf u) Γ} {s : Gabbro.Body.State}
    {b : Gabbro.Body.Stmt} {bs : List Gabbro.Body.Stmt}
    (hs : StmtZiel_G u C c O passes R fn ids st σ ρ s b)
    (ih : ∀ σ₁ ρ₁ s₁, WGRel u σ₁ s₁.world → PositionalLRel fn ids 0 ρ₁ s₁.local' →
      EndZiel_G u C c O passes R rest σ₁ ρ₁ s₁ bs) :
    EndZiel_G u C c O passes R (.cons st rest) σ ρ s (b :: bs) := by
  cases he : execStmt O passes R st σ ρ with
  | ok σ₁ ρ₁ =>
    obtain ⟨A₁, s₁, hS, hW, hL⟩ := hs.2.2 σ₁ ρ₁ he
    have hh := ih σ₁ ρ₁ s₁ hW hL
    refine ⟨fun e h => hh.1 e (by simpa only [execEnd, he] using h), fun σ' v h => ?_⟩
    obtain ⟨A₂, hr⟩ := hh.2 σ' v (by simpa only [execEnd, he] using h)
    refine ⟨A₁ ++ A₂, ?_⟩
    rw [← List.singleton_append]
    exact RueckZ_G.nach hS hr
  | zurueck σ' v =>
    refine ⟨fun e h => ?_, fun σ'' v' h => ?_⟩
    · simp only [execEnd, he] at h; cases h
    · simp only [execEnd, he] at h
      cases h
      obtain ⟨A, hr⟩ := hs.2.1 σ' v he
      refine ⟨A, ?_⟩
      rw [← List.singleton_append]
      exact RueckZ_G.append hr bs
  | logik e =>
    refine ⟨fun e' h => ?_, fun σ' v h => ?_⟩
    · simp only [execEnd, he] at h
      cases h
      exact hs.1 e he
    · simp only [execEnd, he] at h; cases h
  | why σ' r | leave hl σ' ρ' | next hl σ' ρ' | hardware e =>
    exact ⟨fun e h => (by simp only [execEnd, he] at h; cases h),
      fun σ'' v' h => (by simp only [execEnd, he] at h; cases h)⟩

theorem endBodyZ_sim {loopMode : Bool} {P : Programm (declOf u)} (G : GesenktC u C P) (S : Getragen u C)
    (c : Fin u.fns.length) (hc : C c) (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (hRR : RespektiertRahmen P R) :
    ∀ n k ss {Γ : Ctx} (fn ft : UFn) (ns : BodyNames) {Λ : List (Res (declOf u))}
      (ending : Endblock (declOf u) (verOf u c) loopMode Γ Λ) (rest : List UStmt) (bs : List Gabbro.Body.Stmt),
      UmfangB Γ fn ns → Sicht u ft fn → (∀ st ∈ ss, st ∈ (fnAt u c).body) →
      lowEndL (l := loopMode) u c Γ fn n Λ [] ss = .ok (ending, rest) →
      endBodyZ u k ft ns ss = some (bs, rest) →
      ∀ σ ρ s, WGRel u σ s.world → PositionalLRel fn ns.active 0 ρ s.local' →
        EndZiel_G u C c O passes R ending σ ρ s bs
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _ => by cases h
  | _ + 1, 0, _, _, _, _, _, _, _, _, _, _, _, _, _, h => by cases h
  | _ + 1, _ + 1, [], _, _, _, _, _, _, _, _, _, _, _, _, h => by cases h
  | n + 1, k + 1, st :: ss, Γ, fn, ft, ns, Λ, ending, rest, bs, hU, hV, hm, hG, hB => by
    rcases endBodyZ_cases hB with ⟨r, b, rfl, hr, rfl, rfl⟩ | ⟨b, ys, hleaf, hs, hys, rfl⟩
    · rw [lowEndL_succ] at hG
      simp only [lowEndStep] at hG
      cases hg : lowRetEnd (l := loopMode) u c Γ fn Λ [] r with
      | error e => simp only [hg, Except.map] at hG; cases hG
      | ok e =>
        simp only [hg, Except.map] at hG
        cases hG
        have hr' := (retZ_sicht hV ns r).symm.trans hr
        intro σ ρ s hW hL
        obtain ⟨σ', v, hex, hw, hstep⟩ := lowRetEnd_sim c hg hr' hU S.tab O passes R σ ρ s hW hL
        refine ⟨fun err h => (by rw [hex] at h; cases h), fun σ'' v' h => ?_⟩
        rw [hex] at h
        cases h
        refine ⟨[], (by simp), (by simp [Oben]), List.Pairwise.nil, fun ρB _ _ => ⟨s, ?_, hw⟩⟩
        simp only [Gabbro.Body.exec, hstep ρB]
    · obtain ⟨hsN, _, _⟩ := schrittB_einzeln_sicht hV hs (endLeafB_ok hleaf)
      obtain ⟨Λ', gs, nextB, hgs, hnext, rfl⟩ := lowEndL_leaf_ok (endLeafB_ok hleaf) hG
      intro σ ρ s hW hL
      apply endZiel_cons_G
        (stmtZiel_einzeln_G G S c hc O passes R hRR (hm _ (List.mem_cons_self ..))
          (endLeafB_ok hleaf) hgs hsN hU σ ρ s hW hL)
      intro σ₁ ρ₁ s₁ hW₁ hL₁
      exact endBodyZ_sim G S c hc O passes R hRR n k ss fn ft ns nextB rest ys hU hV
        (fun st h => hm st (List.mem_cons_of_mem _ h)) hnext hys σ₁ ρ₁ s₁ hW₁ hL₁

end Gabbro.Bruecke
