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
    (hb : retZ u fn ns r = some b) (hn : ∀ n, r ≠ .why n) (hU : UmfangB Γ fn ns) (hT : TabEindeutig u)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    ∃ σ' v, execEnd O passes R ending σ ρ = .zurueck σ' v ∧ WGRel u σ' s.world ∧
      ∀ ρB, Gabbro.Body.step ρB b s = .returned s (ergValOf (verOf u c).erg v) := by
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
      obtain ⟨σ', v, hex, hw, hs⟩ := lowRet_sim c hStmt hb hn hU hT O passes R σ ρ s hW hL
      refine ⟨σ', v, ?_, hw, hs⟩
      simp only [execStmt] at hex
      cases hex
      rfl
    · cases h

/-- Explicit endings share the full pass relation, including both loop controls. -/
abbrev EndZiel_G {loopMode : Bool} (u : UProg) (C : Fin u.fns.length → Prop) (c : Fin u.fns.length)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    {Γ : Ctx} {Λ : List (Res (declOf u))} (fn : UFn) (ids : List String)
    (ending : Endblock (declOf u) (verOf u c) loopMode Γ Λ) (σ : World (declOf u))
    (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State) (bs : List Gabbro.Body.Stmt) : Prop :=
  AusgangZiel_G u C c R fn ids (execEnd O passes R ending σ ρ).zuAusgang s bs

theorem endZiel_cons_G {loopMode : Bool} {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {Γ : Ctx} {Λ Λ' : List (Res (declOf u))} {fn : UFn} {ids : List String}
    {st : Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ'}
    {rest : Endblock (declOf u) (verOf u c) loopMode Γ Λ'}
    {σ : World (declOf u)} {ρ : Env (declOf u) Γ} {s : Gabbro.Body.State}
    {b : Gabbro.Body.Stmt} {bs : List Gabbro.Body.Stmt}
    (hs : StmtZiel_G u C c O passes R fn ids st σ ρ s b)
    (ih : ∀ σ₁ ρ₁ s₁, WGRel u σ₁ s₁.world → PositionalLRel fn ids 0 ρ₁ s₁.local' →
      EndZiel_G u C c O passes R fn ids rest σ₁ ρ₁ s₁ bs) :
    EndZiel_G u C c O passes R fn ids (.cons st rest) σ ρ s (b :: bs) := by
  cases he : execStmt O passes R st σ ρ with
  | ok σ₁ ρ₁ =>
    obtain ⟨A, s₁, hS, hW, hL⟩ := hs.2.2.1 σ₁ ρ₁ he
    have hh := ausgangZiel_nach hS (ih σ₁ ρ₁ s₁ hW hL)
    simpa only [EndZiel_G, execEnd, he, List.singleton_append] using hh
  | _ =>
    have hh := ausgangZiel_suffix hs (fun _ _ hh => by rw [he] at hh; cases hh) bs
    simpa only [EndZiel_G, execEnd, he, EndAusgang.zuAusgang, List.singleton_append] using hh

/-- Local scope exit transports every ending outcome, including both loop controls. -/
theorem endZiel_bind_G {l : Bool} {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {Γ : Ctx} {Λ : List (Res (declOf u))} {τ : Ty} {fn fn' : UFn} {ids ids' : List String}
    {e : Expr (declOf u) Γ Λ τ} {rest : Endblock (declOf u) (verOf u c) l (τ :: Γ) Λ}
    {σ : World (declOf u)} {ρ : Env (declOf u) Γ} {s s₁ : Gabbro.Body.State}
    {b : Gabbro.Body.Stmt} {bs : List Gabbro.Body.Stmt}
    (hstep : ∀ ρB, RahmenAlleC u C ρB → Gabbro.Body.step ρB b s = .running s₁)
    (htail : ∀ (ρ : Env (declOf u) (τ :: Γ)) β,
      PositionalLRel fn' ids' 0 ρ β → PositionalLRel fn ids 0 ρ.tail β)
    (h : EndZiel_G u C c O passes R fn' ids' rest (σ.lese Λ e.orte)
      (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) s₁ bs)
    (hworld : s₁.world = s.world) :
    EndZiel_G u C c O passes R fn ids (.bind e rest) σ ρ s (b :: bs) := by
  have hgz : ∀ w, gz w s.world ≤ gz w s₁.world := by
    intro w
    simpa only [hworld] using Int.le_refl (gz w s.world)
  let out := execEnd O passes R rest (σ.lese Λ e.orte)
    (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ)
  have heq : out.schrumpf.zuAusgang = out.zuAusgang.schrumpf := by cases out <;> rfl
  change AusgangZiel_G u C c R fn ids out.schrumpf.zuAusgang s (b :: bs)
  rw [heq]
  simpa only [List.singleton_append] using
    ausgangZiel_schrumpf (Strecke_G.schritt hstep hgz) htail h

theorem endBodyZ_sim {loopMode : Bool} {P : Programm (declOf u)} (G : GesenktC u C P) (S : Getragen u C)
    (c : Fin u.fns.length) (hc : C c) (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (hRR : RespektiertRahmen P R) :
    ∀ n k ss {Γ : Ctx} (fn ft : UFn) (ns : BodyNames) {Λ : List (Res (declOf u))}
      (ending : Endblock (declOf u) (verOf u c) loopMode Γ Λ) (rest : List UStmt) (bs : List Gabbro.Body.Stmt),
      UmfangB Γ fn ns → Sicht u ft fn → (∀ st ∈ ss, st ∈ (fnAt u c).body) →
      BindFrischL (protectedNames fn.params fn.kinds) ss →
      lowEndL (l := loopMode) u c Γ fn n Λ [] ss = .ok (ending, rest) →
      endBodyZ u k ft ns ss = some (bs, rest) →
      ∀ σ ρ s, WGRel u σ s.world → PositionalLRel fn ns.active 0 ρ s.local' →
        EndZiel_G u C c O passes R fn ns.active ending σ ρ s bs
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _ => by cases h
  | _ + 1, 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h => by cases h
  | _ + 1, _ + 1, [], _, _, _, _, _, _, _, _, _, _, _, _, _, h => by cases h
  | n + 1, k + 1, st :: ss, Γ, fn, ft, ns, Λ, ending, rest, bs, hU, hV, hm, hF, hG, hB => by
    have hmem : ∀ st ∈ ss, st ∈ (fnAt u c).body := fun st h => hm st (List.mem_cons_of_mem _ h)
    cases endBodyZ_view hB with
    | @ret r ss b hr =>
      rw [lowEndL_succ] at hG
      simp only [lowEndStep] at hG
      cases hg : lowRetEnd (l := loopMode) u c Γ fn Λ [] r with
      | error e => simp only [hg, Except.map] at hG; cases hG
      | ok e =>
        simp only [hg, Except.map] at hG
        cases hG
        have hr' := (retZ_sicht hV ns r).symm.trans hr
        intro σ ρ s hW hL
        by_cases hn : ∃ i, r = .why i
        · obtain ⟨i, rfl⟩ := hn
          obtain ⟨hlt, hp, rfl⟩ := lowRetWhyEnd_ok hg
          simp only [retZ, Option.some.injEq] at hr'
          subst b
          exact ausgangZiel_why ⟨i, hlt⟩ hW
        have hn' : ∀ i, r ≠ .why i := fun i he => hn ⟨i, he⟩
        obtain ⟨σ', v, hex, hw, hstep⟩ := lowRetEnd_sim c hg hr' hn' hU S.tab O passes R σ ρ s hW hL

        refine ⟨fun err h => (by simp only [hex, EndAusgang.zuAusgang] at h; cases h), fun σ'' v' h => ?_,
          fun σ'' ρ'' h => (by simp only [hex, EndAusgang.zuAusgang] at h; cases h),
          fun leave hl σ'' ρ'' h => (by cases leave <;>
            simp only [hex, EndAusgang.zuAusgang, controlG, Bool.false_eq_true, ↓reduceIte] at h <;> cases h),
          fun σ' r h => (by simp only [hex, EndAusgang.zuAusgang] at h; cases h)⟩
        simp only [hex, EndAusgang.zuAusgang] at h
        cases h
        refine ⟨[], (by simp), (by simp [Oben]), List.Pairwise.nil, fun ρB _ _ => ⟨s, ?_, hw⟩⟩
        simp only [Gabbro.Body.exec, hstep ρB]
    | control leave x ss =>
      obtain ⟨hl, -, -⟩ := lowEnd_control_ok hG
      intro σ ρ s hW hL
      have hh := stmtZiel_control_G (c := c) (C := C) (O := O) (passes := passes)
        (R := R) (Λ := Λ) leave hl σ ρ s hW hL
      cases leave <;> simpa only [EndZiel_G, controlEnd, controlStmt, controlStmtB, execEnd,
        EndAusgang.zuAusgang, StmtZiel_G, execStmt] using hh
    | @leaf st ss b ys tail hleaf hs hys =>
      obtain ⟨hsN, _, _⟩ := schrittB_einzeln_sicht hV hs (endLeafB_ok hleaf)
      obtain ⟨Λ', gs, nextB, hgs, hnext, rfl⟩ := lowEndL_leaf_ok (endLeafB_ok hleaf) hG
      intro σ ρ s hW hL
      apply endZiel_cons_G
        (stmtZiel_einzeln_G G S c hc O passes R hRR (hm _ (List.mem_cons_self ..))
          (endLeafB_ok hleaf) hgs hsN hU σ ρ s hW hL)
      intro σ₁ ρ₁ s₁ hW₁ hL₁
      exact endBodyZ_sim G S c hc O passes R hRR n k ss fn ft ns nextB rest ys hU hV
        hmem (bindFrischL_sonst (by cases st <;> first | rfl | cases hleaf) hF) hnext hys σ₁ ρ₁ s₁ hW₁ hL₁

    | @binding st ss b ft' ns' ys tail hl hs hys =>
      cases st
      case bind x d v =>
        obtain ⟨e, he, rfl, rfl, rfl⟩ := schrittB_bind hs
        obtain ⟨ls, nextB, hv, hnext, rfl⟩ := lowEnd_bind_ok hG
        intro σ ρ s hW hL
        obtain ⟨bv, hstep, hWl, hL'⟩ := lowBind_named_sim (x := x) hv
          ((namedSide_sicht hV ns v).symm.trans he) hU S.tab hU.valid σ ρ s hW hL
        apply endZiel_bind_G (fun ρB _ => hstep ρB) (fun _ _ h => h.tail) ?_ rfl
        exact endBodyZ_sim G S c hc O passes R hRR n k ss (fn.mitBindung x ls.range)
          (ft.mitBindung x (0, 0)) (ns.push x) nextB rest ys (hU.bind hF.1 ls.range)
          (hV.bind x (0, 0) ls.range) hmem hF.2 hnext hys _ _ _ hWl hL'
      case bindMut x lo hi v =>
        obtain ⟨e, he, rfl, rfl, rfl⟩ := schrittB_bindMut hs
        obtain ⟨ev, nextB, hv, hnext, rfl⟩ := lowEnd_bindMut_ok hG
        intro σ ρ s hW hL
        obtain ⟨bv, hstep, hWl, hL'⟩ := lowBindMut_named_sim (x := x) hv
          ((namedSide_sicht hV ns v).symm.trans he) hU S.tab hU.valid σ ρ s hW hL
        apply endZiel_bind_G (fun ρB _ => hstep ρB) (fun _ _ h => h.tail) ?_ rfl
        exact endBodyZ_sim G S c hc O passes R hRR n k ss (fn.mitBindung x (lo, hi))
          (ft.mitBindung x (lo, hi)) (ns.push x) nextB rest ys (hU.bind hF.1 (lo, hi))
          (hV.bind x (lo, hi) (lo, hi)) hmem hF.2 hnext hys _ _ _ hWl hL'
      case bindB x v =>
        obtain ⟨e, he, rfl, rfl, rfl⟩ := schrittB_bindB hs
        obtain ⟨ev, nextB, hv, hnext, rfl⟩ := lowEnd_bindB_ok hG
        intro σ ρ s hW hL
        obtain ⟨bv, hstep, hWl, hL'⟩ := lowBindB_named_sim (x := x) hv
          ((condZ_sicht hV ns v).symm.trans he) hU S.tab σ ρ s hW hL
        apply endZiel_bind_G (fun ρB _ => hstep ρB) (fun _ _ h => h.tailB) ?_ rfl
        exact endBodyZ_sim G S c hc O passes R hRR n k ss (fn.mitBindungB x)
          (ft.mitBindungB x) (ns.push x) nextB rest ys (hU.bindB hF.1)
          (hV.bindB x) hmem hF.2 hnext hys _ _ _ hWl hL'
      all_goals cases hl
    | @record x d v ss id fs e ys tail ht he hys =>
      obtain ⟨ev, nextB, hv, hnext, rfl⟩ := lowEnd_bindRecord_ok
        ((recordBinderType_sicht hV d v).symm.trans ht) hG
      intro σ ρ s hW hL
      obtain ⟨bv, hstep, hWl, hL'⟩ := lowBindRecord_named_sim (x := x) hv
        ((namedSide_sicht hV ns v).symm.trans he) hU S.tab σ ρ s hW hL
      apply endZiel_bind_G (fun ρB _ => hstep ρB) (fun _ _ h => h.tailRecord) ?_ rfl
      exact endBodyZ_sim G S c hc O passes R hRR n k ss (fn.mitWert x (.prod id fs))
        (ft.mitWert x (.prod id fs)) (ns.push x) nextB rest ys (hU.bindRecord hF.1 id fs)
        (hV.bindRecord x id fs) hmem
        (by simpa only [UFn.mitWert, uArtVon, protectedNames] using hF.2) hnext hys _ _ _ hWl hL'

end Gabbro.Bruecke
