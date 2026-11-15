module
public import Bruecke.Anweisung.Schleife.Kopf
public import Bruecke.Kette.Schritt
public import Gabbro.Body.Finite
@[expose] public section
namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg} {C : Fin u.fns.length → Prop}

/-- Combine sampled-call histories while presenting the running prefix as one loop.
    The execution equation is required under every environment faithful to that prefix. -/
theorem ausgangZiel_nach_lauf {c : Fin u.fns.length} {l : Bool} {Γ : Ctx}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {fn : UFn} {ids : List String} {out : Ausgang (verOf u c) l Γ}
    {A : List Eintrag} {s s₁ : Gabbro.Body.State} {xs ys zs : List Gabbro.Body.Stmt}
    (hp : Strecke_G u C A s s₁ xs) (h : AusgangZiel_G u C c R fn ids out s₁ ys)
    (he : ∀ ρB, Treu A ρB → RahmenAlleC u C ρB →
      Gabbro.Body.exec ρB zs s = Gabbro.Body.exec ρB ys s₁) :
    AusgangZiel_G u C c R fn ids out s zs := by
  refine ⟨h.1, ?_, ?_, ?_, ?_⟩
  · intro σ v hv
    obtain ⟨B, hr⟩ := h.2.1 σ v hv
    obtain ⟨hg, ho, hk, _⟩ := RueckZ_G.nach hp hr
    refine ⟨A ++ B, hg, ho, hk, fun ρB hT hF => ?_⟩
    rw [he ρB (fun e hm => hT e (List.mem_append_left _ hm)) hF]
    exact hr.2.2.2 ρB (fun e hm => hT e (List.mem_append_right _ hm)) hF
  · intro σ ρ hv
    obtain ⟨B, t, ht, hw, hl⟩ := h.2.2.1 σ ρ hv
    have hh := hp.append ht
    refine ⟨A ++ B, t, { hh with lauf := fun ρB hT hF => ?_ }, hw, hl⟩
    rw [he ρB (fun e hm => hT e (List.mem_append_left _ hm)) hF]
    exact ht.lauf ρB (fun e hm => hT e (List.mem_append_right _ hm)) hF
  · intro leave hloop σ ρ hv
    obtain ⟨B, t, ht, hw, hl⟩ := h.2.2.2.1 leave hloop σ ρ hv
    have hh := hp.append ht
    refine ⟨A ++ B, t, { hh with lauf := fun ρB hT hF => ?_ }, hw, hl⟩
    rw [he ρB (fun e hm => hT e (List.mem_append_left _ hm)) hF]
    exact ht.lauf ρB (fun e hm => hT e (List.mem_append_right _ hm)) hF
  · intro σ r hv
    obtain ⟨B, hr⟩ := h.2.2.2.2 σ r hv
    obtain ⟨hg, ho, hk, _⟩ := RueckZ_G.nach hp hr
    refine ⟨A ++ B, hg, ho, hk, fun ρB hT hF => ?_⟩
    rw [he ρB (fun e hm => hT e (List.mem_append_left _ hm)) hF]
    exact hr.2.2.2 ρB (fun e hm => hT e (List.mem_append_right _ hm)) hF

/-- The generic finite pass simulation consumes exactly the canonical `leave`/`next`
    outcomes. It also preserves sampled calls and early returns from arbitrary bodies. -/
theorem finiteBody_sim {loopMode : Bool} {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {ns : BodyNames} {x : String}
    {t : Fin u.tabs.length}
    (body : Block (declOf u) (verOf u c) true (.index ((declOf u).count t) :: Γ) Λ Λ)
    (bs : List Gabbro.Body.Stmt) (hU : UmfangB Γ fn ns)
    (hBody : ∀ σ ρ s, WGRel u σ s.world →
      PositionalLRel (fn.mitIndex x t.val ((declOf u).count t)) (ns.push x).active 0 ρ s.local' →
      BlockZiel_G u C c O passes R (fn.mitIndex x t.val ((declOf u).count t))
        (ns.push x).active body σ ρ s bs) :
    ∀ (indices : List (Wert (declOf u) (.index ((declOf u).count t)))) σ ρ s,
      WGRel u σ s.world → PositionalLRel fn ns.active 0 ρ s.local' →
      AusgangZiel_G u C c R fn ns.active
        (traverseLauf (l := loopMode) (fun σ ρ => execBlock O passes R body σ ρ)
          (fun σ _ => (σ, true)) indices σ ρ) s
        [.forEach (ns.fresh x) (indices.map (·.n)) bs]
  | [], σ, ρ, s, hW, hL => by
    refine ⟨fun e he => ?_, fun σ' v he => ?_, fun σ' ρ' he => ?_, ?_, fun σ' r he => (by simp only [traverseLauf, ↓reduceIte] at he; cases he)⟩
    · simp only [traverseLauf, ↓reduceIte] at he; cases he
    · simp only [traverseLauf, ↓reduceIte] at he; cases he
    · simp only [traverseLauf, ↓reduceIte] at he
      cases he
      exact ⟨[], s, Strecke_G.schritt (fun _ _ => rfl) (fun _ => Int.le_refl _), hW, hL⟩
    · intro leave hloop σ' ρ' he
      cases leave <;> simp only [traverseLauf, ↓reduceIte, controlG] at he <;> cases he
  | i :: indices, σ, ρ, s, hW, hL => by
    let entry : Gabbro.Body.State :=
      ⟨s.world, Gabbro.Body.bindLocal s.local' (ns.fresh x) (.int i.n)⟩
    have hPass := hBody σ (.cons i ρ) entry hW
      (hL.pushIndex x hU.valid t.val ((declOf u).count t) i)
    cases hex : execBlock O passes R body σ (.cons i ρ) with
    | ok σ₁ ρ₁ =>
      obtain ⟨A, s₁, hp, hw, hl⟩ := hPass.2.2.1 σ₁ ρ₁ hex
        have first : Strecke_G u C A s s₁ [.forEach (ns.fresh x) [i.n] bs] := by
          refine { gut := hp.gut, oben := hp.oben, unten := hp.unten, schluessel := hp.schluessel, mono := hp.mono, lauf := ?_ }
          intro ρB hT hF
          rw [Gabbro.Body.exec_singleton,
            Gabbro.Body.forEach_cons_running ρB (ns.fresh x) i.n [] bs s s₁ (hp.lauf ρB hT hF)]
          rfl
      have ih := finiteBody_sim body bs hU hBody indices σ₁ ρ₁.tail s₁ hw hl.tailIndex
      have hh := ausgangZiel_nach_lauf first ih
        (zs := [.forEach (ns.fresh x) ((i :: indices).map (·.n)) bs])
        (fun ρB hT hF => by
          rw [Gabbro.Body.exec_singleton, Gabbro.Body.exec_singleton, List.map_cons,
            Gabbro.Body.forEach_cons_running ρB (ns.fresh x) i.n (indices.map (·.n)) bs s s₁ (hp.lauf ρB hT hF)])
      simpa only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex] using hh
    | next hloop σ₁ ρ₁ =>
      obtain ⟨A, s₁, hp, hw, hl⟩ := hPass.2.2.2.1 false hloop σ₁ ρ₁ hex
        have first : Strecke_G u C A s s₁ [.forEach (ns.fresh x) [i.n] bs] := by
          refine { gut := hp.gut, oben := hp.oben, unten := hp.unten, schluessel := hp.schluessel, mono := hp.mono, lauf := ?_ }
          intro ρB hT hF
          rw [Gabbro.Body.exec_singleton,
            Gabbro.Body.forEach_cons_next ρB (ns.fresh x) i.n [] bs s s₁ (hp.lauf ρB hT hF)]
          rfl
      have ih := finiteBody_sim body bs hU hBody indices σ₁ ρ₁.tail s₁ hw hl.tailIndex
      have hh := ausgangZiel_nach_lauf first ih
        (zs := [.forEach (ns.fresh x) ((i :: indices).map (·.n)) bs])
        (fun ρB hT hF => by
          rw [Gabbro.Body.exec_singleton, Gabbro.Body.exec_singleton, List.map_cons,
            Gabbro.Body.forEach_cons_next ρB (ns.fresh x) i.n (indices.map (·.n)) bs s s₁ (hp.lauf ρB hT hF)])
      simpa only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex] using hh
    | leave hloop σ₁ ρ₁ =>
      obtain ⟨A, s₁, hp, hw, hl⟩ := hPass.2.2.2.1 true hloop σ₁ ρ₁ hex
        have trace : Strecke_G u C A s s₁ [.forEach (ns.fresh x) ((i :: indices).map (·.n)) bs] := by
          refine { gut := hp.gut, oben := hp.oben, unten := hp.unten, schluessel := hp.schluessel, mono := hp.mono, lauf := ?_ }
          intro ρB hT hF
          rw [Gabbro.Body.exec_singleton, List.map_cons,
            Gabbro.Body.forEach_cons_leave ρB (ns.fresh x) i.n (indices.map (·.n)) bs s s₁ (hp.lauf ρB hT hF)]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro e he
        simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex] at he; cases he
      · intro σ' v he
        simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex] at he; cases he
      · intro σ' ρ' he
        simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex] at he
        cases he
        exact ⟨A, s₁, trace, hw, hl.tailIndex⟩
      · intro leave hloop σ' ρ' he
        cases leave <;> simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex, controlG] at he <;> cases he
      · intro σ' r' he
        simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex] at he; cases he
    | zurueck σ₁ v =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro e he
        simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex] at he; cases he
      · intro σ' v' he
        simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex] at he
        cases he
        obtain ⟨A, hg, ho, hk, hr⟩ := hPass.2.1 σ₁ v hex
        refine ⟨A, hg, ho, hk, fun ρB hT hF => ?_⟩
        obtain ⟨s', hb, hw⟩ := hr ρB hT hF
        refine ⟨s', ?_, hw⟩
        rw [Gabbro.Body.exec_singleton, List.map_cons,
          Gabbro.Body.forEach_cons_returned ρB (ns.fresh x) i.n (indices.map (·.n)) bs s s' _ hb]
      · intro σ' ρ' he
        simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex] at he; cases he
      · intro leave hloop σ' ρ' he
        cases leave <;> simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex, controlG] at he <;> cases he
      · intro σ' r' he
        simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex] at he; cases he
    | logik err =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro e he
        simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex] at he
        cases he
        exact hPass.1 err hex
      · intro σ' v he
        simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex] at he; cases he
      · intro σ' ρ' he
        simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex] at he; cases he
      · intro leave hloop σ' ρ' he
        cases leave <;> simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex, controlG] at he <;> cases he
      · intro σ' r' he
        simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex] at he; cases he
    | why σ₁ r =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro e he
        simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex] at he; cases he
      · intro σ' v he
        simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex] at he; cases he
      · intro σ' ρ' he
        simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex] at he; cases he
      · intro leave hloop σ' ρ' he
        cases leave <;> simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex, controlG] at he <;> cases he
      · intro σ' r' he
        simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex] at he
        cases he
        obtain ⟨A, hg, ho, hk, hr⟩ := hPass.2.2.2.2 σ₁ r hex
        refine ⟨A, hg, ho, hk, fun ρB hT hF => ?_⟩
        obtain ⟨s', hb, hw⟩ := hr ρB hT hF
        refine ⟨s', ?_, hw⟩
        rw [Gabbro.Body.exec_singleton, List.map_cons,
          Gabbro.Body.forEach_cons_returned ρB (ns.fresh x) i.n (indices.map (·.n)) bs s s' _ hb]
    | hardware err =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro e he
        simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex] at he; cases he
      · intro σ' v he
        simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex] at he; cases he
      · intro σ' ρ' he
        simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex] at he; cases he
      · intro leave hloop σ' ρ' he
        cases leave <;> simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex, controlG] at he <;> cases he
      · intro σ' r' he
        simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hex] at he; cases he

/-- The source traversal reuses the full recursive block claim for each actual index. -/
theorem stmtZiel_loop_G {loopMode : Bool} {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {ns : BodyNames} {x : String}
    {t : Fin u.tabs.length}
    {body : Block (declOf u) (verOf u c) true (.index ((declOf u).count t) :: Γ) Λ Λ}
    {bs : List Gabbro.Body.Stmt} (hU : UmfangB Γ fn ns)
    (hBody : ∀ σ ρ s, WGRel u σ s.world →
      PositionalLRel (fn.mitIndex x t.val ((declOf u).count t)) (ns.push x).active 0 ρ s.local' →
      BlockZiel_G u C c O passes R (fn.mitIndex x t.val ((declOf u).count t))
        (ns.push x).active body σ ρ s bs)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    StmtZiel_G u C c O passes R fn ns.active (.traverse (l := loopMode) t Expr.tru body) σ ρ s
      (.forEach (ns.fresh x) (loopIndices u t) bs) := by
  simpa only [StmtZiel_G, execStmt, Expr.orte, lese_nil, eval, wahr?, loopIndices] using
    finiteBody_sim (loopMode := loopMode) body bs hU hBody (alleIndizes ((declOf u).count t)) σ ρ s hW hL

end Gabbro.Bruecke
