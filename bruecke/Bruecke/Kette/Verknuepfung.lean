module
public import Bruecke.Kette.Strecke
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

variable {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
  {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}

theorem blockZiel_nil_G {Γ : Ctx} {Λ : List (Res (declOf u))} (fn : UFn) (σ : World (declOf u))
    (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State) (hW : WRel u σ s.world)
    (hL : LRel fn 0 ρ s.local') :
    BlockZiel_G u C c O passes R fn (Block.nil : Block (declOf u) (verOf u c) false Γ Λ Λ) σ ρ s [] := by
  refine ⟨fun e h => ?_, fun σ' v h => ?_, fun σ' ρ' h => ?_⟩
  · rw [execBlockZ_nil] at h; cases h
  · rw [execBlockZ_nil] at h; cases h
  · rw [execBlockZ_nil] at h
    cases h
    exact ⟨[], s, Strecke_G.leer s, hW, hL⟩

theorem stmtZiel_of_G {Γ : Ctx} {Λ Λ₁ : List (Res (declOf u))} {fn : UFn}
    {st : Stmt (declOf u) (verOf u c) false Γ Λ Λ₁} {blk : Block (declOf u) (verOf u c) false Γ Λ Λ₁}
    {σ σl : World (declOf u)} {ρ : Env (declOf u) Γ} {s : Gabbro.Body.State}
    {x : Gabbro.Body.Stmt} {tB : List Gabbro.Body.Stmt}
    (hG : execStmt O passes R st σ ρ = execBlock O passes R blk σl ρ)
    (hB : ∀ ρB, Gabbro.Body.step ρB x s = Gabbro.Body.exec ρB tB s)
    (h : BlockZiel_G u C c O passes R fn blk σl ρ s tB) : StmtZiel_G u C c O passes R fn st σ ρ s x := by
  refine ⟨fun e he => h.1 e (hG.symm.trans he), fun σ' v he => ?_, fun σ' ρ' he => ?_⟩
  · obtain ⟨A, hg, ho, hk, hb⟩ := h.2.1 σ' v (hG.symm.trans he)
    refine ⟨A, hg, ho, hk, fun ρB hT hF => ?_⟩
    obtain ⟨s', e1, e2⟩ := hb ρB hT hF
    refine ⟨s', ?_, e2⟩
    simp only [Gabbro.Body.exec, hB ρB, e1]
  · obtain ⟨A, s', hS, hW, hL⟩ := h.2.2 σ' ρ' (hG.symm.trans he)
    refine ⟨A, s', { hS with lauf := fun ρB hT hF => ?_ }, hW, hL⟩
    simp only [Gabbro.Body.exec, hB ρB, hS.lauf ρB hT hF]

theorem blockZiel_cons_G {Γ : Ctx} {Λ Λ₁ Λ' : List (Res (declOf u))} {fn : UFn}
    {st : Stmt (declOf u) (verOf u c) false Γ Λ Λ₁}
    {rest : Block (declOf u) (verOf u c) false Γ Λ₁ Λ'} {σ : World (declOf u)}
    {ρ : Env (declOf u) Γ} {s : Gabbro.Body.State} {x : Gabbro.Body.Stmt}
    {ys : List Gabbro.Body.Stmt} (hst : StmtZiel_G u C c O passes R fn st σ ρ s x)
    (hrest : ∀ σ₁ ρ₁ s₁, WRel u σ₁ s₁.world → LRel fn 0 ρ₁ s₁.local' →
      BlockZiel_G u C c O passes R fn rest σ₁ ρ₁ s₁ ys) :
    BlockZiel_G u C c O passes R fn (Block.cons st rest) σ ρ s (x :: ys) := by
  cases hx : execStmt O passes R st σ ρ with
  | ok σ₁ ρ₁ =>
    obtain ⟨A₁, s₁, hS, hW, hL⟩ := hst.2.2 σ₁ ρ₁ hx
    have hw := execBlockZ_cons_ok O passes R st rest hx
    have hr := hrest σ₁ ρ₁ s₁ hW hL
    refine ⟨fun e h => hr.1 e (hw.symm.trans h), fun σ' v h => ?_, fun σ' ρ' h => ?_⟩
    · obtain ⟨A₂, hR⟩ := hr.2.1 σ' v (hw.symm.trans h)
      refine ⟨A₁ ++ A₂, ?_⟩
      rw [← List.singleton_append]
      exact RueckZ_G.nach hS hR
    · obtain ⟨A₂, s₂, hS₂, hW₂, hL₂⟩ := hr.2.2 σ' ρ' (hw.symm.trans h)
      exact ⟨A₁ ++ A₂, s₂, Strecke_G.cons hS hS₂, hW₂, hL₂⟩
  | zurueck σ' v =>
    have hw := execBlockZ_cons_zurueck O passes R st rest (ρ := ρ) hx
    refine ⟨fun e h => (by rw [hw] at h; cases h), fun σ'' v' h => ?_, fun σ'' ρ'' h => (by
      rw [hw] at h; cases h)⟩
    rw [hw] at h
    cases h
    obtain ⟨A, hR⟩ := hst.2.1 σ' v hx
    refine ⟨A, ?_⟩
    rw [← List.singleton_append]
    exact RueckZ_G.append hR ys
  | logik e =>
    have hw := execBlockZ_cons_logik O passes R st rest (ρ := ρ) hx
    refine ⟨fun e' h => ?_, fun σ'' v' h => (by rw [hw] at h; cases h), fun σ'' ρ'' h => (by
      rw [hw] at h; cases h)⟩
    rw [hw] at h
    cases h
    exact hst.1 e hx
  | why σ' r =>
    have hw := execBlockZ_cons_still O passes R st rest (σ := σ) (ρ := ρ)
      (fun _ _ h => by rw [hx] at h; cases h)
    rw [hx] at hw
    exact ⟨fun e h => (by rw [hw] at h; cases h), fun σ'' v' h => (by rw [hw] at h; cases h),
      fun σ'' ρ'' h => (by rw [hw] at h; cases h)⟩
  | leave hl σ' ρ' =>
    have hw := execBlockZ_cons_still O passes R st rest (σ := σ) (ρ := ρ)
      (fun _ _ h => by rw [hx] at h; cases h)
    rw [hx] at hw
    exact ⟨fun e h => (by rw [hw] at h; cases h), fun σ'' v' h => (by rw [hw] at h; cases h),
      fun σ'' ρ'' h => (by rw [hw] at h; cases h)⟩
  | next hl σ' ρ' =>
    have hw := execBlockZ_cons_still O passes R st rest (σ := σ) (ρ := ρ)
      (fun _ _ h => by rw [hx] at h; cases h)
    rw [hx] at hw
    exact ⟨fun e h => (by rw [hw] at h; cases h), fun σ'' v' h => (by rw [hw] at h; cases h),
      fun σ'' ρ'' h => (by rw [hw] at h; cases h)⟩
  | hardware e =>
    have hw := execBlockZ_cons_still O passes R st rest (σ := σ) (ρ := ρ)
      (fun _ _ h => by rw [hx] at h; cases h)
    rw [hx] at hw
    exact ⟨fun e h => (by rw [hw] at h; cases h), fun σ'' v' h => (by rw [hw] at h; cases h),
      fun σ'' ρ'' h => (by rw [hw] at h; cases h)⟩

theorem blockZiel_bind_G {Γ : Ctx} {Λ Λ' : List (Res (declOf u))} {fn : UFn} {τ : Ty}
    {e : Expr (declOf u) Γ Λ τ} {rest : Block (declOf u) (verOf u c) false (τ :: Γ) Λ Λ'}
    {σ : World (declOf u)} {ρ : Env (declOf u) Γ} {s s₁ : Gabbro.Body.State}
    {x : Gabbro.Body.Stmt} {ys : List Gabbro.Body.Stmt} {y : String} {w : Int × Int}
    (hy : y ∉ fn.params.map (·.1))
    (hstep : ∀ ρB, RahmenAlleC u C ρB → Gabbro.Body.step ρB x s = .running s₁)
    (hgz : ∀ w', gz w' s.world ≤ gz w' s₁.world)
    (h : BlockZiel_G u C c O passes R (fn.mitBindung y w) rest (σ.lese Λ e.orte)
      (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) s₁ ys) :
    BlockZiel_G u C c O passes R fn (Block.bind e rest) σ ρ s (x :: ys) := by
  refine ⟨fun err he => ?_, fun σ' v he => ?_, fun σ' ρ' he => ?_⟩
  · rw [execBlockZ_bind] at he
    exact h.1 err (schrumpfZ_logik he)
  · rw [execBlockZ_bind] at he
    obtain ⟨A, hR⟩ := h.2.1 σ' v (schrumpfZ_zurueck he)
    exact ⟨A, RueckZ_G.vor hstep hgz hR⟩
  · rw [execBlockZ_bind] at he
    obtain ⟨ρ'', hin, rfl⟩ := schrumpfZ_ok he
    obtain ⟨A, s', hS, hW, hL⟩ := h.2.2 σ' ρ'' hin
    exact ⟨A, s', Strecke_G.vor hstep hgz hS, hW, lrel_tail hL hy⟩

theorem laufZiel_strecke_G {Γ Γ₁ : Ctx} {Λ Λ₁ : List (Res (declOf u))}
    {b0 : Endblock (declOf u) (verOf u c) false Γ Λ}
    {b1 : Endblock (declOf u) (verOf u c) false Γ₁ Λ₁}
    {σ σ₁ : World (declOf u)} {ρ : Env (declOf u) Γ} {ρ₁ : Env (declOf u) Γ₁}
    {s s₁ : Gabbro.Body.State} {A : List Eintrag} {xs bs : List Gabbro.Body.Stmt}
    (hrun : (∀ e, execEnd O passes R b0 σ ρ = .logik e → execEnd O passes R b1 σ₁ ρ₁ = .logik e) ∧
      (∀ σ' v, execEnd O passes R b0 σ ρ = .zurueck σ' v →
        execEnd O passes R b1 σ₁ ρ₁ = .zurueck σ' v))
    (hS : Strecke_G u C A s s₁ xs) (ih : LaufZielTeilB u C c O passes R b1 σ₁ ρ₁ s₁ bs) :
    LaufZielTeilB u C c O passes R b0 σ ρ s (xs ++ bs) := by
  refine ⟨fun e h => ih.1 e (hrun.1 e h), fun σ' v h => ?_⟩
  obtain ⟨A₂, hg, ho, hk, hb⟩ := ih.2 σ' v (hrun.2 σ' v h)
  refine ⟨A ++ A₂, fun e he => (List.mem_append.mp he).elim (hS.gut e) (hg e),
    fun e he => (List.mem_append.mp he).elim (hS.oben e) (fun h' => oben_mono hS.mono ho e h'),
    schluessel_append hS.schluessel hS.unten hk ho, fun ρB hT hF => ?_⟩
  obtain ⟨s', h1, h2, h3⟩ := hb ρB (fun e he => hT e (List.mem_append_right _ he)) hF
  have hx := hS.lauf ρB (fun e he => hT e (List.mem_append_left _ he)) hF
  have hexec : Gabbro.Body.exec ρB (xs ++ bs) s = Gabbro.Body.exec ρB bs s₁ := by
    simp only [exec_append, hx]
  exact ⟨s', by rw [hexec]; exact h1, by rw [hexec]; exact h2, h3⟩

theorem laufZiel_rueck_G {Γ : Ctx} {Λ : List (Res (declOf u))}
    {b0 : Endblock (declOf u) (verOf u c) false Γ Λ} {σ σ' : World (declOf u)}
    {ρ : Env (declOf u) Γ} {s : Gabbro.Body.State} {bs : List Gabbro.Body.Stmt}
    {A : List Eintrag} {v : ErgVal (declOf u) (verOf u c).erg}
    (h : execEnd O passes R b0 σ ρ = .zurueck σ' v)
    (hR : RueckZ_G u C A s bs σ' (ergValOf (verOf u c).erg v)) :
    LaufZielTeilB u C c O passes R b0 σ ρ s bs := by
  refine ⟨fun e h' => (by rw [h] at h'; cases h'), fun σ'' v' h' => ?_⟩
  rw [h] at h'
  cases h'
  obtain ⟨hg, ho, hk, hb⟩ := hR
  refine ⟨A, hg, ho, hk, fun ρB hT hF => ?_⟩
  obtain ⟨s', h1, h2⟩ := hb ρB hT hF
  exact ⟨s', by simp only [h1, Gabbro.Body.finalState], by rw [h1, finalValue_returned], h2⟩

theorem laufZiel_logik_G {Γ : Ctx} {Λ : List (Res (declOf u))}
    {b0 : Endblock (declOf u) (verOf u c) false Γ Λ} {σ : World (declOf u)}
    {ρ : Env (declOf u) Γ} {s : Gabbro.Body.State} {bs : List Gabbro.Body.Stmt} {e : Logik (declOf u)}
    (h : execEnd O passes R b0 σ ρ = .logik e)
    (hb : ∃ (g : (declOf u).Fn) (σr : World (declOf u)) (envA : Env (declOf u) ((declOf u).params g)),
      C g ∧ R g σr envA = .logik e) :
    LaufZielTeilB u C c O passes R b0 σ ρ s bs :=
  ⟨fun e' h' => (by rw [h] at h'; cases h'; exact hb), fun σ' v h' => (by rw [h] at h'; cases h')⟩

theorem laufZiel_cons_G {Γ : Ctx} {Λ Λ₁ : List (Res (declOf u))} {fn : UFn}
    {st : Stmt (declOf u) (verOf u c) false Γ Λ Λ₁}
    {rest : Endblock (declOf u) (verOf u c) false Γ Λ₁} {σ : World (declOf u)}
    {ρ : Env (declOf u) Γ} {s : Gabbro.Body.State} {x : Gabbro.Body.Stmt}
    {bs : List Gabbro.Body.Stmt} (hst : StmtZiel_G u C c O passes R fn st σ ρ s x)
    (hrest : ∀ σ₁ ρ₁ s₁, WRel u σ₁ s₁.world → LRel fn 0 ρ₁ s₁.local' →
      LaufZielTeilB u C c O passes R rest σ₁ ρ₁ s₁ bs) :
    LaufZielTeilB u C c O passes R (Endblock.cons st rest) σ ρ s (x :: bs) := by
  cases hx : execStmt O passes R st σ ρ with
  | ok σ₁ ρ₁ =>
    obtain ⟨A, s₁, hS, hW, hL⟩ := hst.2.2 σ₁ ρ₁ hx
    have := laufZiel_strecke_G (cons_lauf O passes R st rest σ σ₁ ρ ρ₁ hx) hS (hrest σ₁ ρ₁ s₁ hW hL)
    rw [List.singleton_append] at this
    exact this
  | zurueck σ' v =>
    have hw : execEnd O passes R (Endblock.cons st rest) σ ρ = .zurueck σ' v := by
      simp only [execEnd, hx]
    obtain ⟨A, hR⟩ := hst.2.1 σ' v hx
    have hR' := RueckZ_G.append hR bs
    rw [List.singleton_append] at hR'
    exact laufZiel_rueck_G hw hR'
  | logik e =>
    have hw : execEnd O passes R (Endblock.cons st rest) σ ρ = .logik e := by
      simp only [execEnd, hx]
    exact laufZiel_logik_G hw (hst.1 e hx)
  | why σ' r =>
    have hw : execEnd O passes R (Endblock.cons st rest) σ ρ = .why σ' r := by
      simp only [execEnd, hx]
    exact ⟨fun e h => (by rw [hw] at h; cases h), fun σ'' v h => (by rw [hw] at h; cases h)⟩
  | leave hl σ' ρ' =>
    have hw : execEnd O passes R (Endblock.cons st rest) σ ρ = .leave hl σ' ρ' := by
      simp only [execEnd, hx]
    exact ⟨fun e h => (by rw [hw] at h; cases h), fun σ'' v h => (by rw [hw] at h; cases h)⟩
  | next hl σ' ρ' =>
    have hw : execEnd O passes R (Endblock.cons st rest) σ ρ = .next hl σ' ρ' := by
      simp only [execEnd, hx]
    exact ⟨fun e h => (by rw [hw] at h; cases h), fun σ'' v h => (by rw [hw] at h; cases h)⟩
  | hardware e =>
    have hw : execEnd O passes R (Endblock.cons st rest) σ ρ = .hardware e := by
      simp only [execEnd, hx]
    exact ⟨fun e h => (by rw [hw] at h; cases h), fun σ'' v h => (by rw [hw] at h; cases h)⟩

end Gabbro.Bruecke
