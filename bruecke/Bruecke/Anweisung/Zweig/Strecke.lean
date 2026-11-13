module
public import Bruecke.Anweisung.Zweig.Kopf
@[expose] public section

/-!
# C6, part 3: stretches of a Body run, and how they compose

A branch of a conditional ends in one of three ways the bridge speaks about: it falls through
(the run goes on after the `blkEnd`), it returns, or a callee blames the caller's logic. A
**stretch** (`Strecke`) is the first: an answer table under which the Body statements run from
one state to another, with every entry's ghost below the end state (`Unten`), so that stretches
compose (`Strecke.append`) and a stretch composes with the run's conclusion after it
(`laufZiel_strecke`). `RueckZ` is the second. `StmtZiel`/`BlockZiel` collect the three for one
lowered statement or block against its Body translation; `laufZiel_cons`, `blockZiel_cons` and
`blockZiel_bind` move them along a body and a block.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-! ## 1. Stretches -/

/-- Every entry is a writer's, at an entry state whose ghost is below the one of `W`. -/
def Unten (u : UProg) (A : List Eintrag) (W : Gabbro.Body.World) : Prop :=
  ∀ e ∈ A, ∃ w, geistVon u e.name = some w ∧ gz w e.ein.world < gz w W

/-- **A stretch**: under every environment that follows the table `A` and respects the frames,
    the statements `bs` run from `s` to `s'`. -/
structure Strecke (u : UProg) (A : List Eintrag) (s s' : Gabbro.Body.State)
    (bs : List Gabbro.Body.Stmt) : Prop where
  gut : ∀ e ∈ A, EintragGut u e
  oben : Oben u A s.world
  unten : Unten u A s'.world
  schluessel : Schluessel A
  mono : ∀ w, gz w s.world ≤ gz w s'.world
  lauf : ∀ ρB, Treu A ρB → RahmenAlle u ρB → Gabbro.Body.exec ρB bs s = .running s'

/-- **A return**: under every such environment the statements `bs` return from `s` with the
    answer `v`, in a state related to `σ'`. -/
abbrev RueckZ (u : UProg) (A : List Eintrag) (s : Gabbro.Body.State) (bs : List Gabbro.Body.Stmt)
    (σ' : World (declOf u)) (v : Option Gabbro.Body.Value) : Prop :=
  (∀ e ∈ A, EintragGut u e) ∧ Oben u A s.world ∧ Schluessel A ∧
    ∀ ρB, Treu A ρB → RahmenAlle u ρB →
      ∃ s', Gabbro.Body.exec ρB bs s = .returned s' v ∧ WRel u σ' s'.world

theorem exec_append (ρB : Gabbro.Body.Env) : ∀ (xs ys : List Gabbro.Body.Stmt)
    (s : Gabbro.Body.State),
    Gabbro.Body.exec ρB (xs ++ ys) s =
      match Gabbro.Body.exec ρB xs s with
      | .running s' => Gabbro.Body.exec ρB ys s'
      | o => o
  | [], ys, s => by simp only [List.nil_append, Gabbro.Body.exec]
  | x :: xs, ys, s => by
      simp only [List.cons_append, Gabbro.Body.exec]
      cases Gabbro.Body.step ρB x s with
      | running s1 => exact exec_append ρB xs ys s1
      | returned s1 v => rfl
      | exited s1 => rfl
      | left s1 => rfl
      | stuck => rfl

theorem schluessel_append {A₁ A₂ : List Eintrag} {W : Gabbro.Body.World} (h₁ : Schluessel A₁)
    (hu : Unten u A₁ W) (h₂ : Schluessel A₂) (ho : Oben u A₂ W) : Schluessel (A₁ ++ A₂) := by
  refine List.pairwise_append.mpr ⟨h₁, h₂, fun a ha b hb hab => ?_⟩
  obtain ⟨w, hw, hlt⟩ := hu a ha
  obtain ⟨w', hw', hle⟩ := ho b hb
  rw [hab.1, hw'] at hw
  cases hw
  rw [hab.2] at hlt
  omega

theorem Strecke.leer (s : Gabbro.Body.State) : Strecke u [] s s [] :=
  { gut := fun _ h => absurd h List.not_mem_nil
    oben := fun _ h => absurd h List.not_mem_nil
    unten := fun _ h => absurd h List.not_mem_nil
    schluessel := List.Pairwise.nil
    mono := fun _ => Int.le_refl _
    lauf := fun _ _ _ => rfl }

theorem Strecke.schritt {s s₁ : Gabbro.Body.State} {x : Gabbro.Body.Stmt}
    (hstep : ∀ ρB, RahmenAlle u ρB → Gabbro.Body.step ρB x s = .running s₁)
    (hgz : ∀ w, gz w s.world ≤ gz w s₁.world) : Strecke u [] s s₁ [x] :=
  { gut := fun _ h => absurd h List.not_mem_nil
    oben := fun _ h => absurd h List.not_mem_nil
    unten := fun _ h => absurd h List.not_mem_nil
    schluessel := List.Pairwise.nil
    mono := hgz
    lauf := fun ρB _ hF => by simp only [Gabbro.Body.exec, hstep ρB hF] }

theorem Strecke.append {A₁ A₂ : List Eintrag} {s s₁ s₂ : Gabbro.Body.State}
    {xs ys : List Gabbro.Body.Stmt} (h₁ : Strecke u A₁ s s₁ xs) (h₂ : Strecke u A₂ s₁ s₂ ys) :
    Strecke u (A₁ ++ A₂) s s₂ (xs ++ ys) :=
  { gut := fun e he => (List.mem_append.mp he).elim (h₁.gut e) (h₂.gut e)
    oben := fun e he => (List.mem_append.mp he).elim (h₁.oben e)
      (fun h => oben_mono h₁.mono h₂.oben e h)
    unten := fun e he => (List.mem_append.mp he).elim
      (fun h => by
        obtain ⟨w, hw, hlt⟩ := h₁.unten e h
        exact ⟨w, hw, Int.lt_of_lt_of_le hlt (h₂.mono w)⟩)
      (h₂.unten e)
    schluessel := schluessel_append h₁.schluessel h₁.unten h₂.schluessel h₂.oben
    mono := fun w => Int.le_trans (h₁.mono w) (h₂.mono w)
    lauf := fun ρB hT hF => by
      rw [exec_append, h₁.lauf ρB (fun e he => hT e (List.mem_append_left _ he)) hF]
      exact h₂.lauf ρB (fun e he => hT e (List.mem_append_right _ he)) hF }

theorem Strecke.cons {A₁ A₂ : List Eintrag} {s s₁ s₂ : Gabbro.Body.State} {x : Gabbro.Body.Stmt}
    {ys : List Gabbro.Body.Stmt} (h₁ : Strecke u A₁ s s₁ [x]) (h₂ : Strecke u A₂ s₁ s₂ ys) :
    Strecke u (A₁ ++ A₂) s s₂ (x :: ys) := by
  rw [← List.singleton_append]
  exact Strecke.append h₁ h₂

/-- A first step that runs, before a stretch. -/
theorem Strecke.vor {A : List Eintrag} {s s₁ s₂ : Gabbro.Body.State} {x : Gabbro.Body.Stmt}
    {ys : List Gabbro.Body.Stmt}
    (hstep : ∀ ρB, RahmenAlle u ρB → Gabbro.Body.step ρB x s = .running s₁)
    (hgz : ∀ w, gz w s.world ≤ gz w s₁.world) (h : Strecke u A s₁ s₂ ys) :
    Strecke u A s s₂ (x :: ys) :=
  { gut := h.gut
    oben := oben_mono hgz h.oben
    unten := h.unten
    schluessel := h.schluessel
    mono := fun w => Int.le_trans (hgz w) (h.mono w)
    lauf := fun ρB hT hF => by
      rw [exec_cons_running ρB x ys s s₁ (hstep ρB hF)]
      exact h.lauf ρB hT hF }

theorem step_ite_wahr (ρB : Gabbro.Body.Env) {ce : Gabbro.Body.Expr}
    {t e : List Gabbro.Body.Stmt} {s : Gabbro.Body.State}
    (hc : Gabbro.Body.eval s ce = some (.bool true)) :
    Gabbro.Body.step ρB (.ite ce t e) s = Gabbro.Body.exec ρB t s := by
  simp only [Gabbro.Body.step, hc]

theorem step_ite_falsch (ρB : Gabbro.Body.Env) {ce : Gabbro.Body.Expr}
    {t e : List Gabbro.Body.Stmt} {s : Gabbro.Body.State}
    (hc : Gabbro.Body.eval s ce = some (.bool false)) :
    Gabbro.Body.step ρB (.ite ce t e) s = Gabbro.Body.exec ρB e s := by
  simp only [Gabbro.Body.step, hc]

theorem step_ite_cases (ρB : Gabbro.Body.Env) (ce : Gabbro.Body.Expr)
    (t e : List Gabbro.Body.Stmt) (s : Gabbro.Body.State) :
    Gabbro.Body.step ρB (.ite ce t e) s = Gabbro.Body.exec ρB t s ∨
      Gabbro.Body.step ρB (.ite ce t e) s = Gabbro.Body.exec ρB e s ∨
      Gabbro.Body.step ρB (.ite ce t e) s = .stuck := by
  simp only [Gabbro.Body.step]
  split
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

/-! ## 2. Returns -/

theorem finalValue_returned (s : Gabbro.Body.State) (v : Option Gabbro.Body.Value) :
    Gabbro.Body.finalValue (.returned s v) = v := by
  cases v <;> rfl

theorem RueckZ.append {A : List Eintrag} {s : Gabbro.Body.State} {xs : List Gabbro.Body.Stmt}
    {σ' : World (declOf u)} {v : Option Gabbro.Body.Value} (h : RueckZ u A s xs σ' v)
    (ys : List Gabbro.Body.Stmt) : RueckZ u A s (xs ++ ys) σ' v := by
  obtain ⟨hg, ho, hk, hb⟩ := h
  refine ⟨hg, ho, hk, fun ρB hT hF => ?_⟩
  obtain ⟨s', h1, h2⟩ := hb ρB hT hF
  refine ⟨s', ?_, h2⟩
  simp only [exec_append, h1]

theorem RueckZ.nach {A₁ A₂ : List Eintrag} {s s₁ : Gabbro.Body.State}
    {xs ys : List Gabbro.Body.Stmt} {σ' : World (declOf u)} {v : Option Gabbro.Body.Value}
    (h₁ : Strecke u A₁ s s₁ xs) (h₂ : RueckZ u A₂ s₁ ys σ' v) :
    RueckZ u (A₁ ++ A₂) s (xs ++ ys) σ' v := by
  obtain ⟨hg, ho, hk, hb⟩ := h₂
  refine ⟨fun e he => (List.mem_append.mp he).elim (h₁.gut e) (hg e),
    fun e he => (List.mem_append.mp he).elim (h₁.oben e) (fun h => oben_mono h₁.mono ho e h),
    schluessel_append h₁.schluessel h₁.unten hk ho, fun ρB hT hF => ?_⟩
  obtain ⟨s', e1, e2⟩ := hb ρB (fun e he => hT e (List.mem_append_right _ he)) hF
  refine ⟨s', ?_, e2⟩
  rw [exec_append, h₁.lauf ρB (fun e he => hT e (List.mem_append_left _ he)) hF]
  exact e1

theorem RueckZ.vor {A : List Eintrag} {s s₁ : Gabbro.Body.State} {x : Gabbro.Body.Stmt}
    {ys : List Gabbro.Body.Stmt} {σ' : World (declOf u)} {v : Option Gabbro.Body.Value}
    (hstep : ∀ ρB, RahmenAlle u ρB → Gabbro.Body.step ρB x s = .running s₁)
    (hgz : ∀ w, gz w s.world ≤ gz w s₁.world) (h : RueckZ u A s₁ ys σ' v) :
    RueckZ u A s (x :: ys) σ' v := by
  obtain ⟨hg, ho, hk, hb⟩ := h
  refine ⟨hg, oben_mono hgz ho, hk, fun ρB hT hF => ?_⟩
  obtain ⟨s', e1, e2⟩ := hb ρB hT hF
  exact ⟨s', by rw [exec_cons_running ρB x ys s s₁ (hstep ρB hF)]; exact e1, e2⟩

/-! ## 3. A statement and a block against their Body translation -/

/-- **One lowered statement against one Body statement**: a `logik` outcome is a callee's, a
    return is a `RueckZ`, a fall-through is a stretch to related states. -/
abbrev StmtZiel (u : UProg) (c : Fin u.fns.length) (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    {Γ : Ctx} {Λ Λ₁ : List (Res (declOf u))} (fn : UFn)
    (st : Stmt (declOf u) (verOf u c) false Γ Λ Λ₁) (σ : World (declOf u))
    (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State) (x : Gabbro.Body.Stmt) : Prop :=
  (∀ e, execStmt O passes R st σ ρ = .logik e →
    ∃ (g : (declOf u).Fn) (σr : World (declOf u)) (envA : Env (declOf u) ((declOf u).params g)),
      R g σr envA = .logik e) ∧
  (∀ σ' v, execStmt O passes R st σ ρ = .zurueck σ' v →
    ∃ A, RueckZ u A s [x] σ' (ergValOf (verOf u c).erg v)) ∧
  (∀ σ' ρ', execStmt O passes R st σ ρ = .ok σ' ρ' →
    ∃ A s', Strecke u A s s' [x] ∧ WRel u σ' s'.world ∧ LRel fn 0 ρ' s'.local')

/-- **One lowered block against its Body translation**, the same three outcomes. -/
abbrev BlockZiel (u : UProg) (c : Fin u.fns.length) (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    {Γ : Ctx} {Λ Λ' : List (Res (declOf u))} (fn : UFn)
    (b : Block (declOf u) (verOf u c) false Γ Λ Λ') (σ : World (declOf u))
    (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State) (t : List Gabbro.Body.Stmt) : Prop :=
  (∀ e, execBlock O passes R b σ ρ = .logik e →
    ∃ (g : (declOf u).Fn) (σr : World (declOf u)) (envA : Env (declOf u) ((declOf u).params g)),
      R g σr envA = .logik e) ∧
  (∀ σ' v, execBlock O passes R b σ ρ = .zurueck σ' v →
    ∃ A, RueckZ u A s t σ' (ergValOf (verOf u c).erg v)) ∧
  (∀ σ' ρ', execBlock O passes R b σ ρ = .ok σ' ρ' →
    ∃ A s', Strecke u A s s' t ∧ WRel u σ' s'.world ∧ LRel fn 0 ρ' s'.local')

variable {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
  {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}

theorem blockZiel_nil {Γ : Ctx} {Λ : List (Res (declOf u))} (fn : UFn) (σ : World (declOf u))
    (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State) (hW : WRel u σ s.world)
    (hL : LRel fn 0 ρ s.local') :
    BlockZiel u c O passes R fn (Block.nil : Block (declOf u) (verOf u c) false Γ Λ Λ) σ ρ s [] := by
  refine ⟨fun e h => ?_, fun σ' v h => ?_, fun σ' ρ' h => ?_⟩
  · rw [execBlockZ_nil] at h; cases h
  · rw [execBlockZ_nil] at h; cases h
  · rw [execBlockZ_nil] at h
    cases h
    exact ⟨[], s, Strecke.leer s, hW, hL⟩

/-- A conditional statement whose G outcome is the one of the chosen block and whose Body step
    runs the chosen branch. -/
theorem stmtZiel_of {Γ : Ctx} {Λ Λ₁ : List (Res (declOf u))} {fn : UFn}
    {st : Stmt (declOf u) (verOf u c) false Γ Λ Λ₁} {blk : Block (declOf u) (verOf u c) false Γ Λ Λ₁}
    {σ σl : World (declOf u)} {ρ : Env (declOf u) Γ} {s : Gabbro.Body.State}
    {x : Gabbro.Body.Stmt} {tB : List Gabbro.Body.Stmt}
    (hG : execStmt O passes R st σ ρ = execBlock O passes R blk σl ρ)
    (hB : ∀ ρB, Gabbro.Body.step ρB x s = Gabbro.Body.exec ρB tB s)
    (h : BlockZiel u c O passes R fn blk σl ρ s tB) : StmtZiel u c O passes R fn st σ ρ s x := by
  refine ⟨fun e he => h.1 e (hG.symm.trans he), fun σ' v he => ?_, fun σ' ρ' he => ?_⟩
  · obtain ⟨A, hg, ho, hk, hb⟩ := h.2.1 σ' v (hG.symm.trans he)
    refine ⟨A, hg, ho, hk, fun ρB hT hF => ?_⟩
    obtain ⟨s', e1, e2⟩ := hb ρB hT hF
    refine ⟨s', ?_, e2⟩
    simp only [Gabbro.Body.exec, hB ρB, e1]
  · obtain ⟨A, s', hS, hW, hL⟩ := h.2.2 σ' ρ' (hG.symm.trans he)
    refine ⟨A, s', { hS with lauf := fun ρB hT hF => ?_ }, hW, hL⟩
    simp only [Gabbro.Body.exec, hB ρB, hS.lauf ρB hT hF]

/-- **A statement, then the rest of a block.** -/
theorem blockZiel_cons {Γ : Ctx} {Λ Λ₁ Λ' : List (Res (declOf u))} {fn : UFn}
    {st : Stmt (declOf u) (verOf u c) false Γ Λ Λ₁}
    {rest : Block (declOf u) (verOf u c) false Γ Λ₁ Λ'} {σ : World (declOf u)}
    {ρ : Env (declOf u) Γ} {s : Gabbro.Body.State} {x : Gabbro.Body.Stmt}
    {ys : List Gabbro.Body.Stmt} (hst : StmtZiel u c O passes R fn st σ ρ s x)
    (hrest : ∀ σ₁ ρ₁ s₁, WRel u σ₁ s₁.world → LRel fn 0 ρ₁ s₁.local' →
      BlockZiel u c O passes R fn rest σ₁ ρ₁ s₁ ys) :
    BlockZiel u c O passes R fn (Block.cons st rest) σ ρ s (x :: ys) := by
  cases hx : execStmt O passes R st σ ρ with
  | ok σ₁ ρ₁ =>
    obtain ⟨A₁, s₁, hS, hW, hL⟩ := hst.2.2 σ₁ ρ₁ hx
    have hw := execBlockZ_cons_ok O passes R st rest hx
    have hr := hrest σ₁ ρ₁ s₁ hW hL
    refine ⟨fun e h => hr.1 e (hw.symm.trans h), fun σ' v h => ?_, fun σ' ρ' h => ?_⟩
    · obtain ⟨A₂, hR⟩ := hr.2.1 σ' v (hw.symm.trans h)
      refine ⟨A₁ ++ A₂, ?_⟩
      rw [← List.singleton_append]
      exact RueckZ.nach hS hR
    · obtain ⟨A₂, s₂, hS₂, hW₂, hL₂⟩ := hr.2.2 σ' ρ' (hw.symm.trans h)
      exact ⟨A₁ ++ A₂, s₂, Strecke.cons hS hS₂, hW₂, hL₂⟩
  | zurueck σ' v =>
    have hw := execBlockZ_cons_zurueck O passes R st rest (ρ := ρ) hx
    refine ⟨fun e h => (by rw [hw] at h; cases h), fun σ'' v' h => ?_, fun σ'' ρ'' h => by
      rw [hw] at h; cases h⟩
    rw [hw] at h
    cases h
    obtain ⟨A, hR⟩ := hst.2.1 σ' v hx
    refine ⟨A, ?_⟩
    rw [← List.singleton_append]
    exact RueckZ.append hR ys
  | logik e =>
    have hw := execBlockZ_cons_logik O passes R st rest (ρ := ρ) hx
    refine ⟨fun e' h => ?_, fun σ'' v' h => (by rw [hw] at h; cases h), fun σ'' ρ'' h => by
      rw [hw] at h; cases h⟩
    rw [hw] at h
    cases h
    exact hst.1 e hx
  | why σ' r =>
    have hw := execBlockZ_cons_still O passes R st rest (σ := σ) (ρ := ρ)
      (fun _ _ h => by rw [hx] at h; cases h)
    rw [hx] at hw
    exact ⟨fun e h => (by rw [hw] at h; cases h), fun σ'' v' h => (by rw [hw] at h; cases h),
      fun σ'' ρ'' h => by rw [hw] at h; cases h⟩
  | leave hl σ' ρ' =>
    have hw := execBlockZ_cons_still O passes R st rest (σ := σ) (ρ := ρ)
      (fun _ _ h => by rw [hx] at h; cases h)
    rw [hx] at hw
    exact ⟨fun e h => (by rw [hw] at h; cases h), fun σ'' v' h => (by rw [hw] at h; cases h),
      fun σ'' ρ'' h => by rw [hw] at h; cases h⟩
  | next hl σ' ρ' =>
    have hw := execBlockZ_cons_still O passes R st rest (σ := σ) (ρ := ρ)
      (fun _ _ h => by rw [hx] at h; cases h)
    rw [hx] at hw
    exact ⟨fun e h => (by rw [hw] at h; cases h), fun σ'' v' h => (by rw [hw] at h; cases h),
      fun σ'' ρ'' h => by rw [hw] at h; cases h⟩
  | hardware e =>
    have hw := execBlockZ_cons_still O passes R st rest (σ := σ) (ρ := ρ)
      (fun _ _ h => by rw [hx] at h; cases h)
    rw [hx] at hw
    exact ⟨fun e h => (by rw [hw] at h; cases h), fun σ'' v' h => (by rw [hw] at h; cases h),
      fun σ'' ρ'' h => by rw [hw] at h; cases h⟩

/-- **A binder, then the rest of a block**: the rest runs in the scope with the fresh `y`; after
    the block `y` is out of scope again. -/
theorem blockZiel_bind {Γ : Ctx} {Λ Λ' : List (Res (declOf u))} {fn : UFn} {τ : Ty}
    {e : Expr (declOf u) Γ Λ τ} {rest : Block (declOf u) (verOf u c) false (τ :: Γ) Λ Λ'}
    {σ : World (declOf u)} {ρ : Env (declOf u) Γ} {s s₁ : Gabbro.Body.State}
    {x : Gabbro.Body.Stmt} {ys : List Gabbro.Body.Stmt} {y : String} {w : Int × Int}
    (hy : y ∉ fn.params.map (·.1))
    (hstep : ∀ ρB, RahmenAlle u ρB → Gabbro.Body.step ρB x s = .running s₁)
    (hgz : ∀ w', gz w' s.world ≤ gz w' s₁.world)
    (h : BlockZiel u c O passes R (fn.mitBindung y w) rest (σ.lese Λ e.orte)
      (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) s₁ ys) :
    BlockZiel u c O passes R fn (Block.bind e rest) σ ρ s (x :: ys) := by
  refine ⟨fun err he => ?_, fun σ' v he => ?_, fun σ' ρ' he => ?_⟩
  · rw [execBlockZ_bind] at he
    exact h.1 err (schrumpfZ_logik he)
  · rw [execBlockZ_bind] at he
    obtain ⟨A, hR⟩ := h.2.1 σ' v (schrumpfZ_zurueck he)
    exact ⟨A, RueckZ.vor hstep hgz hR⟩
  · rw [execBlockZ_bind] at he
    obtain ⟨ρ'', hin, rfl⟩ := schrumpfZ_ok he
    obtain ⟨A, s', hS, hW, hL⟩ := h.2.2 σ' ρ'' hin
    exact ⟨A, s', Strecke.vor hstep hgz hS, hW, lrel_tail hL hy⟩

/-! ## 4. The run's conclusion along a body -/

theorem laufZiel_strecke {Γ Γ₁ : Ctx} {Λ Λ₁ : List (Res (declOf u))}
    {b0 : Endblock (declOf u) (verOf u c) false Γ Λ}
    {b1 : Endblock (declOf u) (verOf u c) false Γ₁ Λ₁}
    {σ σ₁ : World (declOf u)} {ρ : Env (declOf u) Γ} {ρ₁ : Env (declOf u) Γ₁}
    {s s₁ : Gabbro.Body.State} {A : List Eintrag} {xs bs : List Gabbro.Body.Stmt}
    (hrun : (∀ e, execEnd O passes R b0 σ ρ = .logik e → execEnd O passes R b1 σ₁ ρ₁ = .logik e) ∧
      (∀ σ' v, execEnd O passes R b0 σ ρ = .zurueck σ' v →
        execEnd O passes R b1 σ₁ ρ₁ = .zurueck σ' v))
    (hS : Strecke u A s s₁ xs) (ih : LaufZiel u c O passes R b1 σ₁ ρ₁ s₁ bs) :
    LaufZiel u c O passes R b0 σ ρ s (xs ++ bs) := by
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

theorem laufZiel_rueck {Γ : Ctx} {Λ : List (Res (declOf u))}
    {b0 : Endblock (declOf u) (verOf u c) false Γ Λ} {σ σ' : World (declOf u)}
    {ρ : Env (declOf u) Γ} {s : Gabbro.Body.State} {bs : List Gabbro.Body.Stmt}
    {A : List Eintrag} {v : ErgVal (declOf u) (verOf u c).erg}
    (h : execEnd O passes R b0 σ ρ = .zurueck σ' v)
    (hR : RueckZ u A s bs σ' (ergValOf (verOf u c).erg v)) :
    LaufZiel u c O passes R b0 σ ρ s bs := by
  refine ⟨fun e h' => (by rw [h] at h'; cases h'), fun σ'' v' h' => ?_⟩
  rw [h] at h'
  cases h'
  obtain ⟨hg, ho, hk, hb⟩ := hR
  refine ⟨A, hg, ho, hk, fun ρB hT hF => ?_⟩
  obtain ⟨s', h1, h2⟩ := hb ρB hT hF
  exact ⟨s', by simp only [h1, Gabbro.Body.finalState], by rw [h1, finalValue_returned], h2⟩

theorem laufZiel_logik {Γ : Ctx} {Λ : List (Res (declOf u))}
    {b0 : Endblock (declOf u) (verOf u c) false Γ Λ} {σ : World (declOf u)}
    {ρ : Env (declOf u) Γ} {s : Gabbro.Body.State} {bs : List Gabbro.Body.Stmt} {e : Logik (declOf u)}
    (h : execEnd O passes R b0 σ ρ = .logik e)
    (hb : ∃ (g : (declOf u).Fn) (σr : World (declOf u)) (envA : Env (declOf u) ((declOf u).params g)),
      R g σr envA = .logik e) :
    LaufZiel u c O passes R b0 σ ρ s bs :=
  ⟨fun e' h' => (by rw [h] at h'; cases h'; exact hb), fun σ' v h' => by rw [h] at h'; cases h'⟩

/-- **A statement, then the rest of a body.** -/
theorem laufZiel_cons {Γ : Ctx} {Λ Λ₁ : List (Res (declOf u))} {fn : UFn}
    {st : Stmt (declOf u) (verOf u c) false Γ Λ Λ₁}
    {rest : Endblock (declOf u) (verOf u c) false Γ Λ₁} {σ : World (declOf u)}
    {ρ : Env (declOf u) Γ} {s : Gabbro.Body.State} {x : Gabbro.Body.Stmt}
    {bs : List Gabbro.Body.Stmt} (hst : StmtZiel u c O passes R fn st σ ρ s x)
    (hrest : ∀ σ₁ ρ₁ s₁, WRel u σ₁ s₁.world → LRel fn 0 ρ₁ s₁.local' →
      LaufZiel u c O passes R rest σ₁ ρ₁ s₁ bs) :
    LaufZiel u c O passes R (Endblock.cons st rest) σ ρ s (x :: bs) := by
  cases hx : execStmt O passes R st σ ρ with
  | ok σ₁ ρ₁ =>
    obtain ⟨A, s₁, hS, hW, hL⟩ := hst.2.2 σ₁ ρ₁ hx
    have := laufZiel_strecke (cons_lauf O passes R st rest σ σ₁ ρ ρ₁ hx) hS (hrest σ₁ ρ₁ s₁ hW hL)
    rw [List.singleton_append] at this
    exact this
  | zurueck σ' v =>
    have hw : execEnd O passes R (Endblock.cons st rest) σ ρ = .zurueck σ' v := by
      simp only [execEnd, hx]
    obtain ⟨A, hR⟩ := hst.2.1 σ' v hx
    have hR' := RueckZ.append hR bs
    rw [List.singleton_append] at hR'
    exact laufZiel_rueck hw hR'
  | logik e =>
    have hw : execEnd O passes R (Endblock.cons st rest) σ ρ = .logik e := by
      simp only [execEnd, hx]
    exact laufZiel_logik hw (hst.1 e hx)
  | why σ' r =>
    have hw : execEnd O passes R (Endblock.cons st rest) σ ρ = .why σ' r := by
      simp only [execEnd, hx]
    exact ⟨fun e h => (by rw [hw] at h; cases h), fun σ'' v h => by rw [hw] at h; cases h⟩
  | leave hl σ' ρ' =>
    have hw : execEnd O passes R (Endblock.cons st rest) σ ρ = .leave hl σ' ρ' := by
      simp only [execEnd, hx]
    exact ⟨fun e h => (by rw [hw] at h; cases h), fun σ'' v h => by rw [hw] at h; cases h⟩
  | next hl σ' ρ' =>
    have hw : execEnd O passes R (Endblock.cons st rest) σ ρ = .next hl σ' ρ' := by
      simp only [execEnd, hx]
    exact ⟨fun e h => (by rw [hw] at h; cases h), fun σ'' v h => by rw [hw] at h; cases h⟩
  | hardware e =>
    have hw : execEnd O passes R (Endblock.cons st rest) σ ρ = .hardware e := by
      simp only [execEnd, hx]
    exact ⟨fun e h => (by rw [hw] at h; cases h), fun σ'' v h => by rw [hw] at h; cases h⟩

end Gabbro.Bruecke
