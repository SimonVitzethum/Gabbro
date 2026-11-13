module
public import Bruecke.Anweisung.Zweig.Strecke
public import Bruecke.Anweisung.Lokal.Position
public import Bruecke.Teil.Lokal.Kopf
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

/-! Answer-table stretches and returns whose environments owe frames only for carried functions. -/

structure Strecke_G (u : UProg) (C : Fin u.fns.length → Prop) (A : List Eintrag) (s s' : Gabbro.Body.State)
    (bs : List Gabbro.Body.Stmt) : Prop where
  gut : ∀ e ∈ A, EintragGut u e
  oben : Oben u A s.world
  unten : Unten u A s'.world
  schluessel : Schluessel A
  mono : ∀ w, gz w s.world ≤ gz w s'.world
  lauf : ∀ ρB, Treu A ρB → RahmenAlleC u C ρB → Gabbro.Body.exec ρB bs s = .running s'

abbrev RueckZ_G (u : UProg) (C : Fin u.fns.length → Prop) (A : List Eintrag) (s : Gabbro.Body.State) (bs : List Gabbro.Body.Stmt)
    (σ' : World (declOf u)) (v : Option Gabbro.Body.Value) : Prop :=
  (∀ e ∈ A, EintragGut u e) ∧ Oben u A s.world ∧ Schluessel A ∧
    ∀ ρB, Treu A ρB → RahmenAlleC u C ρB →
      ∃ s', Gabbro.Body.exec ρB bs s = .returned s' v ∧ WGRel u σ' s'.world

theorem Strecke_G.leer (s : Gabbro.Body.State) : Strecke_G u C [] s s [] :=
  { gut := fun _ h => absurd h List.not_mem_nil
    oben := fun _ h => absurd h List.not_mem_nil
    unten := fun _ h => absurd h List.not_mem_nil
    schluessel := List.Pairwise.nil
    mono := fun _ => Int.le_refl _
    lauf := fun _ _ _ => rfl }

theorem Strecke_G.schritt {s s₁ : Gabbro.Body.State} {x : Gabbro.Body.Stmt}
    (hstep : ∀ ρB, RahmenAlleC u C ρB → Gabbro.Body.step ρB x s = .running s₁)
    (hgz : ∀ w, gz w s.world ≤ gz w s₁.world) : Strecke_G u C [] s s₁ [x] :=
  { gut := fun _ h => absurd h List.not_mem_nil
    oben := fun _ h => absurd h List.not_mem_nil
    unten := fun _ h => absurd h List.not_mem_nil
    schluessel := List.Pairwise.nil
    mono := hgz
    lauf := fun ρB _ hF => by simp only [Gabbro.Body.exec, hstep ρB hF] }

theorem Strecke_G.append {A₁ A₂ : List Eintrag} {s s₁ s₂ : Gabbro.Body.State}
    {xs ys : List Gabbro.Body.Stmt} (h₁ : Strecke_G u C A₁ s s₁ xs) (h₂ : Strecke_G u C A₂ s₁ s₂ ys) :
    Strecke_G u C (A₁ ++ A₂) s s₂ (xs ++ ys) :=
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

theorem Strecke_G.cons {A₁ A₂ : List Eintrag} {s s₁ s₂ : Gabbro.Body.State} {x : Gabbro.Body.Stmt}
    {ys : List Gabbro.Body.Stmt} (h₁ : Strecke_G u C A₁ s s₁ [x]) (h₂ : Strecke_G u C A₂ s₁ s₂ ys) :
    Strecke_G u C (A₁ ++ A₂) s s₂ (x :: ys) := by
  rw [← List.singleton_append]
  exact Strecke_G.append h₁ h₂

theorem Strecke_G.vor {A : List Eintrag} {s s₁ s₂ : Gabbro.Body.State} {x : Gabbro.Body.Stmt}
    {ys : List Gabbro.Body.Stmt}
    (hstep : ∀ ρB, RahmenAlleC u C ρB → Gabbro.Body.step ρB x s = .running s₁)
    (hgz : ∀ w, gz w s.world ≤ gz w s₁.world) (h : Strecke_G u C A s₁ s₂ ys) :
    Strecke_G u C A s s₂ (x :: ys) :=
  { gut := h.gut
    oben := oben_mono hgz h.oben
    unten := h.unten
    schluessel := h.schluessel
    mono := fun w => Int.le_trans (hgz w) (h.mono w)
    lauf := fun ρB hT hF => by
      rw [exec_cons_running ρB x ys s s₁ (hstep ρB hF)]
      exact h.lauf ρB hT hF }

theorem RueckZ_G.append {A : List Eintrag} {s : Gabbro.Body.State} {xs : List Gabbro.Body.Stmt}
    {σ' : World (declOf u)} {v : Option Gabbro.Body.Value} (h : RueckZ_G u C A s xs σ' v)
    (ys : List Gabbro.Body.Stmt) : RueckZ_G u C A s (xs ++ ys) σ' v := by
  obtain ⟨hg, ho, hk, hb⟩ := h
  refine ⟨hg, ho, hk, fun ρB hT hF => ?_⟩
  obtain ⟨s', h1, h2⟩ := hb ρB hT hF
  refine ⟨s', ?_, h2⟩
  simp only [exec_append, h1]

theorem RueckZ_G.nach {A₁ A₂ : List Eintrag} {s s₁ : Gabbro.Body.State}
    {xs ys : List Gabbro.Body.Stmt} {σ' : World (declOf u)} {v : Option Gabbro.Body.Value}
    (h₁ : Strecke_G u C A₁ s s₁ xs) (h₂ : RueckZ_G u C A₂ s₁ ys σ' v) :
    RueckZ_G u C (A₁ ++ A₂) s (xs ++ ys) σ' v := by
  obtain ⟨hg, ho, hk, hb⟩ := h₂
  refine ⟨fun e he => (List.mem_append.mp he).elim (h₁.gut e) (hg e),
    fun e he => (List.mem_append.mp he).elim (h₁.oben e) (fun h => oben_mono h₁.mono ho e h),
    schluessel_append h₁.schluessel h₁.unten hk ho, fun ρB hT hF => ?_⟩
  obtain ⟨s', e1, e2⟩ := hb ρB (fun e he => hT e (List.mem_append_right _ he)) hF
  refine ⟨s', ?_, e2⟩
  rw [exec_append, h₁.lauf ρB (fun e he => hT e (List.mem_append_left _ he)) hF]
  exact e1

theorem RueckZ_G.vor {A : List Eintrag} {s s₁ : Gabbro.Body.State} {x : Gabbro.Body.Stmt}
    {ys : List Gabbro.Body.Stmt} {σ' : World (declOf u)} {v : Option Gabbro.Body.Value}
    (hstep : ∀ ρB, RahmenAlleC u C ρB → Gabbro.Body.step ρB x s = .running s₁)
    (hgz : ∀ w, gz w s.world ≤ gz w s₁.world) (h : RueckZ_G u C A s₁ ys σ' v) :
    RueckZ_G u C A s (x :: ys) σ' v := by
  obtain ⟨hg, ho, hk, hb⟩ := h
  refine ⟨hg, oben_mono hgz ho, hk, fun ρB hT hF => ?_⟩
  obtain ⟨s', e1, e2⟩ := hb ρB hT hF
  exact ⟨s', by rw [exec_cons_running ρB x ys s s₁ (hstep ρB hF)]; exact e1, e2⟩

abbrev StmtZiel_G {loopMode : Bool} (u : UProg) (C : Fin u.fns.length → Prop) (c : Fin u.fns.length) (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    {Γ : Ctx} {Λ Λ₁ : List (Res (declOf u))} (fn : UFn) (ids : List String)
    (st : Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ₁) (σ : World (declOf u))
    (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State) (x : Gabbro.Body.Stmt) : Prop :=
  (∀ e, execStmt O passes R st σ ρ = .logik e →
    ∃ (g : (declOf u).Fn) (σr : World (declOf u)) (envA : Env (declOf u) ((declOf u).params g)),
      C g ∧ R g σr envA = .logik e) ∧
  (∀ σ' v, execStmt O passes R st σ ρ = .zurueck σ' v →
    ∃ A, RueckZ_G u C A s [x] σ' (ergValOf (verOf u c).erg v)) ∧
  (∀ σ' ρ', execStmt O passes R st σ ρ = .ok σ' ρ' →
    ∃ A s', Strecke_G u C A s s' [x] ∧ WGRel u σ' s'.world ∧ PositionalLRel fn ids 0 ρ' s'.local')

abbrev BlockZiel_G {loopMode : Bool} (u : UProg) (C : Fin u.fns.length → Prop) (c : Fin u.fns.length) (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    {Γ : Ctx} {Λ Λ' : List (Res (declOf u))} (fn : UFn) (ids : List String)
    (b : Block (declOf u) (verOf u c) loopMode Γ Λ Λ') (σ : World (declOf u))
    (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State) (t : List Gabbro.Body.Stmt) : Prop :=
  (∀ e, execBlock O passes R b σ ρ = .logik e →
    ∃ (g : (declOf u).Fn) (σr : World (declOf u)) (envA : Env (declOf u) ((declOf u).params g)),
      C g ∧ R g σr envA = .logik e) ∧
  (∀ σ' v, execBlock O passes R b σ ρ = .zurueck σ' v →
    ∃ A, RueckZ_G u C A s t σ' (ergValOf (verOf u c).erg v)) ∧
  (∀ σ' ρ', execBlock O passes R b σ ρ = .ok σ' ρ' →
    ∃ A s', Strecke_G u C A s s' t ∧ WGRel u σ' s'.world ∧ PositionalLRel fn ids 0 ρ' s'.local')

end Gabbro.Bruecke
