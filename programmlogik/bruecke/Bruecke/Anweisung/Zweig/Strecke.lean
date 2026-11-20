module
public import Bruecke.Anweisung.Zweig.Kopf
@[expose] public section

/-!
# Shared stretch and branch execution facts

A `Strecke` records a finite running Body prefix with ordered writer answers and monotone
ghost counters. The append and branch lemmas are shared execution infrastructure;
`Kette/Strecke.lean` supplies the carried-environment version used by the source bridge.
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

end Gabbro.Bruecke
