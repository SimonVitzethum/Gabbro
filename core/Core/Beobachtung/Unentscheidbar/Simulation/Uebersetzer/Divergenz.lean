module

public import Core.Beobachtung.Unentscheidbar.Modell
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Grundlagen

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- A run never dies: every step count still has a frame. This is the runtime
    side of divergence for a minimization loop. -/
def LaufStirbtNicht (prog : List Befehl) (r : Rahmen) : Prop :=
  ∀ k, ∃ r', (Schritt prog)^[k] (some r) = some r'

/-- A run dies: some step count has no successor frame. -/
def LaufStirbt (prog : List Befehl) (r : Rahmen) : Prop :=
  ∃ k, (Schritt prog)^[k] (some r) = none

/-- Not dying and dying are exact complements. Once a run is dead it stays
    dead, so a surviving step count rules out every earlier death. -/
theorem laufStirbtNicht_iff (prog : List Befehl) (r : Rahmen) :
    LaufStirbtNicht prog r ↔ ¬ LaufStirbt prog r := by
  constructor
  · intro hlive hdead
    rcases hdead with ⟨k, hk⟩
    obtain ⟨r', hr'⟩ := hlive k
    rw [hk] at hr'
    cases hr'
  · intro hnot k
    cases hk : (Schritt prog)^[k] (some r) with
    | none =>
      exact False.elim (hnot ⟨k, hk⟩)
    | some r' =>
      exact ⟨r', hk⟩

/-- A run that never dies reaches a frame at every step, hence every state it
    reaches is itself the start of a never-dying run. -/
theorem laufStirbtNichtVon (prog : List Befehl) (r : Rahmen) (k : Nat) (rk : Rahmen)
    (hlive : LaufStirbtNicht prog r)
    (hrk : (Schritt prog)^[k] (some r) = some rk) :
    LaufStirbtNicht prog rk := by
  intro t
  obtain ⟨r', ht⟩ := hlive (k + t)
  refine ⟨r', ?_⟩
  rw [show k + t = t + k by omega, Function.iterate_add_apply, hrk]
  exact ht

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
