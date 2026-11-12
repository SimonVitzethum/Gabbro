/-
  A rank certificate for the cycles of the call graph.

  `zykS` asks two closures of the call graph per pair of functions. A rank that never rises
  along a call site (`kantenFallen`, one walk over the call sites of every body) is equal on
  every cycle (`zykS_rang`), so a property that is a function of the rank is equal on every
  cycle (`zykS_gleich`). The rank itself is not trusted: any function passes or fails the check.
-/
module
public import Grammatik.Logik.Terminierung.Mass
public import Grammatik.Zielsatz.Faeden.Verbund.T1
public import Grammatik.Nebenlaeufigkeit.Allgemein.FadenMerkmal.Stellen
@[expose] public section

namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration} [DecidableEq D.Fn]

/-- The rank does not rise from `f` along one call site. -/
def stelleFaellt (fs : List D.Fn) (r : D.Fn → Nat) (f : D.Fn) : Stelle D → Bool
  | .ruf g => decide (r g ≤ r f)
  | .ind n => fs.all fun g => !(D.passt g n) || decide (r g ≤ r f)
  | .sperre _ => true

/-- The rank rises along no call site of any member. -/
def kantenFallen (P : Programm D) (fs : List D.Fn) (r : D.Fn → Nat) : Bool :=
  fs.all fun f => (stellenE (P.rumpf f)).all (stelleFaellt fs r f)

variable {P : Programm D} {fs : List D.Fn} {r : D.Fn → Nat}

/-- A checked rank does not rise along a call. -/
theorem ruft_faellt (hvoll : ∀ g : D.Fn, g ∈ fs) (checked : kantenFallen P fs r = true)
    {f g : D.Fn} (calls : ruftB P f g = true) : r g ≤ r f := by
  unfold ruftB at calls
  rw [mE_stellen, Bool.not_eq_true'] at calls
  obtain ⟨s, member, rejected⟩ := List.all_eq_false.mp calls
  have falls := List.all_eq_true.mp (List.all_eq_true.mp checked f (hvoll f)) s member
  cases s with
  | ruf h =>
    have same : h = g := by
      simpa only [Merkmal.an, Bool.not_eq_true', decide_eq_false_iff_not, Decidable.not_not,
        Bool.not_eq_true, Bool.not_eq_false'] using rejected
    subst same
    exact of_decide_eq_true falls
  | ind n =>
    have fits : D.passt g n = true := by
      simpa only [Merkmal.an, Bool.not_eq_true', Bool.not_eq_true, Bool.not_eq_false] using rejected
    have at_g := List.all_eq_true.mp falls g (hvoll g)
    rw [fits, Bool.not_true, Bool.false_or] at at_g
    exact of_decide_eq_true at_g
  | sperre L => exact absurd rfl rejected

/-- A checked rank does not rise along the computed call graph. -/
theorem reach_faellt (hvoll : ∀ g : D.Fn, g ∈ fs) (checked : kantenFallen P fs r = true)
    {f g : D.Fn} (reached : reachB P fs f g = true) : r g ≤ r f :=
  reachB_in P fs (Z := fun x => r x ≤ r f) (Nat.le_refl _)
    (fun _ _ below calls => Nat.le_trans (ruft_faellt hvoll checked calls) below) g reached

/-- **A checked rank is equal on every cycle.** -/
theorem zykS_rang (hvoll : ∀ g : D.Fn, g ∈ fs) (checked : kantenFallen P fs r = true)
    {f g : D.Fn} (cycle : zykS P fs f g = true) : r f = r g := by
  unfold zykS zyklusMit at cycle
  have both := (Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp cycle).1
  exact Nat.le_antisymm (reach_faellt hvoll checked both.2) (reach_faellt hvoll checked both.1)

/-- **What is a function of a checked rank is equal on every cycle.** -/
theorem zykS_gleich {α : Type} (hvoll : ∀ g : D.Fn, g ∈ fs) (checked : kantenFallen P fs r = true)
    (wert : D.Fn → α) (proRang : Nat → α) (table : ∀ f, wert f = proRang (r f))
    {f g : D.Fn} (cycle : zykS P fs f g = true) : wert f = wert g := by
  rw [table f, table g, zykS_rang hvoll checked cycle]

end Gabbro.Grammatik
