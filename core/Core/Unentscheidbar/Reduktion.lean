module

public import Core.Unentscheidbar.Modell
public import Mathlib.Computability.Halting
public import Mathlib.Computability.Reduce

@[expose] public section

namespace Gabbro.Core.Unentscheidbar

open Ast.Semantik
open Nat.Partrec.Code

/-- Das Gabbro-Halteprädikat bei fester Eingabe `n`: der simulierte Code `c`
    hält (mit irgendeiner Ausgabe). Das Prädikat steht über `Code`
    (`Primcodable`-Instanz aus Mathlib), nicht über Rahmen — Rahmen enthalten
    Funktionen (`temp`, `zaehler`) und sind nicht abzählbar kodiert. -/
def GabbroHaltsAt (programm : Nat.Partrec.Code → List Befehl)
    (start : Nat.Partrec.Code → ℕ → Rahmen) (n : ℕ) (c : Nat.Partrec.Code) : Prop :=
  ∃ a, HaeltMit (programm c) (start c n) a

/-- Brücke zwischen `Dom` und `= Part.some`: die Treue-Aussage spricht über
    `Part.some`, das Halteproblem über `Dom`. -/
theorem dom_iff_haeltMit {programm : Nat.Partrec.Code → List Befehl}
    {start : Nat.Partrec.Code → ℕ → Rahmen} {c : Nat.Partrec.Code} {n : ℕ}
    (ht : ∀ a, (eval c n = Part.some a ↔ HaeltMit (programm c) (start c n) a)) :
    (eval c n).Dom ↔ GabbroHaltsAt programm start n c := by
  constructor
  · intro hd
    have hEq : eval c n = Part.some (Part.get _ hd) := by
      apply Part.ext
      intro a
      constructor
      · intro ha
        have heq : a = Part.get _ hd := Part.mem_unique ha (Part.get_mem hd)
        rw [heq]
        exact Part.mem_some_iff.mpr rfl
      · intro e
        have heq : a = Part.get _ hd := Part.mem_some_iff.mp e
        rw [heq]
        exact Part.get_mem hd
    exact ⟨_, (ht _).mp hEq⟩
  · rintro ⟨a, ha⟩
    rw [(ht a).mpr ha]
    exact Part.dom_iff_mem.mpr ⟨a, Part.mem_some_iff.mpr rfl⟩

/-- Das Halteproblem der μ-rekursiven Codes reduziert sich many-one auf das
    Gabbro-Halteprädikat — mit der Identität als Reduktionsfunktion, direkt
    aus der Simulationstreue. -/
theorem gabbro_halts_reduktion (programm : Nat.Partrec.Code → List Befehl)
    (start : Nat.Partrec.Code → ℕ → Rahmen) (n : ℕ)
    (h : SimulationsTreue programm start) (hoff : ∀ c, OffenesFragment (start c n)) :
    (fun c => (eval c n).Dom) ≤₀ GabbroHaltsAt programm start n :=
  ⟨id, Computable.id, fun c => dom_iff_haeltMit (h c n (hoff c))⟩

/-- Das Gabbro-Halteprädikat (offenes Fragment, feste Eingabe) ist nicht
    entscheidbar: aus seiner Entscheidbarkeit folgte via Reduktion die des
    μ-rekursiven Halteproblems — Widerspruch zu `halting_problem`. -/
theorem gabbro_halts_unentscheidbar (programm : Nat.Partrec.Code → List Befehl)
    (start : Nat.Partrec.Code → ℕ → Rahmen) (n : ℕ)
    (h : SimulationsTreue programm start) (hoff : ∀ c, OffenesFragment (start c n)) :
    ¬ ComputablePred (GabbroHaltsAt programm start n) := by
  intro hc
  exact ComputablePred.halting_problem n
    (ComputablePred.computable_of_manyOneReducible
      (gabbro_halts_reduktion programm start n h hoff) hc)

/-- Die pinnierte Aussage: für jede treue Simulation und jede feste Eingabe ist
    das Halteprädikat der simulierten Programme im offenen Fragment
    unentscheidbar. -/
def HalteUnentscheidbarAussage : Prop :=
  ∀ programm start n, SimulationsTreue programm start →
    (∀ c, OffenesFragment (start c n)) →
    ¬ ComputablePred (GabbroHaltsAt programm start n)

end Gabbro.Core.Unentscheidbar
