module

public import Core.Unentscheidbar.Modell
public import Mathlib.Computability.Halting
public import Mathlib.Computability.Reduce

@[expose] public section

namespace Gabbro.Core.Unentscheidbar

open Ast.Semantik
open Nat.Partrec.Code

/-- Das Gabbro-Halteprädikat bei fester Eingabe `n`: die Programmnummer `i`
    dekodiert zu einem Programm, das ab dem kanonischen Startrahmen hält
    (mit irgendeiner Ausgabe). Das Prädikat steht über `ℕ` — der Kodierung
    der Gabbro-Programme, die der Prüfer sieht — nicht über Codes. -/
def HaeltProg (s : SimulationsSubstrat) (n : ℕ) (i : ℕ) : Prop :=
  ∃ p, s.dekodiere i = some p ∧ ∃ a, HaeltMit p (s.startVon n) a

/-- Brücke zwischen `Dom` und `= Part.some`: die Treue-Aussage spricht über
    `Part.some`, das Halteproblem über `Dom`. -/
theorem dom_iff_haeltMit {s : SimulationsSubstrat} {c : Nat.Partrec.Code} {n : ℕ}
    (ht : ∀ a, (eval c n = Part.some a ↔
      HaeltMit (s.programm c) (s.startVon n) a)) :
    (eval c n).Dom ↔ ∃ a, HaeltMit (s.programm c) (s.startVon n) a := by
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
    rw [(ht a).mp ha]
    exact Part.dom_iff_mem.mpr ⟨a, Part.mem_some_iff.mpr rfl⟩

/-- Das Halteproblem der μ-rekursiven Codes reduziert sich many-one auf das
    Gabbro-Halteprädikat über Programmnummern: entscheidet `D` die Programme,
    so entscheidet `D ∘ (kodiere ∘ programm)` die Codes. Die Reduktionsfunktion
    ist berechenbar per `komposition_berechenbar`; die Linksinverse
    (`dekodiere_links`) identifiziert das dekodierte Programm eindeutig. -/
theorem substrat_halts_reduktion (s : SimulationsSubstrat) (n : ℕ) :
    (fun c => (eval c n).Dom) ≤₀ HaeltProg s n :=
  ⟨_, s.komposition_berechenbar, fun c => by
    have ht := s.treue c n
    rw [dom_iff_haeltMit ht]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨s.programm c, s.dekodiere_links _, a, ha⟩
    · rintro ⟨p, hp, a, ha⟩
      have h2 : some (s.programm c) = some p := by
        rw [← s.dekodiere_links (s.programm c)]
        exact hp
      have hpeq : p = s.programm c := (Option.some_inj.mp h2).symm
      subst hpeq
      exact ⟨a, ha⟩⟩

/-- Das Gabbro-Halteprädikat über Programmnummern (offenes Fragment, feste
    Eingabe) ist nicht entscheidbar: aus seiner Entscheidbarkeit folgte via
    Reduktion die des μ-rekursiven Halteproblems — Widerspruch zu
    `halting_problem`. -/
theorem substrat_halts_unentscheidbar (s : SimulationsSubstrat) (n : ℕ) :
    ¬ ComputablePred (HaeltProg s n) := by
  intro hc
  exact ComputablePred.halting_problem n
    (ComputablePred.computable_of_manyOneReducible
      (substrat_halts_reduktion s n) hc)

/-- Die pinnierte Aussage: für jedes Substrat und jede feste Eingabe ist das
    Halteprädikat der Gabbro-Programme (als Nummern) unentscheidbar. -/
def HalteUnentscheidbarAussage : Prop :=
  ∀ s n, ¬ ComputablePred (HaeltProg s n)

end Gabbro.Core.Unentscheidbar
