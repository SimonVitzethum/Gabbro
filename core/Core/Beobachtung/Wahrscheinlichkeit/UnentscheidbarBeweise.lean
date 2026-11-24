/-
  File:      Core/Beobachtung/Wahrscheinlichkeit/UnentscheidbarBeweise.lean
  Subject:   Proofs of the six pinned probability-remainder undecidability
    statements (owner rule 2026-11-24, B11(c)(d), M9P).

  Each pinned `…UnentscheidbarAussage` in `Unentscheidbar.lean` states a
  `¬ ComputablePred` over `Nat.Partrec.Code`. Four of them are exactly the
  halting problem on input `0` and are discharged by `ComputablePred.halting_problem 0`.
  The totality and existential-remainder cores are nontrivial extensional
  properties of partial recursive functions; they are discharged by Rice's
  theorem `ComputablePred.rice`, using `Nat.Partrec.zero` (a total witness) and
  `Nat.Partrec.none` (an everywhere-divergent counterexample).

  The partrec cores are proved here. The transfer from these cores to "no
  checker decides the Gabbro remainder" still needs the simulation premise
  `gabbroSimuliertPartrec` described in `Unentscheidbar.lean`; it is not a
  claim of this file.
-/
module

public import Core.Beobachtung.Wahrscheinlichkeit.Unentscheidbar
public import Mathlib.Computability.Halting

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Nat.Partrec.Code

/-- The `planned.probability.event` core is the halting problem on input `0`. -/
theorem prEreignisUnentscheidbar : prEreignisUnentscheidbarAussage :=
  ComputablePred.halting_problem 0

/-- The `planned.probability.cost` core is the halting problem on input `0`. -/
theorem kostenErwartungUnentscheidbar : kostenErwartungUnentscheidbarAussage :=
  ComputablePred.halting_problem 0

/-- Totality is undecidable: by Rice's theorem an everywhere-divergent
    function would have to be total if totality were computable. -/
theorem fastSicherAbschlussUnentscheidbar : fastSicherAbschlussUnentscheidbarAussage := by
  intro h
  have htotal : ∀ n : ℕ, (Part.none : Part ℕ).Dom := by
    exact ComputablePred.rice ({f : ℕ →. ℕ | ∀ n, (f n).Dom} : Set (ℕ →. ℕ)) h
      Nat.Partrec.zero Nat.Partrec.none (by intro n; trivial)
  exact Part.not_none_dom (htotal 0)

/-- The `planned.probability.progress` core is the halting problem on input `0`. -/
theorem fastSicherFortschrittUnentscheidbar : fastSicherFortschrittUnentscheidbarAussage :=
  ComputablePred.halting_problem 0

/-- Existence of a halting input is undecidable: by Rice's theorem an
    everywhere-divergent function would have to halt somewhere if that
    property were computable. -/
theorem infoTheoretischUnentscheidbar : infoTheoretischUnentscheidbarAussage := by
  intro h
  have hex : ∃ n : ℕ, (Part.none : Part ℕ).Dom := by
    exact ComputablePred.rice ({f : ℕ →. ℕ | ∃ n, (f n).Dom} : Set (ℕ →. ℕ)) h
      Nat.Partrec.zero Nat.Partrec.none ⟨0, by trivial⟩
  rcases hex with ⟨n, hn⟩
  exact Part.not_none_dom hn

/-- The `planned.probability.reduction` core is the halting problem on input `0`. -/
theorem reduktionUnentscheidbar : reduktionUnentscheidbarAussage :=
  ComputablePred.halting_problem 0

end Gabbro.Core.Beobachtung
