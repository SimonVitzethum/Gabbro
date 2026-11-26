/-
  File:      core/Core/Annahme/DomaeneBeweise/Unentscheidbar.lean
  Subject:   The domain-coherence condition that escapes the finite table is undecidable
               (owner rule 2026-11-24) and is therefore a GabbroProve user obligation.

  The table checker `pruefeDomaenenTab` decides every condition of `tabKohaerent`: a positive
  domain count, finitely many listed assignments, and finitely many channels. If a plan instead
  computes its assignment for every one of infinitely many places, the condition
  "every place is assigned inside the declared domains" is a totality-style property of an
  arbitrary computation; no checker decides it. The pinned `…UnentscheidbarAussage` below is the
  partrec core of that fact: by Rice's theorem an everywhere-divergent code would have to be
  total if the predicate were computable, contradicting `Part.not_none_dom`. The property is a
  user obligation (GabbroProve), not a checker rule, and the transfer from this partrec core to a
  concrete Gabbro unit still needs the simulation premise described in the existing
  `Beobachtung/Unentscheidbar` and `Beobachtung/Wahrscheinlichkeit/Unentscheidbar` files.
-/
module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.Reduce

@[expose] public section

namespace Gabbro.Core.Annahme

open Nat.Partrec.Code

/-- **No checker decides function-based coherence over infinitely many places** (partrec core,
    user obligation). Deciding whether every place of a computed assignment is in range would
    decide totality of a partial recursive function.
    Difficulty: light. Proof sketch: Rice's theorem with `C = {f | ∀ n, (f n).Dom}`; a computable
    predicate would force the everywhere-divergent `Nat.Partrec.none` into `C`, contradicting
    `Part.not_none_dom` at input `0`. -/
def DomaenenKohaerenzUnentscheidbarAussage : Prop :=
  ¬ ComputablePred fun c : Nat.Partrec.Code => ∀ n : ℕ, (Nat.Partrec.Code.eval c n).Dom

/-- The partrec core is proved: totality is a non-trivial extensional property, so Rice's theorem
    applies and the everywhere-divergent computation cannot be total. -/
theorem domaenenKohaerenz_unentscheidbar : DomaenenKohaerenzUnentscheidbarAussage := by
  intro h
  have htotal : ∀ n : ℕ, (Part.none : Part ℕ).Dom := by
    exact ComputablePred.rice ({f : ℕ →. ℕ | ∀ n, (f n).Dom} : Set (ℕ →. ℕ)) h
      Nat.Partrec.zero Nat.Partrec.none (by intro n; trivial)
  exact Part.not_none_dom (htotal 0)

end Gabbro.Core.Annahme
