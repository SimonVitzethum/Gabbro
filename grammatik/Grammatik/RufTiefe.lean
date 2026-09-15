/-
  File:      Grammatik/RufTiefe.lean
  Subject:   **`rufAt` AT TWO DEPTHS** -- the first consumer of the handler
             congruence (`HandlerKongruenz.lean`), and the one that needs no
             side condition at all.

  `rufAt P O passes n` is the model's call at RECURSION DEPTH `n`: at depth
  `0` it answers `logik (abstieg f)`, "the measure did not fall" (K009).
  Depth is the ONE thing in the sequential semantics that is not a property
  of the program -- it is a number a chain author picks -- and every
  statement conditional on "the call ends in no model error"
  (`Schlusssatz.lean`, part 4) carries the `abstieg` residue because of it.

  THE THEOREM. Raising the depth by one changes NOTHING except where the old
  depth ran out:

      rufAt P O passes n g σ ρ = rufAt P O passes (n+1) g σ ρ
        ∨ ∃ h, rufAt P O passes n g σ ρ = .logik (.abstieg h)

  -- and hence: an outcome that is not an `abstieg` is the outcome at EVERY
  larger depth (`rufAt_stabil_ab`). So part 4's condition, once met at one
  depth by a non-`abstieg` outcome, is met at every larger depth BY THE SAME
  OUTCOME: a chain author computes at one depth and is done.

  WHY IT NEEDS THE CONGRUENCE. `rufAt (n+1)`'s body runs against the handler
  `rufAt n`, and `rufAt (n+2)`'s against `rufAt (n+1)`; the two bodies are
  otherwise the same text, the same world, the same arguments. Relating the
  two runs is exactly "two handlers that differ only where the first answers
  an error give runs that differ only where the first is an error" -- with
  the error set `Er` taken as "an `abstieg` mark".

  WHY THE ONE-SIDED CONGRUENCE AND NOT A SYMMETRIC ONE. Where `rufAt n`
  answers `abstieg`, `rufAt (n+1)` may answer `ok`: the deeper call SUCCEEDS
  where the shallower one ran out. A symmetric congruence ("both are errors")
  has no premise here.
-/
import Grammatik.HandlerKongruenz

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The error set of the depth step: an `abstieg` of some function. -/
def AbstiegMarke (m : Fehlermarke D) : Prop := ∃ h : D.Fn, m = .logik (.abstieg h)

/-- **`rufAt` AT DEPTH `n` IS `rufAt` AT DEPTH `n+1`, EXCEPT WHERE IT RAN
    OUT.** No premise: not on the oracle, not on the program, not on the
    user's logic. -/
theorem rufAt_tiefer (P : Programm D) (O : Orakel D) (passes : Nat) :
    ∀ n : Nat, HandlerUnter AbstiegMarke (rufAt P O passes n) (rufAt P O passes (n + 1)) := by
  intro n
  induction n with
  | zero =>
      intro g σ ρ
      exact Or.inr ⟨.logik (.abstieg g), rfl, ⟨g, rfl⟩⟩
  | succ m ih =>
      intro g σ ρ
      rw [rufAt_succ_eq P O passes m, rufAt_succ_eq P O passes (m + 1)]
      exact rufSchritt_kongruent ih P O passes g σ ρ

/-- **An outcome that is not an `abstieg` is the outcome one depth up.** -/
theorem rufAt_stabil (P : Programm D) (O : Orakel D) (passes n : Nat) (f : D.Fn)
    (σ : World D) (ρ : Env D (D.params f))
    (h : ∀ g : D.Fn, rufAt P O passes n f σ ρ ≠ .logik (.abstieg g)) :
    rufAt P O passes (n + 1) f σ ρ = rufAt P O passes n f σ ρ := by
  rcases rufAt_tiefer P O passes n f σ ρ with he | ⟨mk, h1, ⟨hh, rfl⟩⟩
  · exact he.symm
  · exact absurd h1 (h hh)

/-- **... and the outcome at EVERY larger depth.** The condition of part 4,
    once met at one depth by an outcome that is not an `abstieg`, is met at
    every larger depth BY THE SAME OUTCOME. -/
theorem rufAt_stabil_ab (P : Programm D) (O : Orakel D) (passes n : Nat) (f : D.Fn)
    (σ : World D) (ρ : Env D (D.params f))
    (h : ∀ g : D.Fn, rufAt P O passes n f σ ρ ≠ .logik (.abstieg g)) :
    ∀ k : Nat, rufAt P O passes (n + k) f σ ρ = rufAt P O passes n f σ ρ := by
  intro k
  induction k with
  | zero => rfl
  | succ j ih =>
      have hj : ∀ g : D.Fn, rufAt P O passes (n + j) f σ ρ ≠ .logik (.abstieg g) := by
        intro g hg; rw [ih] at hg; exact h g hg
      have := rufAt_stabil P O passes (n + j) f σ ρ hj
      rw [show n + (j + 1) = (n + j) + 1 from rfl, this, ih]

#print axioms Gabbro.Grammatik.rufAt_tiefer
#print axioms Gabbro.Grammatik.rufAt_stabil_ab

end Gabbro.Grammatik
