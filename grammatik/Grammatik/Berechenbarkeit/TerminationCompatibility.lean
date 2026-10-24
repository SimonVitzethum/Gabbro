/-
  File:      Grammatik/Berechenbarkeit/TerminationCompatibility.lean
  Subject:   Exact compatibility boundary between universality and termination decisions.

  This theorem does NOT assert that a Gabbro universal compiler already exists. Its explicit
  hypothesis is an effective, halting-preserving encoding of partial-recursive codes. Once
  supplied by that compiler, a total computable normal-halting decider is impossible.
  Decidable syntax classification and checking supplied termination proofs remain compatible.
-/
import Mathlib.Computability.Halting
import Mathlib.Computability.Reduce

namespace Gabbro.Grammatik.Berechenbarkeit.TerminationCompatibility

open Nat.Partrec (Code)

/-- An effective halting reduction, at one fixed input. The target may later be a finite
    encoding of actual Gabbro syntax plus input. No simulator correctness is assumed silently. -/
structure HaltingReduction (Target : Type) [Primcodable Target] (halts : Target → Prop) where
  encode : Code → Target
  effective : Computable encode
  correct : ∀ c, (Code.eval c 0).Dom ↔ halts (encode c)

/-- **Universality and a complete computable halting test cannot coexist.** This concerns
    semantic normal halting, not the existing decidable termination classifier. -/
theorem no_complete_halting_test {Target : Type} [Primcodable Target] {halts : Target → Prop}
    (reduction : HaltingReduction Target halts) : ¬ ComputablePred halts := by
  intro test
  apply ComputablePred.halting_problem 0
  exact ComputablePred.computable_of_manyOneReducible
    ⟨reduction.encode, reduction.effective, reduction.correct⟩ test

/-- The reduction premise is inhabited: standard partial-recursive codes provide a real
    reference instance. This is not a Gabbro-compiler witness. -/
def referenceReduction : HaltingReduction Code (fun c => (Code.eval c 0).Dom) :=
  ⟨id, Computable.id, fun _ => Iff.rfl⟩

theorem reference_zeuge : ¬ ComputablePred (fun c : Code => (Code.eval c 0).Dom) :=
  no_complete_halting_test referenceReduction

end Gabbro.Grammatik.Berechenbarkeit.TerminationCompatibility
