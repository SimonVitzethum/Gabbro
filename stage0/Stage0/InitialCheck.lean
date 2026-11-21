module

public import Stage0.Senke.Ausdruck.Old.Pruefer

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Invarianten Invarianten.Pruefer Invarianten.VC
  Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.Frag Invarianten.Modell

variable {D : Deklaration}

/-- The memory-dependent portion of the invariant decision. The lock
    predicate uses exactly the same collector as the full model check. -/
def CheckedInitialInvariants (E : Einheit D) (locks : List D.Lock) : Prop :=
  (∀ item ∈ D.invs, InvHaelt E.P item (E.sp0.welt [])) ∧
    (collect locks _ (checkLockInitial E)).toOption.isSome = true

/-- Decide the invariants on the concrete initial memory after the program
    checker has already verified the writers. -/
def checkInitialInvariants (E : Einheit D) (locks : List D.Lock) :
    Except Frag.Refusal (PLift (CheckedInitialInvariants E locks)) := do
  let translated ← invariantFormula E.P D.invs
  if valid : translated.formula.eval (assignment (E.sp0.welt [])) = true then
    match locked : collect locks _ (checkLockInitial E) with
    | .error cause => .error cause
    | .ok _ => return ⟨(translated.correct _).mp ((qf_eval _ _).mp valid), by rw [locked]; rfl⟩
  else .error (.unsupported "declared invariant is false in the initial memory")

/-- The accepted writer check and the checked initial memory together imply
    the exact invariant Bool of the goal theorem. -/
theorem CheckedInitialInvariants.goal_verdict {E : Einheit D} {functions : List D.Fn} {locks : List D.Lock}
    (initial : CheckedInitialInvariants E locks)
    (accepted : programInvariantsB E.P E.S functions E.lockFormulas {} locks = true) :
    invariantenGeprueftB E functions locks = true := by
  obtain ⟨program, read⟩ := (programInvariantsB_iff E.P E.S functions E.lockFormulas {} locks).mp accepted
  have valid := (qf_eval _ _).mpr ((program.invariants.correct _).mpr initial.1)
  unfold invariantenGeprueftB checkInvariants
  simp only [read, bind, Except.bind, dite_eq_left valid]
  have locked := initial.2
  cases result : collect locks _ (checkLockInitial E) with
  | error cause => simp only [result, Except.toOption, Option.isSome_none, Bool.false_eq_true] at locked
  | ok checks => rfl

end Gabbro.Stage0
