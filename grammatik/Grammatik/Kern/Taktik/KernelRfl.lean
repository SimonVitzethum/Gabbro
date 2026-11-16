/-
  File:      Grammatik/Kern/Taktik/KernelRfl.lean
  Subject:   `kernel_rfl` and `kernel_change`: reflexivity and restatement with the conversion check left to the kernel.
             The elaborator's own evaluation of a closed front-end run costs gigabytes; the kernel's
             costs megabytes. Nothing is trusted: the kernel checks the term when the theorem is added,
             exactly as with `decide +kernel`, and a false equality is a kernel error.
-/
module

public meta import Lean.Elab.Tactic

public section

open Lean Elab Tactic Meta in
/-- Close `a = b` with `Eq.refl a`; the kernel decides whether `a` and `b` are convertible. -/
elab "kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let type ← instantiateMVars (← goal.getType)
  let some (α, lhs, _) := type.eq? | throwError "kernel_rfl: the goal is not an equality"
  let level ← getLevel α
  goal.assign (mkApp2 (.const ``Eq.refl [level]) α lhs)

open Lean Elab Tactic Meta in
/-- Replace the goal by `t`; the kernel decides whether the two are convertible. -/
elab "kernel_change " t:term : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← Term.elabType t)
  Term.synthesizeSyntheticMVarsNoPostponing
  replaceMainGoal [← goal.replaceTargetDefEq (← instantiateMVars target)]

open Lean Elab Tactic Meta in
/-- Replace the type of the hypothesis `h` by `t`; the kernel decides whether the two are convertible. -/
elab "kernel_change " t:term " at " h:ident : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← Term.elabType t)
  Term.synthesizeSyntheticMVarsNoPostponing
  replaceMainGoal [← goal.replaceLocalDeclDefEq (← getFVarId h) (← instantiateMVars target)]

/-- The tactic closes a computed equality. -/
theorem kernel_rfl_zeuge : (List.range 3).map (· + 1) = [1, 2, 3] := by kernel_rfl

/-- The goal and a hypothesis are restated through a computation. -/
theorem kernel_change_zeuge (h : (List.range 2).length + 1 = 3) : (List.range 3).length = 3 := by
  kernel_change 3 = 3 at h
  kernel_change 3 = 3
  exact h
