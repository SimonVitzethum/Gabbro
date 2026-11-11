/-
  File:      Grammatik/Kern/Taktik/KernelRfl.lean
  Subject:   `kernel_rfl`: close an equality by reflexivity and leave the conversion check to the kernel.
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

/-- The tactic closes a computed equality. -/
theorem kernel_rfl_zeuge : (List.range 3).map (· + 1) = [1, 2, 3] := by kernel_rfl
